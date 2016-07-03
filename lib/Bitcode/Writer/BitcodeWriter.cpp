//===--- Bitcode/Writer/BitcodeWriter.cpp - Bitcode Writer ----------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Bitcode writer implementation.
//
//===----------------------------------------------------------------------===//

#include "ValueEnumerator.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/Triple.h"
#include "llvm/Bitcode/BitstreamWriter.h"
#include "llvm/Bitcode/LLVMBitCodes.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/UseListOrder.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/Program.h"
#include "llvm/Support/SHA1.h"
#include "llvm/Support/raw_ostream.h"
#include <cctype>
#include <map>
using namespace llvm;

namespace {
/// These are manifest constants used by the bitcode writer. They do not need to
/// be kept in sync with the reader, but need to be consistent within this file.
enum {
  // VALUE_SYMTAB_BLOCK abbrev id's.
  VST_ENTRY_8_ABBREV = bitc::FIRST_APPLICATION_ABBREV,
  VST_ENTRY_7_ABBREV,
  VST_ENTRY_6_ABBREV,
  VST_BBENTRY_6_ABBREV,

  // CONSTANTS_BLOCK abbrev id's.
  CONSTANTS_SETTYPE_ABBREV = bitc::FIRST_APPLICATION_ABBREV,
  CONSTANTS_INTEGER_ABBREV,
  CONSTANTS_CE_CAST_Abbrev,
  CONSTANTS_NULL_Abbrev,

  // FUNCTION_BLOCK abbrev id's.
  FUNCTION_INST_LOAD_ABBREV = bitc::FIRST_APPLICATION_ABBREV,
  FUNCTION_INST_BINOP_ABBREV,
  FUNCTION_INST_BINOP_FLAGS_ABBREV,
  FUNCTION_INST_CAST_ABBREV,
  FUNCTION_INST_RET_VOID_ABBREV,
  FUNCTION_INST_RET_VAL_ABBREV,
  FUNCTION_INST_UNREACHABLE_ABBREV,
  FUNCTION_INST_GEP_ABBREV,
};

/// Abstract class to manage the bitcode writing, subclassed for each bitcode
/// file type. Owns the BitstreamWriter, and includes the main entry point for
/// writing.
class BitcodeWriter {
protected:
  /// Pointer to the buffer allocated by caller for bitcode writing.
  const SmallVectorImpl<char> &Buffer;

  /// The stream created and owned by the BitodeWriter.
  BitstreamWriter Stream;

  /// Saves the offset of the VSTOffset record that must eventually be
  /// backpatched with the offset of the actual VST.
  uint64_t VSTOffsetPlaceholder = 0;

public:
  /// Constructs a BitcodeWriter object, and initializes a BitstreamRecord,
  /// writing to the provided \p Buffer.
  BitcodeWriter(SmallVectorImpl<char> &Buffer)
      : Buffer(Buffer), Stream(Buffer) {}

  virtual ~BitcodeWriter() = default;

  /// Main entry point to write the bitcode file, which writes the bitcode
  /// header and will then invoke the virtual writeBlocks() method.
  void write();

private:
  /// Derived classes must implement this to write the corresponding blocks for
  /// that bitcode file type.
  virtual void writeBlocks() = 0;

protected:
  bool hasVSTOffsetPlaceholder() { return VSTOffsetPlaceholder != 0; }
  void writeValueSymbolTableForwardDecl();
  void writeBitcodeHeader();
};

/// Class to manage the bitcode writing for a module.
class ModuleBitcodeWriter : public BitcodeWriter {
  /// The Module to write to bitcode.
  const Module &M;

  /// Enumerates ids for all values in the module.
  ValueEnumerator VE;

  /// Optional per-module index to write for ThinLTO.
  const ModuleSummaryIndex *Index;

  /// True if a module hash record should be written.
  bool GenerateHash;

  /// The start bit of the module block, for use in generating a module hash
  uint64_t BitcodeStartBit = 0;

public:
  /// Constructs a ModuleBitcodeWriter object for the given Module,
  /// writing to the provided \p Buffer.
  ModuleBitcodeWriter(const Module *M, SmallVectorImpl<char> &Buffer,
                      bool ShouldPreserveUseListOrder,
                      const ModuleSummaryIndex *Index, bool GenerateHash)
      : BitcodeWriter(Buffer), M(*M), VE(*M, ShouldPreserveUseListOrder),
        Index(Index), GenerateHash(GenerateHash) {
    // Save the start bit of the actual bitcode, in case there is space
    // saved at the start for the darwin header above. The reader stream
    // will start at the bitcode, and we need the offset of the VST
    // to line up.
    BitcodeStartBit = Stream.GetCurrentBitNo();
  }

private:
  /// Main entry point for writing a module to bitcode, invoked by
  /// BitcodeWriter::write() after it writes the header.
  void writeBlocks() override;

  /// Create the "IDENTIFICATION_BLOCK_ID" containing a single string with the
  /// current llvm version, and a record for the epoch number.
  void writeIdentificationBlock();

  /// Emit the current module to the bitstream.
  void writeModule();

  uint64_t bitcodeStartBit() { return BitcodeStartBit; }

  void writeStringRecord(unsigned Code, StringRef Str, unsigned AbbrevToUse);
  void writeAttributeGroupTable();
  void writeAttributeTable();
  void writeTypeTable();
  void writeComdats();
  void writeModuleInfo();
  void writeValueAsMetadata(const ValueAsMetadata *MD,
                            SmallVectorImpl<uint64_t> &Record);
  void writeMDTuple(const MDTuple *N, SmallVectorImpl<uint64_t> &Record,
                    unsigned Abbrev);
  unsigned createDILocationAbbrev();
  void writeDILocation(const DILocation *N, SmallVectorImpl<uint64_t> &Record,
                       unsigned &Abbrev);
  unsigned createGenericDINodeAbbrev();
  void writeGenericDINode(const GenericDINode *N,
                          SmallVectorImpl<uint64_t> &Record, unsigned &Abbrev);
  void writeDISubrange(const DISubrange *N, SmallVectorImpl<uint64_t> &Record,
                       unsigned Abbrev);
  void writeDIEnumerator(const DIEnumerator *N,
                         SmallVectorImpl<uint64_t> &Record, unsigned Abbrev);
  void writeDIBasicType(const DIBasicType *N, SmallVectorImpl<uint64_t> &Record,
                        unsigned Abbrev);
  void writeDIDerivedType(const DIDerivedType *N,
                          SmallVectorImpl<uint64_t> &Record, unsigned Abbrev);
  void writeDICompositeType(const DICompositeType *N,
                            SmallVectorImpl<uint64_t> &Record, unsigned Abbrev);
  void writeDISubroutineType(const DISubroutineType *N,
                             SmallVectorImpl<uint64_t> &Record,
                             unsigned Abbrev);
  void writeDIFile(const DIFile *N, SmallVectorImpl<uint64_t> &Record,
                   unsigned Abbrev);
  void writeDICompileUnit(const DICompileUnit *N,
                          SmallVectorImpl<uint64_t> &Record, unsigned Abbrev);
  void writeDISubprogram(const DISubprogram *N,
                         SmallVectorImpl<uint64_t> &Record, unsigned Abbrev);
  void writeDILexicalBlock(const DILexicalBlock *N,
                           SmallVectorImpl<uint64_t> &Record, unsigned Abbrev);
  void writeDILexicalBlockFile(const DILexicalBlockFile *N,
                               SmallVectorImpl<uint64_t> &Record,
                               unsigned Abbrev);
  void writeDINamespace(const DINamespace *N, SmallVectorImpl<uint64_t> &Record,
                        unsigned Abbrev);
  void writeDIMacro(const DIMacro *N, SmallVectorImpl<uint64_t> &Record,
                    unsigned Abbrev);
  void writeDIMacroFile(const DIMacroFile *N, SmallVectorImpl<uint64_t> &Record,
                        unsigned Abbrev);
  void writeDIModule(const DIModule *N, SmallVectorImpl<uint64_t> &Record,
                     unsigned Abbrev);
  void writeDITemplateTypeParameter(const DITemplateTypeParameter *N,
                                    SmallVectorImpl<uint64_t> &Record,
                                    unsigned Abbrev);
  void writeDITemplateValueParameter(const DITemplateValueParameter *N,
                                     SmallVectorImpl<uint64_t> &Record,
                                     unsigned Abbrev);
  void writeDIGlobalVariable(const DIGlobalVariable *N,
                             SmallVectorImpl<uint64_t> &Record,
                             unsigned Abbrev);
  void writeDILocalVariable(const DILocalVariable *N,
                            SmallVectorImpl<uint64_t> &Record, unsigned Abbrev);
  void writeDIExpression(const DIExpression *N,
                         SmallVectorImpl<uint64_t> &Record, unsigned Abbrev);
  void writeDIObjCProperty(const DIObjCProperty *N,
                           SmallVectorImpl<uint64_t> &Record, unsigned Abbrev);
  void writeDIImportedEntity(const DIImportedEntity *N,
                             SmallVectorImpl<uint64_t> &Record,
                             unsigned Abbrev);
  unsigned createNamedMetadataAbbrev();
  void writeNamedMetadata(SmallVectorImpl<uint64_t> &Record);
  unsigned createMetadataStringsAbbrev();
  void writeMetadataStrings(ArrayRef<const Metadata *> Strings,
                            SmallVectorImpl<uint64_t> &Record);
  void writeMetadataRecords(ArrayRef<const Metadata *> MDs,
                            SmallVectorImpl<uint64_t> &Record);
  void writeModuleMetadata();
  void writeFunctionMetadata(const Function &F);
  void writeFunctionMetadataAttachment(const Function &F);
  void writeGlobalVariableMetadataAttachment(const GlobalVariable &GV);
  void pushGlobalMetadataAttachment(SmallVectorImpl<uint64_t> &Record,
                                    const GlobalObject &GO);
  void writeModuleMetadataKinds();
  void writeOperandBundleTags();
  void writeConstants(unsigned FirstVal, unsigned LastVal, bool isGlobal);
  void writeModuleConstants();
  bool pushValueAndType(const Value *V, unsigned InstID,
                        SmallVectorImpl<unsigned> &Vals);
  void writeOperandBundles(ImmutableCallSite CS, unsigned InstID);
  void pushValue(const Value *V, unsigned InstID,
                 SmallVectorImpl<unsigned> &Vals);
  void pushValueSigned(const Value *V, unsigned InstID,
                       SmallVectorImpl<uint64_t> &Vals);
  void writeInstruction(const Instruction &I, unsigned InstID,
                        SmallVectorImpl<unsigned> &Vals);
  void writeValueSymbolTable(
      const ValueSymbolTable &VST, bool IsModuleLevel = false,
      DenseMap<const Function *, uint64_t> *FunctionToBitcodeIndex = nullptr);
  void writeUseList(UseListOrder &&Order);
  void writeUseListBlock(const Function *F);
  void
  writeFunction(const Function &F,
                DenseMap<const Function *, uint64_t> &FunctionToBitcodeIndex);
  void writeBlockInfo();
  void writePerModuleFunctionSummaryRecord(SmallVector<uint64_t, 64> &NameVals,
                                           GlobalValueSummary *Summary,
                                           unsigned ValueID,
                                           unsigned FSCallsAbbrev,
                                           unsigned FSCallsProfileAbbrev,
                                           const Function &F);
  void writeModuleLevelReferences(const GlobalVariable &V,
                                  SmallVector<uint64_t, 64> &NameVals,
                                  unsigned FSModRefsAbbrev);
  void writePerModuleGlobalValueSummary();
  void writeModuleHash(size_t BlockStartPos);
};

/// Class to manage the bitcode writing for a combined index.
class IndexBitcodeWriter : public BitcodeWriter {
  /// The combined index to write to bitcode.
  const ModuleSummaryIndex &Index;

  /// When writing a subset of the index for distributed backends, client
  /// provides a map of modules to the corresponding GUIDs/summaries to write.
  std::map<std::string, GVSummaryMapTy> *ModuleToSummariesForIndex;

  /// Map that holds the correspondence between the GUID used in the combined
  /// index and a value id generated by this class to use in references.
  std::map<GlobalValue::GUID, unsigned> GUIDToValueIdMap;

  /// Tracks the last value id recorded in the GUIDToValueMap.
  unsigned GlobalValueId = 0;

public:
  /// Constructs a IndexBitcodeWriter object for the given combined index,
  /// writing to the provided \p Buffer. When writing a subset of the index
  /// for a distributed backend, provide a \p ModuleToSummariesForIndex map.
  IndexBitcodeWriter(SmallVectorImpl<char> &Buffer,
                     const ModuleSummaryIndex &Index,
                     std::map<std::string, GVSummaryMapTy>
                         *ModuleToSummariesForIndex = nullptr)
      : BitcodeWriter(Buffer), Index(Index),
        ModuleToSummariesForIndex(ModuleToSummariesForIndex) {
    // Assign unique value ids to all summaries to be written, for use
    // in writing out the call graph edges. Save the mapping from GUID
    // to the new global value id to use when writing those edges, which
    // are currently saved in the index in terms of GUID.
    for (const auto &I : *this)
      GUIDToValueIdMap[I.first] = ++GlobalValueId;
  }

  /// The below iterator returns the GUID and associated summary.
  typedef std::pair<GlobalValue::GUID, GlobalValueSummary *> GVInfo;

  /// Iterator over the value GUID and summaries to be written to bitcode,
  /// hides the details of whether they are being pulled from the entire
  /// index or just those in a provided ModuleToSummariesForIndex map.
  class iterator
      : public llvm::iterator_facade_base<iterator, std::forward_iterator_tag,
                                          GVInfo> {
    /// Enables access to parent class.
    const IndexBitcodeWriter &Writer;

    // Iterators used when writing only those summaries in a provided
    // ModuleToSummariesForIndex map:

    /// Points to the last element in outer ModuleToSummariesForIndex map.
    std::map<std::string, GVSummaryMapTy>::iterator ModuleSummariesBack;
    /// Iterator on outer ModuleToSummariesForIndex map.
    std::map<std::string, GVSummaryMapTy>::iterator ModuleSummariesIter;
    /// Iterator on an inner global variable summary map.
    GVSummaryMapTy::iterator ModuleGVSummariesIter;

    // Iterators used when writing all summaries in the index:

    /// Points to the last element in the Index outer GlobalValueMap.
    const_gvsummary_iterator IndexSummariesBack;
    /// Iterator on outer GlobalValueMap.
    const_gvsummary_iterator IndexSummariesIter;
    /// Iterator on an inner GlobalValueSummaryList.
    GlobalValueSummaryList::const_iterator IndexGVSummariesIter;

  public:
    /// Construct iterator from parent \p Writer and indicate if we are
    /// constructing the end iterator.
    iterator(const IndexBitcodeWriter &Writer, bool IsAtEnd) : Writer(Writer) {
      // Set up the appropriate set of iterators given whether we are writing
      // the full index or just a subset.
      // Can't setup the Back or inner iterators if the corresponding map
      // is empty. This will be handled specially in operator== as well.
      if (Writer.ModuleToSummariesForIndex &&
          !Writer.ModuleToSummariesForIndex->empty()) {
        for (ModuleSummariesBack = Writer.ModuleToSummariesForIndex->begin();
             std::next(ModuleSummariesBack) !=
             Writer.ModuleToSummariesForIndex->end();
             ModuleSummariesBack++)
          ;
        ModuleSummariesIter = !IsAtEnd
                                  ? Writer.ModuleToSummariesForIndex->begin()
                                  : ModuleSummariesBack;
        ModuleGVSummariesIter = !IsAtEnd ? ModuleSummariesIter->second.begin()
                                         : ModuleSummariesBack->second.end();
      } else if (!Writer.ModuleToSummariesForIndex &&
                 Writer.Index.begin() != Writer.Index.end()) {
        for (IndexSummariesBack = Writer.Index.begin();
             std::next(IndexSummariesBack) != Writer.Index.end();
             IndexSummariesBack++)
          ;
        IndexSummariesIter =
            !IsAtEnd ? Writer.Index.begin() : IndexSummariesBack;
        IndexGVSummariesIter = !IsAtEnd ? IndexSummariesIter->second.begin()
                                        : IndexSummariesBack->second.end();
      }
    }

    /// Increment the appropriate set of iterators.
    iterator &operator++() {
      // First the inner iterator is incremented, then if it is at the end
      // and there are more outer iterations to go, the inner is reset to
      // the start of the next inner list.
      if (Writer.ModuleToSummariesForIndex) {
        ++ModuleGVSummariesIter;
        if (ModuleGVSummariesIter == ModuleSummariesIter->second.end() &&
            ModuleSummariesIter != ModuleSummariesBack) {
          ++ModuleSummariesIter;
          ModuleGVSummariesIter = ModuleSummariesIter->second.begin();
        }
      } else {
        ++IndexGVSummariesIter;
        if (IndexGVSummariesIter == IndexSummariesIter->second.end() &&
            IndexSummariesIter != IndexSummariesBack) {
          ++IndexSummariesIter;
          IndexGVSummariesIter = IndexSummariesIter->second.begin();
        }
      }
      return *this;
    }

    /// Access the <GUID,GlobalValueSummary*> pair corresponding to the current
    /// outer and inner iterator positions.
    GVInfo operator*() {
      if (Writer.ModuleToSummariesForIndex)
        return std::make_pair(ModuleGVSummariesIter->first,
                              ModuleGVSummariesIter->second);
      return std::make_pair(IndexSummariesIter->first,
                            IndexGVSummariesIter->get());
    }

    /// Checks if the iterators are equal, with special handling for empty
    /// indexes.
    bool operator==(const iterator &RHS) const {
      if (Writer.ModuleToSummariesForIndex) {
        // First ensure that both are writing the same subset.
        if (Writer.ModuleToSummariesForIndex !=
            RHS.Writer.ModuleToSummariesForIndex)
          return false;
        // Already determined above that maps are the same, so if one is
        // empty, they both are.
        if (Writer.ModuleToSummariesForIndex->empty())
          return true;
        // Ensure the ModuleGVSummariesIter are iterating over the same
        // container before checking them below.
        if (ModuleSummariesIter != RHS.ModuleSummariesIter)
          return false;
        return ModuleGVSummariesIter == RHS.ModuleGVSummariesIter;
      }
      // First ensure RHS also writing the full index, and that both are
      // writing the same full index.
      if (RHS.Writer.ModuleToSummariesForIndex ||
          &Writer.Index != &RHS.Writer.Index)
        return false;
      // Already determined above that maps are the same, so if one is
      // empty, they both are.
      if (Writer.Index.begin() == Writer.Index.end())
        return true;
      // Ensure the IndexGVSummariesIter are iterating over the same
      // container before checking them below.
      if (IndexSummariesIter != RHS.IndexSummariesIter)
        return false;
      return IndexGVSummariesIter == RHS.IndexGVSummariesIter;
    }
  };

  /// Obtain the start iterator over the summaries to be written.
  iterator begin() { return iterator(*this, /*IsAtEnd=*/false); }
  /// Obtain the end iterator over the summaries to be written.
  iterator end() { return iterator(*this, /*IsAtEnd=*/true); }

private:
  /// Main entry point for writing a combined index to bitcode, invoked by
  /// BitcodeWriter::write() after it writes the header.
  void writeBlocks() override;

  void writeIndex();
  void writeModStrings();
  void writeCombinedValueSymbolTable();
  void writeCombinedGlobalValueSummary();

  /// Indicates whether the provided \p ModulePath should be written into
  /// the module string table, e.g. if full index written or if it is in
  /// the provided subset.
  bool doIncludeModule(StringRef ModulePath) {
    return !ModuleToSummariesForIndex ||
           ModuleToSummariesForIndex->count(ModulePath);
  }

  bool hasValueId(GlobalValue::GUID ValGUID) {
    const auto &VMI = GUIDToValueIdMap.find(ValGUID);
    return VMI != GUIDToValueIdMap.end();
  }
  unsigned getValueId(GlobalValue::GUID ValGUID) {
    const auto &VMI = GUIDToValueIdMap.find(ValGUID);
    // If this GUID doesn't have an entry, assign one.
    if (VMI == GUIDToValueIdMap.end()) {
      GUIDToValueIdMap[ValGUID] = ++GlobalValueId;
      return GlobalValueId;
    } else {
      return VMI->second;
    }
  }
  std::map<GlobalValue::GUID, unsigned> &valueIds() { return GUIDToValueIdMap; }
};
} // end anonymous namespace

static unsigned getEncodedCastOpcode(unsigned Opcode) {
  switch (Opcode) {
  default: llvm_unreachable("Unknown cast instruction!");
  case Instruction::Trunc   : return bitc::CAST_TRUNC;
  case Instruction::ZExt    : return bitc::CAST_ZEXT;
  case Instruction::SExt    : return bitc::CAST_SEXT;
  case Instruction::FPToUI  : return bitc::CAST_FPTOUI;
  case Instruction::FPToSI  : return bitc::CAST_FPTOSI;
  case Instruction::UIToFP  : return bitc::CAST_UITOFP;
  case Instruction::SIToFP  : return bitc::CAST_SITOFP;
  case Instruction::FPTrunc : return bitc::CAST_FPTRUNC;
  case Instruction::FPExt   : return bitc::CAST_FPEXT;
  case Instruction::PtrToInt: return bitc::CAST_PTRTOINT;
  case Instruction::IntToPtr: return bitc::CAST_INTTOPTR;
  case Instruction::BitCast : return bitc::CAST_BITCAST;
  case Instruction::AddrSpaceCast: return bitc::CAST_ADDRSPACECAST;
  }
}

static unsigned getEncodedBinaryOpcode(unsigned Opcode) {
  switch (Opcode) {
  default: llvm_unreachable("Unknown binary instruction!");
  case Instruction::Add:
  case Instruction::FAdd: return bitc::BINOP_ADD;
  case Instruction::Sub:
  case Instruction::FSub: return bitc::BINOP_SUB;
  case Instruction::Mul:
  case Instruction::FMul: return bitc::BINOP_MUL;
  case Instruction::UDiv: return bitc::BINOP_UDIV;
  case Instruction::FDiv:
  case Instruction::SDiv: return bitc::BINOP_SDIV;
  case Instruction::URem: return bitc::BINOP_UREM;
  case Instruction::FRem:
  case Instruction::SRem: return bitc::BINOP_SREM;
  case Instruction::Shl:  return bitc::BINOP_SHL;
  case Instruction::LShr: return bitc::BINOP_LSHR;
  case Instruction::AShr: return bitc::BINOP_ASHR;
  case Instruction::And:  return bitc::BINOP_AND;
  case Instruction::Or:   return bitc::BINOP_OR;
  case Instruction::Xor:  return bitc::BINOP_XOR;
  }
}

static unsigned getEncodedRMWOperation(AtomicRMWInst::BinOp Op) {
  switch (Op) {
  default: llvm_unreachable("Unknown RMW operation!");
  case AtomicRMWInst::Xchg: return bitc::RMW_XCHG;
  case AtomicRMWInst::Add: return bitc::RMW_ADD;
  case AtomicRMWInst::Sub: return bitc::RMW_SUB;
  case AtomicRMWInst::And: return bitc::RMW_AND;
  case AtomicRMWInst::Nand: return bitc::RMW_NAND;
  case AtomicRMWInst::Or: return bitc::RMW_OR;
  case AtomicRMWInst::Xor: return bitc::RMW_XOR;
  case AtomicRMWInst::Max: return bitc::RMW_MAX;
  case AtomicRMWInst::Min: return bitc::RMW_MIN;
  case AtomicRMWInst::UMax: return bitc::RMW_UMAX;
  case AtomicRMWInst::UMin: return bitc::RMW_UMIN;
  }
}

static unsigned getEncodedOrdering(AtomicOrdering Ordering) {
  switch (Ordering) {
  case AtomicOrdering::NotAtomic: return bitc::ORDERING_NOTATOMIC;
  case AtomicOrdering::Unordered: return bitc::ORDERING_UNORDERED;
  case AtomicOrdering::Monotonic: return bitc::ORDERING_MONOTONIC;
  case AtomicOrdering::Acquire: return bitc::ORDERING_ACQUIRE;
  case AtomicOrdering::Release: return bitc::ORDERING_RELEASE;
  case AtomicOrdering::AcquireRelease: return bitc::ORDERING_ACQREL;
  case AtomicOrdering::SequentiallyConsistent: return bitc::ORDERING_SEQCST;
  }
  llvm_unreachable("Invalid ordering");
}

static unsigned getEncodedSynchScope(SynchronizationScope SynchScope) {
  switch (SynchScope) {
  case SingleThread: return bitc::SYNCHSCOPE_SINGLETHREAD;
  case CrossThread: return bitc::SYNCHSCOPE_CROSSTHREAD;
  }
  llvm_unreachable("Invalid synch scope");
}

void ModuleBitcodeWriter::writeStringRecord(unsigned Code, StringRef Str,
                                            unsigned AbbrevToUse) {
  SmallVector<unsigned, 64> Vals;

  // Code: [strchar x N]
  for (unsigned i = 0, e = Str.size(); i != e; ++i) {
    if (AbbrevToUse && !BitCodeAbbrevOp::isChar6(Str[i]))
      AbbrevToUse = 0;
    Vals.push_back(Str[i]);
  }

  // Emit the finished record.
  Stream.EmitRecord(Code, Vals, AbbrevToUse);
}

static uint64_t getAttrKindEncoding(Attribute::AttrKind Kind) {
  switch (Kind) {
  case Attribute::Alignment:
    return bitc::ATTR_KIND_ALIGNMENT;
  case Attribute::AllocSize:
    return bitc::ATTR_KIND_ALLOC_SIZE;
  case Attribute::AlwaysInline:
    return bitc::ATTR_KIND_ALWAYS_INLINE;
  case Attribute::ArgMemOnly:
    return bitc::ATTR_KIND_ARGMEMONLY;
  case Attribute::Builtin:
    return bitc::ATTR_KIND_BUILTIN;
  case Attribute::ByVal:
    return bitc::ATTR_KIND_BY_VAL;
  case Attribute::Convergent:
    return bitc::ATTR_KIND_CONVERGENT;
  case Attribute::Coroutine:
    return bitc::ATTR_KIND_COROUTINE;
  case Attribute::InAlloca:
    return bitc::ATTR_KIND_IN_ALLOCA;
  case Attribute::Cold:
    return bitc::ATTR_KIND_COLD;
  case Attribute::InaccessibleMemOnly:
    return bitc::ATTR_KIND_INACCESSIBLEMEM_ONLY;
  case Attribute::InaccessibleMemOrArgMemOnly:
    return bitc::ATTR_KIND_INACCESSIBLEMEM_OR_ARGMEMONLY;
  case Attribute::InlineHint:
    return bitc::ATTR_KIND_INLINE_HINT;
  case Attribute::InReg:
    return bitc::ATTR_KIND_IN_REG;
  case Attribute::JumpTable:
    return bitc::ATTR_KIND_JUMP_TABLE;
  case Attribute::MinSize:
    return bitc::ATTR_KIND_MIN_SIZE;
  case Attribute::Naked:
    return bitc::ATTR_KIND_NAKED;
  case Attribute::Nest:
    return bitc::ATTR_KIND_NEST;
  case Attribute::NoAlias:
    return bitc::ATTR_KIND_NO_ALIAS;
  case Attribute::NoBuiltin:
    return bitc::ATTR_KIND_NO_BUILTIN;
  case Attribute::NoCapture:
    return bitc::ATTR_KIND_NO_CAPTURE;
  case Attribute::NoDuplicate:
    return bitc::ATTR_KIND_NO_DUPLICATE;
  case Attribute::NoImplicitFloat:
    return bitc::ATTR_KIND_NO_IMPLICIT_FLOAT;
  case Attribute::NoInline:
    return bitc::ATTR_KIND_NO_INLINE;
  case Attribute::NoRecurse:
    return bitc::ATTR_KIND_NO_RECURSE;
  case Attribute::NonLazyBind:
    return bitc::ATTR_KIND_NON_LAZY_BIND;
  case Attribute::NonNull:
    return bitc::ATTR_KIND_NON_NULL;
  case Attribute::Dereferenceable:
    return bitc::ATTR_KIND_DEREFERENCEABLE;
  case Attribute::DereferenceableOrNull:
    return bitc::ATTR_KIND_DEREFERENCEABLE_OR_NULL;
  case Attribute::NoRedZone:
    return bitc::ATTR_KIND_NO_RED_ZONE;
  case Attribute::NoReturn:
    return bitc::ATTR_KIND_NO_RETURN;
  case Attribute::NoUnwind:
    return bitc::ATTR_KIND_NO_UNWIND;
  case Attribute::OptimizeForSize:
    return bitc::ATTR_KIND_OPTIMIZE_FOR_SIZE;
  case Attribute::OptimizeNone:
    return bitc::ATTR_KIND_OPTIMIZE_NONE;
  case Attribute::ReadNone:
    return bitc::ATTR_KIND_READ_NONE;
  case Attribute::ReadOnly:
    return bitc::ATTR_KIND_READ_ONLY;
  case Attribute::Returned:
    return bitc::ATTR_KIND_RETURNED;
  case Attribute::ReturnsTwice:
    return bitc::ATTR_KIND_RETURNS_TWICE;
  case Attribute::SExt:
    return bitc::ATTR_KIND_S_EXT;
  case Attribute::StackAlignment:
    return bitc::ATTR_KIND_STACK_ALIGNMENT;
  case Attribute::StackProtect:
    return bitc::ATTR_KIND_STACK_PROTECT;
  case Attribute::StackProtectReq:
    return bitc::ATTR_KIND_STACK_PROTECT_REQ;
  case Attribute::StackProtectStrong:
    return bitc::ATTR_KIND_STACK_PROTECT_STRONG;
  case Attribute::SafeStack:
    return bitc::ATTR_KIND_SAFESTACK;
  case Attribute::StructRet:
    return bitc::ATTR_KIND_STRUCT_RET;
  case Attribute::SanitizeAddress:
    return bitc::ATTR_KIND_SANITIZE_ADDRESS;
  case Attribute::SanitizeThread:
    return bitc::ATTR_KIND_SANITIZE_THREAD;
  case Attribute::SanitizeMemory:
    return bitc::ATTR_KIND_SANITIZE_MEMORY;
  case Attribute::SwiftError:
    return bitc::ATTR_KIND_SWIFT_ERROR;
  case Attribute::SwiftSelf:
    return bitc::ATTR_KIND_SWIFT_SELF;
  case Attribute::UWTable:
    return bitc::ATTR_KIND_UW_TABLE;
  case Attribute::ZExt:
    return bitc::ATTR_KIND_Z_EXT;
  case Attribute::EndAttrKinds:
    llvm_unreachable("Can not encode end-attribute kinds marker.");
  case Attribute::None:
    llvm_unreachable("Can not encode none-attribute.");
  }

  llvm_unreachable("Trying to encode unknown attribute");
}

void ModuleBitcodeWriter::writeAttributeGroupTable() {
  const std::vector<AttributeSet> &AttrGrps = VE.getAttributeGroups();
  if (AttrGrps.empty()) return;

  Stream.EnterSubblock(bitc::PARAMATTR_GROUP_BLOCK_ID, 3);

  SmallVector<uint64_t, 64> Record;
  for (unsigned i = 0, e = AttrGrps.size(); i != e; ++i) {
    AttributeSet AS = AttrGrps[i];
    for (unsigned i = 0, e = AS.getNumSlots(); i != e; ++i) {
      AttributeSet A = AS.getSlotAttributes(i);

      Record.push_back(VE.getAttributeGroupID(A));
      Record.push_back(AS.getSlotIndex(i));

      for (AttributeSet::iterator I = AS.begin(0), E = AS.end(0);
           I != E; ++I) {
        Attribute Attr = *I;
        if (Attr.isEnumAttribute()) {
          Record.push_back(0);
          Record.push_back(getAttrKindEncoding(Attr.getKindAsEnum()));
        } else if (Attr.isIntAttribute()) {
          Record.push_back(1);
          Record.push_back(getAttrKindEncoding(Attr.getKindAsEnum()));
          Record.push_back(Attr.getValueAsInt());
        } else {
          StringRef Kind = Attr.getKindAsString();
          StringRef Val = Attr.getValueAsString();

          Record.push_back(Val.empty() ? 3 : 4);
          Record.append(Kind.begin(), Kind.end());
          Record.push_back(0);
          if (!Val.empty()) {
            Record.append(Val.begin(), Val.end());
            Record.push_back(0);
          }
        }
      }

      Stream.EmitRecord(bitc::PARAMATTR_GRP_CODE_ENTRY, Record);
      Record.clear();
    }
  }

  Stream.ExitBlock();
}

void ModuleBitcodeWriter::writeAttributeTable() {
  const std::vector<AttributeSet> &Attrs = VE.getAttributes();
  if (Attrs.empty()) return;

  Stream.EnterSubblock(bitc::PARAMATTR_BLOCK_ID, 3);

  SmallVector<uint64_t, 64> Record;
  for (unsigned i = 0, e = Attrs.size(); i != e; ++i) {
    const AttributeSet &A = Attrs[i];
    for (unsigned i = 0, e = A.getNumSlots(); i != e; ++i)
      Record.push_back(VE.getAttributeGroupID(A.getSlotAttributes(i)));

    Stream.EmitRecord(bitc::PARAMATTR_CODE_ENTRY, Record);
    Record.clear();
  }

  Stream.ExitBlock();
}

/// WriteTypeTable - Write out the type table for a module.
void ModuleBitcodeWriter::writeTypeTable() {
  const ValueEnumerator::TypeList &TypeList = VE.getTypes();

  Stream.EnterSubblock(bitc::TYPE_BLOCK_ID_NEW, 4 /*count from # abbrevs */);
  SmallVector<uint64_t, 64> TypeVals;

  uint64_t NumBits = VE.computeBitsRequiredForTypeIndicies();

  // Abbrev for TYPE_CODE_POINTER.
  BitCodeAbbrev *Abbv = new BitCodeAbbrev();
  Abbv->Add(BitCodeAbbrevOp(bitc::TYPE_CODE_POINTER));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, NumBits));
  Abbv->Add(BitCodeAbbrevOp(0));  // Addrspace = 0
  unsigned PtrAbbrev = Stream.EmitAbbrev(Abbv);

  // Abbrev for TYPE_CODE_FUNCTION.
  Abbv = new BitCodeAbbrev();
  Abbv->Add(BitCodeAbbrevOp(bitc::TYPE_CODE_FUNCTION));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 1));  // isvararg
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, NumBits));

  unsigned FunctionAbbrev = Stream.EmitAbbrev(Abbv);

  // Abbrev for TYPE_CODE_STRUCT_ANON.
  Abbv = new BitCodeAbbrev();
  Abbv->Add(BitCodeAbbrevOp(bitc::TYPE_CODE_STRUCT_ANON));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 1));  // ispacked
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, NumBits));

  unsigned StructAnonAbbrev = Stream.EmitAbbrev(Abbv);

  // Abbrev for TYPE_CODE_STRUCT_NAME.
  Abbv = new BitCodeAbbrev();
  Abbv->Add(BitCodeAbbrevOp(bitc::TYPE_CODE_STRUCT_NAME));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Char6));
  unsigned StructNameAbbrev = Stream.EmitAbbrev(Abbv);

  // Abbrev for TYPE_CODE_STRUCT_NAMED.
  Abbv = new BitCodeAbbrev();
  Abbv->Add(BitCodeAbbrevOp(bitc::TYPE_CODE_STRUCT_NAMED));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 1));  // ispacked
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, NumBits));

  unsigned StructNamedAbbrev = Stream.EmitAbbrev(Abbv);

  // Abbrev for TYPE_CODE_ARRAY.
  Abbv = new BitCodeAbbrev();
  Abbv->Add(BitCodeAbbrevOp(bitc::TYPE_CODE_ARRAY));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));   // size
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, NumBits));

  unsigned ArrayAbbrev = Stream.EmitAbbrev(Abbv);

  // Emit an entry count so the reader can reserve space.
  TypeVals.push_back(TypeList.size());
  Stream.EmitRecord(bitc::TYPE_CODE_NUMENTRY, TypeVals);
  TypeVals.clear();

  // Loop over all of the types, emitting each in turn.
  for (unsigned i = 0, e = TypeList.size(); i != e; ++i) {
    Type *T = TypeList[i];
    int AbbrevToUse = 0;
    unsigned Code = 0;

    switch (T->getTypeID()) {
    case Type::VoidTyID:      Code = bitc::TYPE_CODE_VOID;      break;
    case Type::HalfTyID:      Code = bitc::TYPE_CODE_HALF;      break;
    case Type::FloatTyID:     Code = bitc::TYPE_CODE_FLOAT;     break;
    case Type::DoubleTyID:    Code = bitc::TYPE_CODE_DOUBLE;    break;
    case Type::X86_FP80TyID:  Code = bitc::TYPE_CODE_X86_FP80;  break;
    case Type::FP128TyID:     Code = bitc::TYPE_CODE_FP128;     break;
    case Type::PPC_FP128TyID: Code = bitc::TYPE_CODE_PPC_FP128; break;
    case Type::LabelTyID:     Code = bitc::TYPE_CODE_LABEL;     break;
    case Type::MetadataTyID:  Code = bitc::TYPE_CODE_METADATA;  break;
    case Type::X86_MMXTyID:   Code = bitc::TYPE_CODE_X86_MMX;   break;
    case Type::TokenTyID:     Code = bitc::TYPE_CODE_TOKEN;     break;
    case Type::IntegerTyID:
      // INTEGER: [width]
      Code = bitc::TYPE_CODE_INTEGER;
      TypeVals.push_back(cast<IntegerType>(T)->getBitWidth());
      break;
    case Type::PointerTyID: {
      PointerType *PTy = cast<PointerType>(T);
      // POINTER: [pointee type, address space]
      Code = bitc::TYPE_CODE_POINTER;
      TypeVals.push_back(VE.getTypeID(PTy->getElementType()));
      unsigned AddressSpace = PTy->getAddressSpace();
      TypeVals.push_back(AddressSpace);
      if (AddressSpace == 0) AbbrevToUse = PtrAbbrev;
      break;
    }
    case Type::FunctionTyID: {
      FunctionType *FT = cast<FunctionType>(T);
      // FUNCTION: [isvararg, retty, paramty x N]
      Code = bitc::TYPE_CODE_FUNCTION;
      TypeVals.push_back(FT->isVarArg());
      TypeVals.push_back(VE.getTypeID(FT->getReturnType()));
      for (unsigned i = 0, e = FT->getNumParams(); i != e; ++i)
        TypeVals.push_back(VE.getTypeID(FT->getParamType(i)));
      AbbrevToUse = FunctionAbbrev;
      break;
    }
    case Type::StructTyID: {
      StructType *ST = cast<StructType>(T);
      // STRUCT: [ispacked, eltty x N]
      TypeVals.push_back(ST->isPacked());
      // Output all of the element types.
      for (StructType::element_iterator I = ST->element_begin(),
           E = ST->element_end(); I != E; ++I)
        TypeVals.push_back(VE.getTypeID(*I));

      if (ST->isLiteral()) {
        Code = bitc::TYPE_CODE_STRUCT_ANON;
        AbbrevToUse = StructAnonAbbrev;
      } else {
        if (ST->isOpaque()) {
          Code = bitc::TYPE_CODE_OPAQUE;
        } else {
          Code = bitc::TYPE_CODE_STRUCT_NAMED;
          AbbrevToUse = StructNamedAbbrev;
        }

        // Emit the name if it is present.
        if (!ST->getName().empty())
          writeStringRecord(bitc::TYPE_CODE_STRUCT_NAME, ST->getName(),
                            StructNameAbbrev);
      }
      break;
    }
    case Type::ArrayTyID: {
      ArrayType *AT = cast<ArrayType>(T);
      // ARRAY: [numelts, eltty]
      Code = bitc::TYPE_CODE_ARRAY;
      TypeVals.push_back(AT->getNumElements());
      TypeVals.push_back(VE.getTypeID(AT->getElementType()));
      AbbrevToUse = ArrayAbbrev;
      break;
    }
    case Type::VectorTyID: {
      VectorType *VT = cast<VectorType>(T);
      // VECTOR [numelts, eltty]
      Code = bitc::TYPE_CODE_VECTOR;
      TypeVals.push_back(VT->getNumElements());
      TypeVals.push_back(VE.getTypeID(VT->getElementType()));
      break;
    }
    }

    // Emit the finished record.
    Stream.EmitRecord(Code, TypeVals, AbbrevToUse);
    TypeVals.clear();
  }

  Stream.ExitBlock();
}

static unsigned getEncodedLinkage(const GlobalValue::LinkageTypes Linkage) {
  switch (Linkage) {
  case GlobalValue::ExternalLinkage:
    return 0;
  case GlobalValue::WeakAnyLinkage:
    return 16;
  case GlobalValue::AppendingLinkage:
    return 2;
  case GlobalValue::InternalLinkage:
    return 3;
  case GlobalValue::LinkOnceAnyLinkage:
    return 18;
  case GlobalValue::ExternalWeakLinkage:
    return 7;
  case GlobalValue::CommonLinkage:
    return 8;
  case GlobalValue::PrivateLinkage:
    return 9;
  case GlobalValue::WeakODRLinkage:
    return 17;
  case GlobalValue::LinkOnceODRLinkage:
    return 19;
  case GlobalValue::AvailableExternallyLinkage:
    return 12;
  }
  llvm_unreachable("Invalid linkage");
}

static unsigned getEncodedLinkage(const GlobalValue &GV) {
  return getEncodedLinkage(GV.getLinkage());
}

// Decode the flags for GlobalValue in the summary
static uint64_t getEncodedGVSummaryFlags(GlobalValueSummary::GVFlags Flags) {
  uint64_t RawFlags = 0;

  RawFlags |= Flags.HasSection; // bool

  // Linkage don't need to be remapped at that time for the summary. Any future
  // change to the getEncodedLinkage() function will need to be taken into
  // account here as well.
  RawFlags = (RawFlags << 4) | Flags.Linkage; // 4 bits

  return RawFlags;
}

static unsigned getEncodedVisibility(const GlobalValue &GV) {
  switch (GV.getVisibility()) {
  case GlobalValue::DefaultVisibility:   return 0;
  case GlobalValue::HiddenVisibility:    return 1;
  case GlobalValue::ProtectedVisibility: return 2;
  }
  llvm_unreachable("Invalid visibility");
}

static unsigned getEncodedDLLStorageClass(const GlobalValue &GV) {
  switch (GV.getDLLStorageClass()) {
  case GlobalValue::DefaultStorageClass:   return 0;
  case GlobalValue::DLLImportStorageClass: return 1;
  case GlobalValue::DLLExportStorageClass: return 2;
  }
  llvm_unreachable("Invalid DLL storage class");
}

static unsigned getEncodedThreadLocalMode(const GlobalValue &GV) {
  switch (GV.getThreadLocalMode()) {
    case GlobalVariable::NotThreadLocal:         return 0;
    case GlobalVariable::GeneralDynamicTLSModel: return 1;
    case GlobalVariable::LocalDynamicTLSModel:   return 2;
    case GlobalVariable::InitialExecTLSModel:    return 3;
    case GlobalVariable::LocalExecTLSModel:      return 4;
  }
  llvm_unreachable("Invalid TLS model");
}

static unsigned getEncodedComdatSelectionKind(const Comdat &C) {
  switch (C.getSelectionKind()) {
  case Comdat::Any:
    return bitc::COMDAT_SELECTION_KIND_ANY;
  case Comdat::ExactMatch:
    return bitc::COMDAT_SELECTION_KIND_EXACT_MATCH;
  case Comdat::Largest:
    return bitc::COMDAT_SELECTION_KIND_LARGEST;
  case Comdat::NoDuplicates:
    return bitc::COMDAT_SELECTION_KIND_NO_DUPLICATES;
  case Comdat::SameSize:
    return bitc::COMDAT_SELECTION_KIND_SAME_SIZE;
  }
  llvm_unreachable("Invalid selection kind");
}

static unsigned getEncodedUnnamedAddr(const GlobalValue &GV) {
  switch (GV.getUnnamedAddr()) {
  case GlobalValue::UnnamedAddr::None:   return 0;
  case GlobalValue::UnnamedAddr::Local:  return 2;
  case GlobalValue::UnnamedAddr::Global: return 1;
  }
  llvm_unreachable("Invalid unnamed_addr");
}

void ModuleBitcodeWriter::writeComdats() {
  SmallVector<unsigned, 64> Vals;
  for (const Comdat *C : VE.getComdats()) {
    // COMDAT: [selection_kind, name]
    Vals.push_back(getEncodedComdatSelectionKind(*C));
    size_t Size = C->getName().size();
    assert(isUInt<32>(Size));
    Vals.push_back(Size);
    for (char Chr : C->getName())
      Vals.push_back((unsigned char)Chr);
    Stream.EmitRecord(bitc::MODULE_CODE_COMDAT, Vals, /*AbbrevToUse=*/0);
    Vals.clear();
  }
}

/// Write a record that will eventually hold the word offset of the
/// module-level VST. For now the offset is 0, which will be backpatched
/// after the real VST is written. Saves the bit offset to backpatch.
void BitcodeWriter::writeValueSymbolTableForwardDecl() {
  // Write a placeholder value in for the offset of the real VST,
  // which is written after the function blocks so that it can include
  // the offset of each function. The placeholder offset will be
  // updated when the real VST is written.
  BitCodeAbbrev *Abbv = new BitCodeAbbrev();
  Abbv->Add(BitCodeAbbrevOp(bitc::MODULE_CODE_VSTOFFSET));
  // Blocks are 32-bit aligned, so we can use a 32-bit word offset to
  // hold the real VST offset. Must use fixed instead of VBR as we don't
  // know how many VBR chunks to reserve ahead of time.
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 32));
  unsigned VSTOffsetAbbrev = Stream.EmitAbbrev(Abbv);

  // Emit the placeholder
  uint64_t Vals[] = {bitc::MODULE_CODE_VSTOFFSET, 0};
  Stream.EmitRecordWithAbbrev(VSTOffsetAbbrev, Vals);

  // Compute and save the bit offset to the placeholder, which will be
  // patched when the real VST is written. We can simply subtract the 32-bit
  // fixed size from the current bit number to get the location to backpatch.
  VSTOffsetPlaceholder = Stream.GetCurrentBitNo() - 32;
}

enum StringEncoding { SE_Char6, SE_Fixed7, SE_Fixed8 };

/// Determine the encoding to use for the given string name and length.
static StringEncoding getStringEncoding(const char *Str, unsigned StrLen) {
  bool isChar6 = true;
  for (const char *C = Str, *E = C + StrLen; C != E; ++C) {
    if (isChar6)
      isChar6 = BitCodeAbbrevOp::isChar6(*C);
    if ((unsigned char)*C & 128)
      // don't bother scanning the rest.
      return SE_Fixed8;
  }
  if (isChar6)
    return SE_Char6;
  else
    return SE_Fixed7;
}

/// Emit top-level description of module, including target triple, inline asm,
/// descriptors for global variables, and function prototype info.
/// Returns the bit offset to backpatch with the location of the real VST.
void ModuleBitcodeWriter::writeModuleInfo() {
  // Emit various pieces of data attached to a module.
  if (!M.getTargetTriple().empty())
    writeStringRecord(bitc::MODULE_CODE_TRIPLE, M.getTargetTriple(),
                      0 /*TODO*/);
  const std::string &DL = M.getDataLayoutStr();
  if (!DL.empty())
    writeStringRecord(bitc::MODULE_CODE_DATALAYOUT, DL, 0 /*TODO*/);
  if (!M.getModuleInlineAsm().empty())
    writeStringRecord(bitc::MODULE_CODE_ASM, M.getModuleInlineAsm(),
                      0 /*TODO*/);

  // Emit information about sections and GC, computing how many there are. Also
  // compute the maximum alignment value.
  std::map<std::string, unsigned> SectionMap;
  std::map<std::string, unsigned> GCMap;
  unsigned MaxAlignment = 0;
  unsigned MaxGlobalType = 0;
  for (const GlobalValue &GV : M.globals()) {
    MaxAlignment = std::max(MaxAlignment, GV.getAlignment());
    MaxGlobalType = std::max(MaxGlobalType, VE.getTypeID(GV.getValueType()));
    if (GV.hasSection()) {
      // Give section names unique ID's.
      unsigned &Entry = SectionMap[GV.getSection()];
      if (!Entry) {
        writeStringRecord(bitc::MODULE_CODE_SECTIONNAME, GV.getSection(),
                          0 /*TODO*/);
        Entry = SectionMap.size();
      }
    }
  }
  for (const Function &F : M) {
    MaxAlignment = std::max(MaxAlignment, F.getAlignment());
    if (F.hasSection()) {
      // Give section names unique ID's.
      unsigned &Entry = SectionMap[F.getSection()];
      if (!Entry) {
        writeStringRecord(bitc::MODULE_CODE_SECTIONNAME, F.getSection(),
                          0 /*TODO*/);
        Entry = SectionMap.size();
      }
    }
    if (F.hasGC()) {
      // Same for GC names.
      unsigned &Entry = GCMap[F.getGC()];
      if (!Entry) {
        writeStringRecord(bitc::MODULE_CODE_GCNAME, F.getGC(), 0 /*TODO*/);
        Entry = GCMap.size();
      }
    }
  }

  // Emit abbrev for globals, now that we know # sections and max alignment.
  unsigned SimpleGVarAbbrev = 0;
  if (!M.global_empty()) {
    // Add an abbrev for common globals with no visibility or thread localness.
    BitCodeAbbrev *Abbv = new BitCodeAbbrev();
    Abbv->Add(BitCodeAbbrevOp(bitc::MODULE_CODE_GLOBALVAR));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed,
                              Log2_32_Ceil(MaxGlobalType+1)));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 6));   // AddrSpace << 2
                                                           //| explicitType << 1
                                                           //| constant
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 6));   // Initializer.
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 5)); // Linkage.
    if (MaxAlignment == 0)                                 // Alignment.
      Abbv->Add(BitCodeAbbrevOp(0));
    else {
      unsigned MaxEncAlignment = Log2_32(MaxAlignment)+1;
      Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed,
                               Log2_32_Ceil(MaxEncAlignment+1)));
    }
    if (SectionMap.empty())                                    // Section.
      Abbv->Add(BitCodeAbbrevOp(0));
    else
      Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed,
                               Log2_32_Ceil(SectionMap.size()+1)));
    // Don't bother emitting vis + thread local.
    SimpleGVarAbbrev = Stream.EmitAbbrev(Abbv);
  }

  // Emit the global variable information.
  SmallVector<unsigned, 64> Vals;
  for (const GlobalVariable &GV : M.globals()) {
    unsigned AbbrevToUse = 0;

    // GLOBALVAR: [type, isconst, initid,
    //             linkage, alignment, section, visibility, threadlocal,
    //             unnamed_addr, externally_initialized, dllstorageclass,
    //             comdat]
    Vals.push_back(VE.getTypeID(GV.getValueType()));
    Vals.push_back(GV.getType()->getAddressSpace() << 2 | 2 | GV.isConstant());
    Vals.push_back(GV.isDeclaration() ? 0 :
                   (VE.getValueID(GV.getInitializer()) + 1));
    Vals.push_back(getEncodedLinkage(GV));
    Vals.push_back(Log2_32(GV.getAlignment())+1);
    Vals.push_back(GV.hasSection() ? SectionMap[GV.getSection()] : 0);
    if (GV.isThreadLocal() ||
        GV.getVisibility() != GlobalValue::DefaultVisibility ||
        GV.getUnnamedAddr() != GlobalValue::UnnamedAddr::None ||
        GV.isExternallyInitialized() ||
        GV.getDLLStorageClass() != GlobalValue::DefaultStorageClass ||
        GV.hasComdat()) {
      Vals.push_back(getEncodedVisibility(GV));
      Vals.push_back(getEncodedThreadLocalMode(GV));
      Vals.push_back(getEncodedUnnamedAddr(GV));
      Vals.push_back(GV.isExternallyInitialized());
      Vals.push_back(getEncodedDLLStorageClass(GV));
      Vals.push_back(GV.hasComdat() ? VE.getComdatID(GV.getComdat()) : 0);
    } else {
      AbbrevToUse = SimpleGVarAbbrev;
    }

    Stream.EmitRecord(bitc::MODULE_CODE_GLOBALVAR, Vals, AbbrevToUse);
    Vals.clear();
  }

  // Emit the function proto information.
  for (const Function &F : M) {
    // FUNCTION:  [type, callingconv, isproto, linkage, paramattrs, alignment,
    //             section, visibility, gc, unnamed_addr, prologuedata,
    //             dllstorageclass, comdat, prefixdata, personalityfn]
    Vals.push_back(VE.getTypeID(F.getFunctionType()));
    Vals.push_back(F.getCallingConv());
    Vals.push_back(F.isDeclaration());
    Vals.push_back(getEncodedLinkage(F));
    Vals.push_back(VE.getAttributeID(F.getAttributes()));
    Vals.push_back(Log2_32(F.getAlignment())+1);
    Vals.push_back(F.hasSection() ? SectionMap[F.getSection()] : 0);
    Vals.push_back(getEncodedVisibility(F));
    Vals.push_back(F.hasGC() ? GCMap[F.getGC()] : 0);
    Vals.push_back(getEncodedUnnamedAddr(F));
    Vals.push_back(F.hasPrologueData() ? (VE.getValueID(F.getPrologueData()) + 1)
                                       : 0);
    Vals.push_back(getEncodedDLLStorageClass(F));
    Vals.push_back(F.hasComdat() ? VE.getComdatID(F.getComdat()) : 0);
    Vals.push_back(F.hasPrefixData() ? (VE.getValueID(F.getPrefixData()) + 1)
                                     : 0);
    Vals.push_back(
        F.hasPersonalityFn() ? (VE.getValueID(F.getPersonalityFn()) + 1) : 0);

    unsigned AbbrevToUse = 0;
    Stream.EmitRecord(bitc::MODULE_CODE_FUNCTION, Vals, AbbrevToUse);
    Vals.clear();
  }

  // Emit the alias information.
  for (const GlobalAlias &A : M.aliases()) {
    // ALIAS: [alias type, aliasee val#, linkage, visibility, dllstorageclass,
    //         threadlocal, unnamed_addr]
    Vals.push_back(VE.getTypeID(A.getValueType()));
    Vals.push_back(A.getType()->getAddressSpace());
    Vals.push_back(VE.getValueID(A.getAliasee()));
    Vals.push_back(getEncodedLinkage(A));
    Vals.push_back(getEncodedVisibility(A));
    Vals.push_back(getEncodedDLLStorageClass(A));
    Vals.push_back(getEncodedThreadLocalMode(A));
    Vals.push_back(getEncodedUnnamedAddr(A));
    unsigned AbbrevToUse = 0;
    Stream.EmitRecord(bitc::MODULE_CODE_ALIAS, Vals, AbbrevToUse);
    Vals.clear();
  }

  // Emit the ifunc information.
  for (const GlobalIFunc &I : M.ifuncs()) {
    // IFUNC: [ifunc type, address space, resolver val#, linkage, visibility]
    Vals.push_back(VE.getTypeID(I.getValueType()));
    Vals.push_back(I.getType()->getAddressSpace());
    Vals.push_back(VE.getValueID(I.getResolver()));
    Vals.push_back(getEncodedLinkage(I));
    Vals.push_back(getEncodedVisibility(I));
    Stream.EmitRecord(bitc::MODULE_CODE_IFUNC, Vals);
    Vals.clear();
  }

  // Emit the module's source file name.
  {
    StringEncoding Bits = getStringEncoding(M.getSourceFileName().data(),
                                            M.getSourceFileName().size());
    BitCodeAbbrevOp AbbrevOpToUse = BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 8);
    if (Bits == SE_Char6)
      AbbrevOpToUse = BitCodeAbbrevOp(BitCodeAbbrevOp::Char6);
    else if (Bits == SE_Fixed7)
      AbbrevOpToUse = BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 7);

    // MODULE_CODE_SOURCE_FILENAME: [namechar x N]
    BitCodeAbbrev *Abbv = new BitCodeAbbrev();
    Abbv->Add(BitCodeAbbrevOp(bitc::MODULE_CODE_SOURCE_FILENAME));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));
    Abbv->Add(AbbrevOpToUse);
    unsigned FilenameAbbrev = Stream.EmitAbbrev(Abbv);

    for (const auto P : M.getSourceFileName())
      Vals.push_back((unsigned char)P);

    // Emit the finished record.
    Stream.EmitRecord(bitc::MODULE_CODE_SOURCE_FILENAME, Vals, FilenameAbbrev);
    Vals.clear();
  }

  // If we have a VST, write the VSTOFFSET record placeholder.
  if (M.getValueSymbolTable().empty())
    return;
  writeValueSymbolTableForwardDecl();
}

static uint64_t getOptimizationFlags(const Value *V) {
  uint64_t Flags = 0;

  if (const auto *OBO = dyn_cast<OverflowingBinaryOperator>(V)) {
    if (OBO->hasNoSignedWrap())
      Flags |= 1 << bitc::OBO_NO_SIGNED_WRAP;
    if (OBO->hasNoUnsignedWrap())
      Flags |= 1 << bitc::OBO_NO_UNSIGNED_WRAP;
  } else if (const auto *PEO = dyn_cast<PossiblyExactOperator>(V)) {
    if (PEO->isExact())
      Flags |= 1 << bitc::PEO_EXACT;
  } else if (const auto *FPMO = dyn_cast<FPMathOperator>(V)) {
    if (FPMO->hasUnsafeAlgebra())
      Flags |= FastMathFlags::UnsafeAlgebra;
    if (FPMO->hasNoNaNs())
      Flags |= FastMathFlags::NoNaNs;
    if (FPMO->hasNoInfs())
      Flags |= FastMathFlags::NoInfs;
    if (FPMO->hasNoSignedZeros())
      Flags |= FastMathFlags::NoSignedZeros;
    if (FPMO->hasAllowReciprocal())
      Flags |= FastMathFlags::AllowReciprocal;
  }

  return Flags;
}

void ModuleBitcodeWriter::writeValueAsMetadata(
    const ValueAsMetadata *MD, SmallVectorImpl<uint64_t> &Record) {
  // Mimic an MDNode with a value as one operand.
  Value *V = MD->getValue();
  Record.push_back(VE.getTypeID(V->getType()));
  Record.push_back(VE.getValueID(V));
  Stream.EmitRecord(bitc::METADATA_VALUE, Record, 0);
  Record.clear();
}

void ModuleBitcodeWriter::writeMDTuple(const MDTuple *N,
                                       SmallVectorImpl<uint64_t> &Record,
                                       unsigned Abbrev) {
  for (unsigned i = 0, e = N->getNumOperands(); i != e; ++i) {
    Metadata *MD = N->getOperand(i);
    assert(!(MD && isa<LocalAsMetadata>(MD)) &&
           "Unexpected function-local metadata");
    Record.push_back(VE.getMetadataOrNullID(MD));
  }
  Stream.EmitRecord(N->isDistinct() ? bitc::METADATA_DISTINCT_NODE
                                    : bitc::METADATA_NODE,
                    Record, Abbrev);
  Record.clear();
}

unsigned ModuleBitcodeWriter::createDILocationAbbrev() {
  // Assume the column is usually under 128, and always output the inlined-at
  // location (it's never more expensive than building an array size 1).
  BitCodeAbbrev *Abbv = new BitCodeAbbrev();
  Abbv->Add(BitCodeAbbrevOp(bitc::METADATA_LOCATION));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 1));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 6));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 6));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 6));
  return Stream.EmitAbbrev(Abbv);
}

void ModuleBitcodeWriter::writeDILocation(const DILocation *N,
                                          SmallVectorImpl<uint64_t> &Record,
                                          unsigned &Abbrev) {
  if (!Abbrev)
    Abbrev = createDILocationAbbrev();

  Record.push_back(N->isDistinct());
  Record.push_back(N->getLine());
  Record.push_back(N->getColumn());
  Record.push_back(VE.getMetadataID(N->getScope()));
  Record.push_back(VE.getMetadataOrNullID(N->getInlinedAt()));

  Stream.EmitRecord(bitc::METADATA_LOCATION, Record, Abbrev);
  Record.clear();
}

unsigned ModuleBitcodeWriter::createGenericDINodeAbbrev() {
  // Assume the column is usually under 128, and always output the inlined-at
  // location (it's never more expensive than building an array size 1).
  BitCodeAbbrev *Abbv = new BitCodeAbbrev();
  Abbv->Add(BitCodeAbbrevOp(bitc::METADATA_GENERIC_DEBUG));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 1));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 6));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 1));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 6));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 6));
  return Stream.EmitAbbrev(Abbv);
}

void ModuleBitcodeWriter::writeGenericDINode(const GenericDINode *N,
                                             SmallVectorImpl<uint64_t> &Record,
                                             unsigned &Abbrev) {
  if (!Abbrev)
    Abbrev = createGenericDINodeAbbrev();

  Record.push_back(N->isDistinct());
  Record.push_back(N->getTag());
  Record.push_back(0); // Per-tag version field; unused for now.

  for (auto &I : N->operands())
    Record.push_back(VE.getMetadataOrNullID(I));

  Stream.EmitRecord(bitc::METADATA_GENERIC_DEBUG, Record, Abbrev);
  Record.clear();
}

static uint64_t rotateSign(int64_t I) {
  uint64_t U = I;
  return I < 0 ? ~(U << 1) : U << 1;
}

void ModuleBitcodeWriter::writeDISubrange(const DISubrange *N,
                                          SmallVectorImpl<uint64_t> &Record,
                                          unsigned Abbrev) {
  Record.push_back(N->isDistinct());
  Record.push_back(N->getCount());
  Record.push_back(rotateSign(N->getLowerBound()));

  Stream.EmitRecord(bitc::METADATA_SUBRANGE, Record, Abbrev);
  Record.clear();
}

void ModuleBitcodeWriter::writeDIEnumerator(const DIEnumerator *N,
                                            SmallVectorImpl<uint64_t> &Record,
                                            unsigned Abbrev) {
  Record.push_back(N->isDistinct());
  Record.push_back(rotateSign(N->getValue()));
  Record.push_back(VE.getMetadataOrNullID(N->getRawName()));

  Stream.EmitRecord(bitc::METADATA_ENUMERATOR, Record, Abbrev);
  Record.clear();
}

void ModuleBitcodeWriter::writeDIBasicType(const DIBasicType *N,
                                           SmallVectorImpl<uint64_t> &Record,
                                           unsigned Abbrev) {
  Record.push_back(N->isDistinct());
  Record.push_back(N->getTag());
  Record.push_back(VE.getMetadataOrNullID(N->getRawName()));
  Record.push_back(N->getSizeInBits());
  Record.push_back(N->getAlignInBits());
  Record.push_back(N->getEncoding());

  Stream.EmitRecord(bitc::METADATA_BASIC_TYPE, Record, Abbrev);
  Record.clear();
}

void ModuleBitcodeWriter::writeDIDerivedType(const DIDerivedType *N,
                                             SmallVectorImpl<uint64_t> &Record,
                                             unsigned Abbrev) {
  Record.push_back(N->isDistinct());
  Record.push_back(N->getTag());
  Record.push_back(VE.getMetadataOrNullID(N->getRawName()));
  Record.push_back(VE.getMetadataOrNullID(N->getFile()));
  Record.push_back(N->getLine());
  Record.push_back(VE.getMetadataOrNullID(N->getScope()));
  Record.push_back(VE.getMetadataOrNullID(N->getBaseType()));
  Record.push_back(N->getSizeInBits());
  Record.push_back(N->getAlignInBits());
  Record.push_back(N->getOffsetInBits());
  Record.push_back(N->getFlags());
  Record.push_back(VE.getMetadataOrNullID(N->getExtraData()));

  Stream.EmitRecord(bitc::METADATA_DERIVED_TYPE, Record, Abbrev);
  Record.clear();
}

void ModuleBitcodeWriter::writeDICompositeType(
    const DICompositeType *N, SmallVectorImpl<uint64_t> &Record,
    unsigned Abbrev) {
  const unsigned IsNotUsedInOldTypeRef = 0x2;
  Record.push_back(IsNotUsedInOldTypeRef | (unsigned)N->isDistinct());
  Record.push_back(N->getTag());
  Record.push_back(VE.getMetadataOrNullID(N->getRawName()));
  Record.push_back(VE.getMetadataOrNullID(N->getFile()));
  Record.push_back(N->getLine());
  Record.push_back(VE.getMetadataOrNullID(N->getScope()));
  Record.push_back(VE.getMetadataOrNullID(N->getBaseType()));
  Record.push_back(N->getSizeInBits());
  Record.push_back(N->getAlignInBits());
  Record.push_back(N->getOffsetInBits());
  Record.push_back(N->getFlags());
  Record.push_back(VE.getMetadataOrNullID(N->getElements().get()));
  Record.push_back(N->getRuntimeLang());
  Record.push_back(VE.getMetadataOrNullID(N->getVTableHolder()));
  Record.push_back(VE.getMetadataOrNullID(N->getTemplateParams().get()));
  Record.push_back(VE.getMetadataOrNullID(N->getRawIdentifier()));

  Stream.EmitRecord(bitc::METADATA_COMPOSITE_TYPE, Record, Abbrev);
  Record.clear();
}

void ModuleBitcodeWriter::writeDISubroutineType(
    const DISubroutineType *N, SmallVectorImpl<uint64_t> &Record,
    unsigned Abbrev) {
  const unsigned HasNoOldTypeRefs = 0x2;
  Record.push_back(HasNoOldTypeRefs | (unsigned)N->isDistinct());
  Record.push_back(N->getFlags());
  Record.push_back(VE.getMetadataOrNullID(N->getTypeArray().get()));
  Record.push_back(N->getCC());

  Stream.EmitRecord(bitc::METADATA_SUBROUTINE_TYPE, Record, Abbrev);
  Record.clear();
}

void ModuleBitcodeWriter::writeDIFile(const DIFile *N,
                                      SmallVectorImpl<uint64_t> &Record,
                                      unsigned Abbrev) {
  Record.push_back(N->isDistinct());
  Record.push_back(VE.getMetadataOrNullID(N->getRawFilename()));
  Record.push_back(VE.getMetadataOrNullID(N->getRawDirectory()));

  Stream.EmitRecord(bitc::METADATA_FILE, Record, Abbrev);
  Record.clear();
}

void ModuleBitcodeWriter::writeDICompileUnit(const DICompileUnit *N,
                                             SmallVectorImpl<uint64_t> &Record,
                                             unsigned Abbrev) {
  assert(N->isDistinct() && "Expected distinct compile units");
  Record.push_back(/* IsDistinct */ true);
  Record.push_back(N->getSourceLanguage());
  Record.push_back(VE.getMetadataOrNullID(N->getFile()));
  Record.push_back(VE.getMetadataOrNullID(N->getRawProducer()));
  Record.push_back(N->isOptimized());
  Record.push_back(VE.getMetadataOrNullID(N->getRawFlags()));
  Record.push_back(N->getRuntimeVersion());
  Record.push_back(VE.getMetadataOrNullID(N->getRawSplitDebugFilename()));
  Record.push_back(N->getEmissionKind());
  Record.push_back(VE.getMetadataOrNullID(N->getEnumTypes().get()));
  Record.push_back(VE.getMetadataOrNullID(N->getRetainedTypes().get()));
  Record.push_back(/* subprograms */ 0);
  Record.push_back(VE.getMetadataOrNullID(N->getGlobalVariables().get()));
  Record.push_back(VE.getMetadataOrNullID(N->getImportedEntities().get()));
  Record.push_back(N->getDWOId());
  Record.push_back(VE.getMetadataOrNullID(N->getMacros().get()));

  Stream.EmitRecord(bitc::METADATA_COMPILE_UNIT, Record, Abbrev);
  Record.clear();
}

void ModuleBitcodeWriter::writeDISubprogram(const DISubprogram *N,
                                            SmallVectorImpl<uint64_t> &Record,
                                            unsigned Abbrev) {
  uint64_t HasUnitFlag = 1 << 1;
  Record.push_back(N->isDistinct() | HasUnitFlag);
  Record.push_back(VE.getMetadataOrNullID(N->getScope()));
  Record.push_back(VE.getMetadataOrNullID(N->getRawName()));
  Record.push_back(VE.getMetadataOrNullID(N->getRawLinkageName()));
  Record.push_back(VE.getMetadataOrNullID(N->getFile()));
  Record.push_back(N->getLine());
  Record.push_back(VE.getMetadataOrNullID(N->getType()));
  Record.push_back(N->isLocalToUnit());
  Record.push_back(N->isDefinition());
  Record.push_back(N->getScopeLine());
  Record.push_back(VE.getMetadataOrNullID(N->getContainingType()));
  Record.push_back(N->getVirtuality());
  Record.push_back(N->getVirtualIndex());
  Record.push_back(N->getFlags());
  Record.push_back(N->isOptimized());
  Record.push_back(VE.getMetadataOrNullID(N->getRawUnit()));
  Record.push_back(VE.getMetadataOrNullID(N->getTemplateParams().get()));
  Record.push_back(VE.getMetadataOrNullID(N->getDeclaration()));
  Record.push_back(VE.getMetadataOrNullID(N->getVariables().get()));
  Record.push_back(N->getThisAdjustment());

  Stream.EmitRecord(bitc::METADATA_SUBPROGRAM, Record, Abbrev);
  Record.clear();
}

void ModuleBitcodeWriter::writeDILexicalBlock(const DILexicalBlock *N,
                                              SmallVectorImpl<uint64_t> &Record,
                                              unsigned Abbrev) {
  Record.push_back(N->isDistinct());
  Record.push_back(VE.getMetadataOrNullID(N->getScope()));
  Record.push_back(VE.getMetadataOrNullID(N->getFile()));
  Record.push_back(N->getLine());
  Record.push_back(N->getColumn());

  Stream.EmitRecord(bitc::METADATA_LEXICAL_BLOCK, Record, Abbrev);
  Record.clear();
}

void ModuleBitcodeWriter::writeDILexicalBlockFile(
    const DILexicalBlockFile *N, SmallVectorImpl<uint64_t> &Record,
    unsigned Abbrev) {
  Record.push_back(N->isDistinct());
  Record.push_back(VE.getMetadataOrNullID(N->getScope()));
  Record.push_back(VE.getMetadataOrNullID(N->getFile()));
  Record.push_back(N->getDiscriminator());

  Stream.EmitRecord(bitc::METADATA_LEXICAL_BLOCK_FILE, Record, Abbrev);
  Record.clear();
}

void ModuleBitcodeWriter::writeDINamespace(const DINamespace *N,
                                           SmallVectorImpl<uint64_t> &Record,
                                           unsigned Abbrev) {
  Record.push_back(N->isDistinct());
  Record.push_back(VE.getMetadataOrNullID(N->getScope()));
  Record.push_back(VE.getMetadataOrNullID(N->getFile()));
  Record.push_back(VE.getMetadataOrNullID(N->getRawName()));
  Record.push_back(N->getLine());

  Stream.EmitRecord(bitc::METADATA_NAMESPACE, Record, Abbrev);
  Record.clear();
}

void ModuleBitcodeWriter::writeDIMacro(const DIMacro *N,
                                       SmallVectorImpl<uint64_t> &Record,
                                       unsigned Abbrev) {
  Record.push_back(N->isDistinct());
  Record.push_back(N->getMacinfoType());
  Record.push_back(N->getLine());
  Record.push_back(VE.getMetadataOrNullID(N->getRawName()));
  Record.push_back(VE.getMetadataOrNullID(N->getRawValue()));

  Stream.EmitRecord(bitc::METADATA_MACRO, Record, Abbrev);
  Record.clear();
}

void ModuleBitcodeWriter::writeDIMacroFile(const DIMacroFile *N,
                                           SmallVectorImpl<uint64_t> &Record,
                                           unsigned Abbrev) {
  Record.push_back(N->isDistinct());
  Record.push_back(N->getMacinfoType());
  Record.push_back(N->getLine());
  Record.push_back(VE.getMetadataOrNullID(N->getFile()));
  Record.push_back(VE.getMetadataOrNullID(N->getElements().get()));

  Stream.EmitRecord(bitc::METADATA_MACRO_FILE, Record, Abbrev);
  Record.clear();
}

void ModuleBitcodeWriter::writeDIModule(const DIModule *N,
                                        SmallVectorImpl<uint64_t> &Record,
                                        unsigned Abbrev) {
  Record.push_back(N->isDistinct());
  for (auto &I : N->operands())
    Record.push_back(VE.getMetadataOrNullID(I));

  Stream.EmitRecord(bitc::METADATA_MODULE, Record, Abbrev);
  Record.clear();
}

void ModuleBitcodeWriter::writeDITemplateTypeParameter(
    const DITemplateTypeParameter *N, SmallVectorImpl<uint64_t> &Record,
    unsigned Abbrev) {
  Record.push_back(N->isDistinct());
  Record.push_back(VE.getMetadataOrNullID(N->getRawName()));
  Record.push_back(VE.getMetadataOrNullID(N->getType()));

  Stream.EmitRecord(bitc::METADATA_TEMPLATE_TYPE, Record, Abbrev);
  Record.clear();
}

void ModuleBitcodeWriter::writeDITemplateValueParameter(
    const DITemplateValueParameter *N, SmallVectorImpl<uint64_t> &Record,
    unsigned Abbrev) {
  Record.push_back(N->isDistinct());
  Record.push_back(N->getTag());
  Record.push_back(VE.getMetadataOrNullID(N->getRawName()));
  Record.push_back(VE.getMetadataOrNullID(N->getType()));
  Record.push_back(VE.getMetadataOrNullID(N->getValue()));

  Stream.EmitRecord(bitc::METADATA_TEMPLATE_VALUE, Record, Abbrev);
  Record.clear();
}

void ModuleBitcodeWriter::writeDIGlobalVariable(
    const DIGlobalVariable *N, SmallVectorImpl<uint64_t> &Record,
    unsigned Abbrev) {
  Record.push_back(N->isDistinct());
  Record.push_back(VE.getMetadataOrNullID(N->getScope()));
  Record.push_back(VE.getMetadataOrNullID(N->getRawName()));
  Record.push_back(VE.getMetadataOrNullID(N->getRawLinkageName()));
  Record.push_back(VE.getMetadataOrNullID(N->getFile()));
  Record.push_back(N->getLine());
  Record.push_back(VE.getMetadataOrNullID(N->getType()));
  Record.push_back(N->isLocalToUnit());
  Record.push_back(N->isDefinition());
  Record.push_back(VE.getMetadataOrNullID(N->getRawVariable()));
  Record.push_back(VE.getMetadataOrNullID(N->getStaticDataMemberDeclaration()));

  Stream.EmitRecord(bitc::METADATA_GLOBAL_VAR, Record, Abbrev);
  Record.clear();
}

void ModuleBitcodeWriter::writeDILocalVariable(
    const DILocalVariable *N, SmallVectorImpl<uint64_t> &Record,
    unsigned Abbrev) {
  Record.push_back(N->isDistinct());
  Record.push_back(VE.getMetadataOrNullID(N->getScope()));
  Record.push_back(VE.getMetadataOrNullID(N->getRawName()));
  Record.push_back(VE.getMetadataOrNullID(N->getFile()));
  Record.push_back(N->getLine());
  Record.push_back(VE.getMetadataOrNullID(N->getType()));
  Record.push_back(N->getArg());
  Record.push_back(N->getFlags());

  Stream.EmitRecord(bitc::METADATA_LOCAL_VAR, Record, Abbrev);
  Record.clear();
}

void ModuleBitcodeWriter::writeDIExpression(const DIExpression *N,
                                            SmallVectorImpl<uint64_t> &Record,
                                            unsigned Abbrev) {
  Record.reserve(N->getElements().size() + 1);

  Record.push_back(N->isDistinct());
  Record.append(N->elements_begin(), N->elements_end());

  Stream.EmitRecord(bitc::METADATA_EXPRESSION, Record, Abbrev);
  Record.clear();
}

void ModuleBitcodeWriter::writeDIObjCProperty(const DIObjCProperty *N,
                                              SmallVectorImpl<uint64_t> &Record,
                                              unsigned Abbrev) {
  Record.push_back(N->isDistinct());
  Record.push_back(VE.getMetadataOrNullID(N->getRawName()));
  Record.push_back(VE.getMetadataOrNullID(N->getFile()));
  Record.push_back(N->getLine());
  Record.push_back(VE.getMetadataOrNullID(N->getRawSetterName()));
  Record.push_back(VE.getMetadataOrNullID(N->getRawGetterName()));
  Record.push_back(N->getAttributes());
  Record.push_back(VE.getMetadataOrNullID(N->getType()));

  Stream.EmitRecord(bitc::METADATA_OBJC_PROPERTY, Record, Abbrev);
  Record.clear();
}

void ModuleBitcodeWriter::writeDIImportedEntity(
    const DIImportedEntity *N, SmallVectorImpl<uint64_t> &Record,
    unsigned Abbrev) {
  Record.push_back(N->isDistinct());
  Record.push_back(N->getTag());
  Record.push_back(VE.getMetadataOrNullID(N->getScope()));
  Record.push_back(VE.getMetadataOrNullID(N->getEntity()));
  Record.push_back(N->getLine());
  Record.push_back(VE.getMetadataOrNullID(N->getRawName()));

  Stream.EmitRecord(bitc::METADATA_IMPORTED_ENTITY, Record, Abbrev);
  Record.clear();
}

unsigned ModuleBitcodeWriter::createNamedMetadataAbbrev() {
  BitCodeAbbrev *Abbv = new BitCodeAbbrev();
  Abbv->Add(BitCodeAbbrevOp(bitc::METADATA_NAME));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 8));
  return Stream.EmitAbbrev(Abbv);
}

void ModuleBitcodeWriter::writeNamedMetadata(
    SmallVectorImpl<uint64_t> &Record) {
  if (M.named_metadata_empty())
    return;

  unsigned Abbrev = createNamedMetadataAbbrev();
  for (const NamedMDNode &NMD : M.named_metadata()) {
    // Write name.
    StringRef Str = NMD.getName();
    Record.append(Str.bytes_begin(), Str.bytes_end());
    Stream.EmitRecord(bitc::METADATA_NAME, Record, Abbrev);
    Record.clear();

    // Write named metadata operands.
    for (const MDNode *N : NMD.operands())
      Record.push_back(VE.getMetadataID(N));
    Stream.EmitRecord(bitc::METADATA_NAMED_NODE, Record, 0);
    Record.clear();
  }
}

unsigned ModuleBitcodeWriter::createMetadataStringsAbbrev() {
  BitCodeAbbrev *Abbv = new BitCodeAbbrev();
  Abbv->Add(BitCodeAbbrevOp(bitc::METADATA_STRINGS));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 6)); // # of strings
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 6)); // offset to chars
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Blob));
  return Stream.EmitAbbrev(Abbv);
}

/// Write out a record for MDString.
///
/// All the metadata strings in a metadata block are emitted in a single
/// record.  The sizes and strings themselves are shoved into a blob.
void ModuleBitcodeWriter::writeMetadataStrings(
    ArrayRef<const Metadata *> Strings, SmallVectorImpl<uint64_t> &Record) {
  if (Strings.empty())
    return;

  // Start the record with the number of strings.
  Record.push_back(bitc::METADATA_STRINGS);
  Record.push_back(Strings.size());

  // Emit the sizes of the strings in the blob.
  SmallString<256> Blob;
  {
    BitstreamWriter W(Blob);
    for (const Metadata *MD : Strings)
      W.EmitVBR(cast<MDString>(MD)->getLength(), 6);
    W.FlushToWord();
  }

  // Add the offset to the strings to the record.
  Record.push_back(Blob.size());

  // Add the strings to the blob.
  for (const Metadata *MD : Strings)
    Blob.append(cast<MDString>(MD)->getString());

  // Emit the final record.
  Stream.EmitRecordWithBlob(createMetadataStringsAbbrev(), Record, Blob);
  Record.clear();
}

void ModuleBitcodeWriter::writeMetadataRecords(
    ArrayRef<const Metadata *> MDs, SmallVectorImpl<uint64_t> &Record) {
  if (MDs.empty())
    return;

  // Initialize MDNode abbreviations.
#define HANDLE_MDNODE_LEAF(CLASS) unsigned CLASS##Abbrev = 0;
#include "llvm/IR/Metadata.def"

  for (const Metadata *MD : MDs) {
    if (const MDNode *N = dyn_cast<MDNode>(MD)) {
      assert(N->isResolved() && "Expected forward references to be resolved");

      switch (N->getMetadataID()) {
      default:
        llvm_unreachable("Invalid MDNode subclass");
#define HANDLE_MDNODE_LEAF(CLASS)                                              \
  case Metadata::CLASS##Kind:                                                  \
    write##CLASS(cast<CLASS>(N), Record, CLASS##Abbrev);                       \
    continue;
#include "llvm/IR/Metadata.def"
      }
    }
    writeValueAsMetadata(cast<ValueAsMetadata>(MD), Record);
  }
}

void ModuleBitcodeWriter::writeModuleMetadata() {
  if (!VE.hasMDs() && M.named_metadata_empty())
    return;

  Stream.EnterSubblock(bitc::METADATA_BLOCK_ID, 3);
  SmallVector<uint64_t, 64> Record;
  writeMetadataStrings(VE.getMDStrings(), Record);
  writeMetadataRecords(VE.getNonMDStrings(), Record);
  writeNamedMetadata(Record);

  auto AddDeclAttachedMetadata = [&](const GlobalObject &GO) {
    SmallVector<uint64_t, 4> Record;
    Record.push_back(VE.getValueID(&GO));
    pushGlobalMetadataAttachment(Record, GO);
    Stream.EmitRecord(bitc::METADATA_GLOBAL_DECL_ATTACHMENT, Record);
  };
  for (const Function &F : M)
    if (F.isDeclaration() && F.hasMetadata())
      AddDeclAttachedMetadata(F);
  // FIXME: Only store metadata for declarations here, and move data for global
  // variable definitions to a separate block (PR28134).
  for (const GlobalVariable &GV : M.globals())
    if (GV.hasMetadata())
      AddDeclAttachedMetadata(GV);

  Stream.ExitBlock();
}

void ModuleBitcodeWriter::writeFunctionMetadata(const Function &F) {
  if (!VE.hasMDs())
    return;

  Stream.EnterSubblock(bitc::METADATA_BLOCK_ID, 3);
  SmallVector<uint64_t, 64> Record;
  writeMetadataStrings(VE.getMDStrings(), Record);
  writeMetadataRecords(VE.getNonMDStrings(), Record);
  Stream.ExitBlock();
}

void ModuleBitcodeWriter::pushGlobalMetadataAttachment(
    SmallVectorImpl<uint64_t> &Record, const GlobalObject &GO) {
  // [n x [id, mdnode]]
  SmallVector<std::pair<unsigned, MDNode *>, 4> MDs;
  GO.getAllMetadata(MDs);
  for (const auto &I : MDs) {
    Record.push_back(I.first);
    Record.push_back(VE.getMetadataID(I.second));
  }
}

void ModuleBitcodeWriter::writeFunctionMetadataAttachment(const Function &F) {
  Stream.EnterSubblock(bitc::METADATA_ATTACHMENT_ID, 3);

  SmallVector<uint64_t, 64> Record;

  if (F.hasMetadata()) {
    pushGlobalMetadataAttachment(Record, F);
    Stream.EmitRecord(bitc::METADATA_ATTACHMENT, Record, 0);
    Record.clear();
  }

  // Write metadata attachments
  // METADATA_ATTACHMENT - [m x [value, [n x [id, mdnode]]]
  SmallVector<std::pair<unsigned, MDNode *>, 4> MDs;
  for (const BasicBlock &BB : F)
    for (const Instruction &I : BB) {
      MDs.clear();
      I.getAllMetadataOtherThanDebugLoc(MDs);

      // If no metadata, ignore instruction.
      if (MDs.empty()) continue;

      Record.push_back(VE.getInstructionID(&I));

      for (unsigned i = 0, e = MDs.size(); i != e; ++i) {
        Record.push_back(MDs[i].first);
        Record.push_back(VE.getMetadataID(MDs[i].second));
      }
      Stream.EmitRecord(bitc::METADATA_ATTACHMENT, Record, 0);
      Record.clear();
    }

  Stream.ExitBlock();
}

void ModuleBitcodeWriter::writeModuleMetadataKinds() {
  SmallVector<uint64_t, 64> Record;

  // Write metadata kinds
  // METADATA_KIND - [n x [id, name]]
  SmallVector<StringRef, 8> Names;
  M.getMDKindNames(Names);

  if (Names.empty()) return;

  Stream.EnterSubblock(bitc::METADATA_KIND_BLOCK_ID, 3);

  for (unsigned MDKindID = 0, e = Names.size(); MDKindID != e; ++MDKindID) {
    Record.push_back(MDKindID);
    StringRef KName = Names[MDKindID];
    Record.append(KName.begin(), KName.end());

    Stream.EmitRecord(bitc::METADATA_KIND, Record, 0);
    Record.clear();
  }

  Stream.ExitBlock();
}

void ModuleBitcodeWriter::writeOperandBundleTags() {
  // Write metadata kinds
  //
  // OPERAND_BUNDLE_TAGS_BLOCK_ID : N x OPERAND_BUNDLE_TAG
  //
  // OPERAND_BUNDLE_TAG - [strchr x N]

  SmallVector<StringRef, 8> Tags;
  M.getOperandBundleTags(Tags);

  if (Tags.empty())
    return;

  Stream.EnterSubblock(bitc::OPERAND_BUNDLE_TAGS_BLOCK_ID, 3);

  SmallVector<uint64_t, 64> Record;

  for (auto Tag : Tags) {
    Record.append(Tag.begin(), Tag.end());

    Stream.EmitRecord(bitc::OPERAND_BUNDLE_TAG, Record, 0);
    Record.clear();
  }

  Stream.ExitBlock();
}

static void emitSignedInt64(SmallVectorImpl<uint64_t> &Vals, uint64_t V) {
  if ((int64_t)V >= 0)
    Vals.push_back(V << 1);
  else
    Vals.push_back((-V << 1) | 1);
}

void ModuleBitcodeWriter::writeConstants(unsigned FirstVal, unsigned LastVal,
                                         bool isGlobal) {
  if (FirstVal == LastVal) return;

  Stream.EnterSubblock(bitc::CONSTANTS_BLOCK_ID, 4);

  unsigned AggregateAbbrev = 0;
  unsigned String8Abbrev = 0;
  unsigned CString7Abbrev = 0;
  unsigned CString6Abbrev = 0;
  // If this is a constant pool for the module, emit module-specific abbrevs.
  if (isGlobal) {
    // Abbrev for CST_CODE_AGGREGATE.
    BitCodeAbbrev *Abbv = new BitCodeAbbrev();
    Abbv->Add(BitCodeAbbrevOp(bitc::CST_CODE_AGGREGATE));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, Log2_32_Ceil(LastVal+1)));
    AggregateAbbrev = Stream.EmitAbbrev(Abbv);

    // Abbrev for CST_CODE_STRING.
    Abbv = new BitCodeAbbrev();
    Abbv->Add(BitCodeAbbrevOp(bitc::CST_CODE_STRING));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 8));
    String8Abbrev = Stream.EmitAbbrev(Abbv);
    // Abbrev for CST_CODE_CSTRING.
    Abbv = new BitCodeAbbrev();
    Abbv->Add(BitCodeAbbrevOp(bitc::CST_CODE_CSTRING));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 7));
    CString7Abbrev = Stream.EmitAbbrev(Abbv);
    // Abbrev for CST_CODE_CSTRING.
    Abbv = new BitCodeAbbrev();
    Abbv->Add(BitCodeAbbrevOp(bitc::CST_CODE_CSTRING));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Char6));
    CString6Abbrev = Stream.EmitAbbrev(Abbv);
  }

  SmallVector<uint64_t, 64> Record;

  const ValueEnumerator::ValueList &Vals = VE.getValues();
  Type *LastTy = nullptr;
  for (unsigned i = FirstVal; i != LastVal; ++i) {
    const Value *V = Vals[i].first;
    // If we need to switch types, do so now.
    if (V->getType() != LastTy) {
      LastTy = V->getType();
      Record.push_back(VE.getTypeID(LastTy));
      Stream.EmitRecord(bitc::CST_CODE_SETTYPE, Record,
                        CONSTANTS_SETTYPE_ABBREV);
      Record.clear();
    }

    if (const InlineAsm *IA = dyn_cast<InlineAsm>(V)) {
      Record.push_back(unsigned(IA->hasSideEffects()) |
                       unsigned(IA->isAlignStack()) << 1 |
                       unsigned(IA->getDialect()&1) << 2);

      // Add the asm string.
      const std::string &AsmStr = IA->getAsmString();
      Record.push_back(AsmStr.size());
      Record.append(AsmStr.begin(), AsmStr.end());

      // Add the constraint string.
      const std::string &ConstraintStr = IA->getConstraintString();
      Record.push_back(ConstraintStr.size());
      Record.append(ConstraintStr.begin(), ConstraintStr.end());
      Stream.EmitRecord(bitc::CST_CODE_INLINEASM, Record);
      Record.clear();
      continue;
    }
    const Constant *C = cast<Constant>(V);
    unsigned Code = -1U;
    unsigned AbbrevToUse = 0;
    if (C->isNullValue()) {
      Code = bitc::CST_CODE_NULL;
    } else if (isa<UndefValue>(C)) {
      Code = bitc::CST_CODE_UNDEF;
    } else if (const ConstantInt *IV = dyn_cast<ConstantInt>(C)) {
      if (IV->getBitWidth() <= 64) {
        uint64_t V = IV->getSExtValue();
        emitSignedInt64(Record, V);
        Code = bitc::CST_CODE_INTEGER;
        AbbrevToUse = CONSTANTS_INTEGER_ABBREV;
      } else {                             // Wide integers, > 64 bits in size.
        // We have an arbitrary precision integer value to write whose
        // bit width is > 64. However, in canonical unsigned integer
        // format it is likely that the high bits are going to be zero.
        // So, we only write the number of active words.
        unsigned NWords = IV->getValue().getActiveWords();
        const uint64_t *RawWords = IV->getValue().getRawData();
        for (unsigned i = 0; i != NWords; ++i) {
          emitSignedInt64(Record, RawWords[i]);
        }
        Code = bitc::CST_CODE_WIDE_INTEGER;
      }
    } else if (const ConstantFP *CFP = dyn_cast<ConstantFP>(C)) {
      Code = bitc::CST_CODE_FLOAT;
      Type *Ty = CFP->getType();
      if (Ty->isHalfTy() || Ty->isFloatTy() || Ty->isDoubleTy()) {
        Record.push_back(CFP->getValueAPF().bitcastToAPInt().getZExtValue());
      } else if (Ty->isX86_FP80Ty()) {
        // api needed to prevent premature destruction
        // bits are not in the same order as a normal i80 APInt, compensate.
        APInt api = CFP->getValueAPF().bitcastToAPInt();
        const uint64_t *p = api.getRawData();
        Record.push_back((p[1] << 48) | (p[0] >> 16));
        Record.push_back(p[0] & 0xffffLL);
      } else if (Ty->isFP128Ty() || Ty->isPPC_FP128Ty()) {
        APInt api = CFP->getValueAPF().bitcastToAPInt();
        const uint64_t *p = api.getRawData();
        Record.push_back(p[0]);
        Record.push_back(p[1]);
      } else {
        assert (0 && "Unknown FP type!");
      }
    } else if (isa<ConstantDataSequential>(C) &&
               cast<ConstantDataSequential>(C)->isString()) {
      const ConstantDataSequential *Str = cast<ConstantDataSequential>(C);
      // Emit constant strings specially.
      unsigned NumElts = Str->getNumElements();
      // If this is a null-terminated string, use the denser CSTRING encoding.
      if (Str->isCString()) {
        Code = bitc::CST_CODE_CSTRING;
        --NumElts;  // Don't encode the null, which isn't allowed by char6.
      } else {
        Code = bitc::CST_CODE_STRING;
        AbbrevToUse = String8Abbrev;
      }
      bool isCStr7 = Code == bitc::CST_CODE_CSTRING;
      bool isCStrChar6 = Code == bitc::CST_CODE_CSTRING;
      for (unsigned i = 0; i != NumElts; ++i) {
        unsigned char V = Str->getElementAsInteger(i);
        Record.push_back(V);
        isCStr7 &= (V & 128) == 0;
        if (isCStrChar6)
          isCStrChar6 = BitCodeAbbrevOp::isChar6(V);
      }

      if (isCStrChar6)
        AbbrevToUse = CString6Abbrev;
      else if (isCStr7)
        AbbrevToUse = CString7Abbrev;
    } else if (const ConstantDataSequential *CDS =
                  dyn_cast<ConstantDataSequential>(C)) {
      Code = bitc::CST_CODE_DATA;
      Type *EltTy = CDS->getType()->getElementType();
      if (isa<IntegerType>(EltTy)) {
        for (unsigned i = 0, e = CDS->getNumElements(); i != e; ++i)
          Record.push_back(CDS->getElementAsInteger(i));
      } else {
        for (unsigned i = 0, e = CDS->getNumElements(); i != e; ++i)
          Record.push_back(
              CDS->getElementAsAPFloat(i).bitcastToAPInt().getLimitedValue());
      }
    } else if (isa<ConstantAggregate>(C)) {
      Code = bitc::CST_CODE_AGGREGATE;
      for (const Value *Op : C->operands())
        Record.push_back(VE.getValueID(Op));
      AbbrevToUse = AggregateAbbrev;
    } else if (const ConstantExpr *CE = dyn_cast<ConstantExpr>(C)) {
      switch (CE->getOpcode()) {
      default:
        if (Instruction::isCast(CE->getOpcode())) {
          Code = bitc::CST_CODE_CE_CAST;
          Record.push_back(getEncodedCastOpcode(CE->getOpcode()));
          Record.push_back(VE.getTypeID(C->getOperand(0)->getType()));
          Record.push_back(VE.getValueID(C->getOperand(0)));
          AbbrevToUse = CONSTANTS_CE_CAST_Abbrev;
        } else {
          assert(CE->getNumOperands() == 2 && "Unknown constant expr!");
          Code = bitc::CST_CODE_CE_BINOP;
          Record.push_back(getEncodedBinaryOpcode(CE->getOpcode()));
          Record.push_back(VE.getValueID(C->getOperand(0)));
          Record.push_back(VE.getValueID(C->getOperand(1)));
          uint64_t Flags = getOptimizationFlags(CE);
          if (Flags != 0)
            Record.push_back(Flags);
        }
        break;
      case Instruction::GetElementPtr: {
        Code = bitc::CST_CODE_CE_GEP;
        const auto *GO = cast<GEPOperator>(C);
        if (GO->isInBounds())
          Code = bitc::CST_CODE_CE_INBOUNDS_GEP;
        Record.push_back(VE.getTypeID(GO->getSourceElementType()));
        for (unsigned i = 0, e = CE->getNumOperands(); i != e; ++i) {
          Record.push_back(VE.getTypeID(C->getOperand(i)->getType()));
          Record.push_back(VE.getValueID(C->getOperand(i)));
        }
        break;
      }
      case Instruction::Select:
        Code = bitc::CST_CODE_CE_SELECT;
        Record.push_back(VE.getValueID(C->getOperand(0)));
        Record.push_back(VE.getValueID(C->getOperand(1)));
        Record.push_back(VE.getValueID(C->getOperand(2)));
        break;
      case Instruction::ExtractElement:
        Code = bitc::CST_CODE_CE_EXTRACTELT;
        Record.push_back(VE.getTypeID(C->getOperand(0)->getType()));
        Record.push_back(VE.getValueID(C->getOperand(0)));
        Record.push_back(VE.getTypeID(C->getOperand(1)->getType()));
        Record.push_back(VE.getValueID(C->getOperand(1)));
        break;
      case Instruction::InsertElement:
        Code = bitc::CST_CODE_CE_INSERTELT;
        Record.push_back(VE.getValueID(C->getOperand(0)));
        Record.push_back(VE.getValueID(C->getOperand(1)));
        Record.push_back(VE.getTypeID(C->getOperand(2)->getType()));
        Record.push_back(VE.getValueID(C->getOperand(2)));
        break;
      case Instruction::ShuffleVector:
        // If the return type and argument types are the same, this is a
        // standard shufflevector instruction.  If the types are different,
        // then the shuffle is widening or truncating the input vectors, and
        // the argument type must also be encoded.
        if (C->getType() == C->getOperand(0)->getType()) {
          Code = bitc::CST_CODE_CE_SHUFFLEVEC;
        } else {
          Code = bitc::CST_CODE_CE_SHUFVEC_EX;
          Record.push_back(VE.getTypeID(C->getOperand(0)->getType()));
        }
        Record.push_back(VE.getValueID(C->getOperand(0)));
        Record.push_back(VE.getValueID(C->getOperand(1)));
        Record.push_back(VE.getValueID(C->getOperand(2)));
        break;
      case Instruction::ICmp:
      case Instruction::FCmp:
        Code = bitc::CST_CODE_CE_CMP;
        Record.push_back(VE.getTypeID(C->getOperand(0)->getType()));
        Record.push_back(VE.getValueID(C->getOperand(0)));
        Record.push_back(VE.getValueID(C->getOperand(1)));
        Record.push_back(CE->getPredicate());
        break;
      }
    } else if (const BlockAddress *BA = dyn_cast<BlockAddress>(C)) {
      Code = bitc::CST_CODE_BLOCKADDRESS;
      Record.push_back(VE.getTypeID(BA->getFunction()->getType()));
      Record.push_back(VE.getValueID(BA->getFunction()));
      Record.push_back(VE.getGlobalBasicBlockID(BA->getBasicBlock()));
    } else {
#ifndef NDEBUG
      C->dump();
#endif
      llvm_unreachable("Unknown constant!");
    }
    Stream.EmitRecord(Code, Record, AbbrevToUse);
    Record.clear();
  }

  Stream.ExitBlock();
}

void ModuleBitcodeWriter::writeModuleConstants() {
  const ValueEnumerator::ValueList &Vals = VE.getValues();

  // Find the first constant to emit, which is the first non-globalvalue value.
  // We know globalvalues have been emitted by WriteModuleInfo.
  for (unsigned i = 0, e = Vals.size(); i != e; ++i) {
    if (!isa<GlobalValue>(Vals[i].first)) {
      writeConstants(i, Vals.size(), true);
      return;
    }
  }
}

/// pushValueAndType - The file has to encode both the value and type id for
/// many values, because we need to know what type to create for forward
/// references.  However, most operands are not forward references, so this type
/// field is not needed.
///
/// This function adds V's value ID to Vals.  If the value ID is higher than the
/// instruction ID, then it is a forward reference, and it also includes the
/// type ID.  The value ID that is written is encoded relative to the InstID.
bool ModuleBitcodeWriter::pushValueAndType(const Value *V, unsigned InstID,
                                           SmallVectorImpl<unsigned> &Vals) {
  unsigned ValID = VE.getValueID(V);
  // Make encoding relative to the InstID.
  Vals.push_back(InstID - ValID);
  if (ValID >= InstID) {
    Vals.push_back(VE.getTypeID(V->getType()));
    return true;
  }
  return false;
}

void ModuleBitcodeWriter::writeOperandBundles(ImmutableCallSite CS,
                                              unsigned InstID) {
  SmallVector<unsigned, 64> Record;
  LLVMContext &C = CS.getInstruction()->getContext();

  for (unsigned i = 0, e = CS.getNumOperandBundles(); i != e; ++i) {
    const auto &Bundle = CS.getOperandBundleAt(i);
    Record.push_back(C.getOperandBundleTagID(Bundle.getTagName()));

    for (auto &Input : Bundle.Inputs)
      pushValueAndType(Input, InstID, Record);

    Stream.EmitRecord(bitc::FUNC_CODE_OPERAND_BUNDLE, Record);
    Record.clear();
  }
}

/// pushValue - Like pushValueAndType, but where the type of the value is
/// omitted (perhaps it was already encoded in an earlier operand).
void ModuleBitcodeWriter::pushValue(const Value *V, unsigned InstID,
                                    SmallVectorImpl<unsigned> &Vals) {
  unsigned ValID = VE.getValueID(V);
  Vals.push_back(InstID - ValID);
}

void ModuleBitcodeWriter::pushValueSigned(const Value *V, unsigned InstID,
                                          SmallVectorImpl<uint64_t> &Vals) {
  unsigned ValID = VE.getValueID(V);
  int64_t diff = ((int32_t)InstID - (int32_t)ValID);
  emitSignedInt64(Vals, diff);
}

/// WriteInstruction - Emit an instruction to the specified stream.
void ModuleBitcodeWriter::writeInstruction(const Instruction &I,
                                           unsigned InstID,
                                           SmallVectorImpl<unsigned> &Vals) {
  unsigned Code = 0;
  unsigned AbbrevToUse = 0;
  VE.setInstructionID(&I);
  switch (I.getOpcode()) {
  default:
    if (Instruction::isCast(I.getOpcode())) {
      Code = bitc::FUNC_CODE_INST_CAST;
      if (!pushValueAndType(I.getOperand(0), InstID, Vals))
        AbbrevToUse = FUNCTION_INST_CAST_ABBREV;
      Vals.push_back(VE.getTypeID(I.getType()));
      Vals.push_back(getEncodedCastOpcode(I.getOpcode()));
    } else {
      assert(isa<BinaryOperator>(I) && "Unknown instruction!");
      Code = bitc::FUNC_CODE_INST_BINOP;
      if (!pushValueAndType(I.getOperand(0), InstID, Vals))
        AbbrevToUse = FUNCTION_INST_BINOP_ABBREV;
      pushValue(I.getOperand(1), InstID, Vals);
      Vals.push_back(getEncodedBinaryOpcode(I.getOpcode()));
      uint64_t Flags = getOptimizationFlags(&I);
      if (Flags != 0) {
        if (AbbrevToUse == FUNCTION_INST_BINOP_ABBREV)
          AbbrevToUse = FUNCTION_INST_BINOP_FLAGS_ABBREV;
        Vals.push_back(Flags);
      }
    }
    break;

  case Instruction::GetElementPtr: {
    Code = bitc::FUNC_CODE_INST_GEP;
    AbbrevToUse = FUNCTION_INST_GEP_ABBREV;
    auto &GEPInst = cast<GetElementPtrInst>(I);
    Vals.push_back(GEPInst.isInBounds());
    Vals.push_back(VE.getTypeID(GEPInst.getSourceElementType()));
    for (unsigned i = 0, e = I.getNumOperands(); i != e; ++i)
      pushValueAndType(I.getOperand(i), InstID, Vals);
    break;
  }
  case Instruction::ExtractValue: {
    Code = bitc::FUNC_CODE_INST_EXTRACTVAL;
    pushValueAndType(I.getOperand(0), InstID, Vals);
    const ExtractValueInst *EVI = cast<ExtractValueInst>(&I);
    Vals.append(EVI->idx_begin(), EVI->idx_end());
    break;
  }
  case Instruction::InsertValue: {
    Code = bitc::FUNC_CODE_INST_INSERTVAL;
    pushValueAndType(I.getOperand(0), InstID, Vals);
    pushValueAndType(I.getOperand(1), InstID, Vals);
    const InsertValueInst *IVI = cast<InsertValueInst>(&I);
    Vals.append(IVI->idx_begin(), IVI->idx_end());
    break;
  }
  case Instruction::Select:
    Code = bitc::FUNC_CODE_INST_VSELECT;
    pushValueAndType(I.getOperand(1), InstID, Vals);
    pushValue(I.getOperand(2), InstID, Vals);
    pushValueAndType(I.getOperand(0), InstID, Vals);
    break;
  case Instruction::ExtractElement:
    Code = bitc::FUNC_CODE_INST_EXTRACTELT;
    pushValueAndType(I.getOperand(0), InstID, Vals);
    pushValueAndType(I.getOperand(1), InstID, Vals);
    break;
  case Instruction::InsertElement:
    Code = bitc::FUNC_CODE_INST_INSERTELT;
    pushValueAndType(I.getOperand(0), InstID, Vals);
    pushValue(I.getOperand(1), InstID, Vals);
    pushValueAndType(I.getOperand(2), InstID, Vals);
    break;
  case Instruction::ShuffleVector:
    Code = bitc::FUNC_CODE_INST_SHUFFLEVEC;
    pushValueAndType(I.getOperand(0), InstID, Vals);
    pushValue(I.getOperand(1), InstID, Vals);
    pushValue(I.getOperand(2), InstID, Vals);
    break;
  case Instruction::ICmp:
  case Instruction::FCmp: {
    // compare returning Int1Ty or vector of Int1Ty
    Code = bitc::FUNC_CODE_INST_CMP2;
    pushValueAndType(I.getOperand(0), InstID, Vals);
    pushValue(I.getOperand(1), InstID, Vals);
    Vals.push_back(cast<CmpInst>(I).getPredicate());
    uint64_t Flags = getOptimizationFlags(&I);
    if (Flags != 0)
      Vals.push_back(Flags);
    break;
  }

  case Instruction::Ret:
    {
      Code = bitc::FUNC_CODE_INST_RET;
      unsigned NumOperands = I.getNumOperands();
      if (NumOperands == 0)
        AbbrevToUse = FUNCTION_INST_RET_VOID_ABBREV;
      else if (NumOperands == 1) {
        if (!pushValueAndType(I.getOperand(0), InstID, Vals))
          AbbrevToUse = FUNCTION_INST_RET_VAL_ABBREV;
      } else {
        for (unsigned i = 0, e = NumOperands; i != e; ++i)
          pushValueAndType(I.getOperand(i), InstID, Vals);
      }
    }
    break;
  case Instruction::Br:
    {
      Code = bitc::FUNC_CODE_INST_BR;
      const BranchInst &II = cast<BranchInst>(I);
      Vals.push_back(VE.getValueID(II.getSuccessor(0)));
      if (II.isConditional()) {
        Vals.push_back(VE.getValueID(II.getSuccessor(1)));
        pushValue(II.getCondition(), InstID, Vals);
      }
    }
    break;
  case Instruction::Switch:
    {
      Code = bitc::FUNC_CODE_INST_SWITCH;
      const SwitchInst &SI = cast<SwitchInst>(I);
      Vals.push_back(VE.getTypeID(SI.getCondition()->getType()));
      pushValue(SI.getCondition(), InstID, Vals);
      Vals.push_back(VE.getValueID(SI.getDefaultDest()));
      for (SwitchInst::ConstCaseIt Case : SI.cases()) {
        Vals.push_back(VE.getValueID(Case.getCaseValue()));
        Vals.push_back(VE.getValueID(Case.getCaseSuccessor()));
      }
    }
    break;
  case Instruction::IndirectBr:
    Code = bitc::FUNC_CODE_INST_INDIRECTBR;
    Vals.push_back(VE.getTypeID(I.getOperand(0)->getType()));
    // Encode the address operand as relative, but not the basic blocks.
    pushValue(I.getOperand(0), InstID, Vals);
    for (unsigned i = 1, e = I.getNumOperands(); i != e; ++i)
      Vals.push_back(VE.getValueID(I.getOperand(i)));
    break;

  case Instruction::Invoke: {
    const InvokeInst *II = cast<InvokeInst>(&I);
    const Value *Callee = II->getCalledValue();
    FunctionType *FTy = II->getFunctionType();

    if (II->hasOperandBundles())
      writeOperandBundles(II, InstID);

    Code = bitc::FUNC_CODE_INST_INVOKE;

    Vals.push_back(VE.getAttributeID(II->getAttributes()));
    Vals.push_back(II->getCallingConv() | 1 << 13);
    Vals.push_back(VE.getValueID(II->getNormalDest()));
    Vals.push_back(VE.getValueID(II->getUnwindDest()));
    Vals.push_back(VE.getTypeID(FTy));
    pushValueAndType(Callee, InstID, Vals);

    // Emit value #'s for the fixed parameters.
    for (unsigned i = 0, e = FTy->getNumParams(); i != e; ++i)
      pushValue(I.getOperand(i), InstID, Vals); // fixed param.

    // Emit type/value pairs for varargs params.
    if (FTy->isVarArg()) {
      for (unsigned i = FTy->getNumParams(), e = I.getNumOperands()-3;
           i != e; ++i)
        pushValueAndType(I.getOperand(i), InstID, Vals); // vararg
    }
    break;
  }
  case Instruction::Resume:
    Code = bitc::FUNC_CODE_INST_RESUME;
    pushValueAndType(I.getOperand(0), InstID, Vals);
    break;
  case Instruction::CleanupRet: {
    Code = bitc::FUNC_CODE_INST_CLEANUPRET;
    const auto &CRI = cast<CleanupReturnInst>(I);
    pushValue(CRI.getCleanupPad(), InstID, Vals);
    if (CRI.hasUnwindDest())
      Vals.push_back(VE.getValueID(CRI.getUnwindDest()));
    break;
  }
  case Instruction::CatchRet: {
    Code = bitc::FUNC_CODE_INST_CATCHRET;
    const auto &CRI = cast<CatchReturnInst>(I);
    pushValue(CRI.getCatchPad(), InstID, Vals);
    Vals.push_back(VE.getValueID(CRI.getSuccessor()));
    break;
  }
  case Instruction::CleanupPad:
  case Instruction::CatchPad: {
    const auto &FuncletPad = cast<FuncletPadInst>(I);
    Code = isa<CatchPadInst>(FuncletPad) ? bitc::FUNC_CODE_INST_CATCHPAD
                                         : bitc::FUNC_CODE_INST_CLEANUPPAD;
    pushValue(FuncletPad.getParentPad(), InstID, Vals);

    unsigned NumArgOperands = FuncletPad.getNumArgOperands();
    Vals.push_back(NumArgOperands);
    for (unsigned Op = 0; Op != NumArgOperands; ++Op)
      pushValueAndType(FuncletPad.getArgOperand(Op), InstID, Vals);
    break;
  }
  case Instruction::CatchSwitch: {
    Code = bitc::FUNC_CODE_INST_CATCHSWITCH;
    const auto &CatchSwitch = cast<CatchSwitchInst>(I);

    pushValue(CatchSwitch.getParentPad(), InstID, Vals);

    unsigned NumHandlers = CatchSwitch.getNumHandlers();
    Vals.push_back(NumHandlers);
    for (const BasicBlock *CatchPadBB : CatchSwitch.handlers())
      Vals.push_back(VE.getValueID(CatchPadBB));

    if (CatchSwitch.hasUnwindDest())
      Vals.push_back(VE.getValueID(CatchSwitch.getUnwindDest()));
    break;
  }
  case Instruction::Unreachable:
    Code = bitc::FUNC_CODE_INST_UNREACHABLE;
    AbbrevToUse = FUNCTION_INST_UNREACHABLE_ABBREV;
    break;

  case Instruction::PHI: {
    const PHINode &PN = cast<PHINode>(I);
    Code = bitc::FUNC_CODE_INST_PHI;
    // With the newer instruction encoding, forward references could give
    // negative valued IDs.  This is most common for PHIs, so we use
    // signed VBRs.
    SmallVector<uint64_t, 128> Vals64;
    Vals64.push_back(VE.getTypeID(PN.getType()));
    for (unsigned i = 0, e = PN.getNumIncomingValues(); i != e; ++i) {
      pushValueSigned(PN.getIncomingValue(i), InstID, Vals64);
      Vals64.push_back(VE.getValueID(PN.getIncomingBlock(i)));
    }
    // Emit a Vals64 vector and exit.
    Stream.EmitRecord(Code, Vals64, AbbrevToUse);
    Vals64.clear();
    return;
  }

  case Instruction::LandingPad: {
    const LandingPadInst &LP = cast<LandingPadInst>(I);
    Code = bitc::FUNC_CODE_INST_LANDINGPAD;
    Vals.push_back(VE.getTypeID(LP.getType()));
    Vals.push_back(LP.isCleanup());
    Vals.push_back(LP.getNumClauses());
    for (unsigned I = 0, E = LP.getNumClauses(); I != E; ++I) {
      if (LP.isCatch(I))
        Vals.push_back(LandingPadInst::Catch);
      else
        Vals.push_back(LandingPadInst::Filter);
      pushValueAndType(LP.getClause(I), InstID, Vals);
    }
    break;
  }

  case Instruction::Alloca: {
    Code = bitc::FUNC_CODE_INST_ALLOCA;
    const AllocaInst &AI = cast<AllocaInst>(I);
    Vals.push_back(VE.getTypeID(AI.getAllocatedType()));
    Vals.push_back(VE.getTypeID(I.getOperand(0)->getType()));
    Vals.push_back(VE.getValueID(I.getOperand(0))); // size.
    unsigned AlignRecord = Log2_32(AI.getAlignment()) + 1;
    assert(Log2_32(Value::MaximumAlignment) + 1 < 1 << 5 &&
           "not enough bits for maximum alignment");
    assert(AlignRecord < 1 << 5 && "alignment greater than 1 << 64");
    AlignRecord |= AI.isUsedWithInAlloca() << 5;
    AlignRecord |= 1 << 6;
    AlignRecord |= AI.isSwiftError() << 7;
    Vals.push_back(AlignRecord);
    break;
  }

  case Instruction::Load:
    if (cast<LoadInst>(I).isAtomic()) {
      Code = bitc::FUNC_CODE_INST_LOADATOMIC;
      pushValueAndType(I.getOperand(0), InstID, Vals);
    } else {
      Code = bitc::FUNC_CODE_INST_LOAD;
      if (!pushValueAndType(I.getOperand(0), InstID, Vals)) // ptr
        AbbrevToUse = FUNCTION_INST_LOAD_ABBREV;
    }
    Vals.push_back(VE.getTypeID(I.getType()));
    Vals.push_back(Log2_32(cast<LoadInst>(I).getAlignment())+1);
    Vals.push_back(cast<LoadInst>(I).isVolatile());
    if (cast<LoadInst>(I).isAtomic()) {
      Vals.push_back(getEncodedOrdering(cast<LoadInst>(I).getOrdering()));
      Vals.push_back(getEncodedSynchScope(cast<LoadInst>(I).getSynchScope()));
    }
    break;
  case Instruction::Store:
    if (cast<StoreInst>(I).isAtomic())
      Code = bitc::FUNC_CODE_INST_STOREATOMIC;
    else
      Code = bitc::FUNC_CODE_INST_STORE;
    pushValueAndType(I.getOperand(1), InstID, Vals); // ptrty + ptr
    pushValueAndType(I.getOperand(0), InstID, Vals); // valty + val
    Vals.push_back(Log2_32(cast<StoreInst>(I).getAlignment())+1);
    Vals.push_back(cast<StoreInst>(I).isVolatile());
    if (cast<StoreInst>(I).isAtomic()) {
      Vals.push_back(getEncodedOrdering(cast<StoreInst>(I).getOrdering()));
      Vals.push_back(getEncodedSynchScope(cast<StoreInst>(I).getSynchScope()));
    }
    break;
  case Instruction::AtomicCmpXchg:
    Code = bitc::FUNC_CODE_INST_CMPXCHG;
    pushValueAndType(I.getOperand(0), InstID, Vals); // ptrty + ptr
    pushValueAndType(I.getOperand(1), InstID, Vals); // cmp.
    pushValue(I.getOperand(2), InstID, Vals);        // newval.
    Vals.push_back(cast<AtomicCmpXchgInst>(I).isVolatile());
    Vals.push_back(
        getEncodedOrdering(cast<AtomicCmpXchgInst>(I).getSuccessOrdering()));
    Vals.push_back(
        getEncodedSynchScope(cast<AtomicCmpXchgInst>(I).getSynchScope()));
    Vals.push_back(
        getEncodedOrdering(cast<AtomicCmpXchgInst>(I).getFailureOrdering()));
    Vals.push_back(cast<AtomicCmpXchgInst>(I).isWeak());
    break;
  case Instruction::AtomicRMW:
    Code = bitc::FUNC_CODE_INST_ATOMICRMW;
    pushValueAndType(I.getOperand(0), InstID, Vals); // ptrty + ptr
    pushValue(I.getOperand(1), InstID, Vals);        // val.
    Vals.push_back(
        getEncodedRMWOperation(cast<AtomicRMWInst>(I).getOperation()));
    Vals.push_back(cast<AtomicRMWInst>(I).isVolatile());
    Vals.push_back(getEncodedOrdering(cast<AtomicRMWInst>(I).getOrdering()));
    Vals.push_back(
        getEncodedSynchScope(cast<AtomicRMWInst>(I).getSynchScope()));
    break;
  case Instruction::Fence:
    Code = bitc::FUNC_CODE_INST_FENCE;
    Vals.push_back(getEncodedOrdering(cast<FenceInst>(I).getOrdering()));
    Vals.push_back(getEncodedSynchScope(cast<FenceInst>(I).getSynchScope()));
    break;
  case Instruction::Call: {
    const CallInst &CI = cast<CallInst>(I);
    FunctionType *FTy = CI.getFunctionType();

    if (CI.hasOperandBundles())
      writeOperandBundles(&CI, InstID);

    Code = bitc::FUNC_CODE_INST_CALL;

    Vals.push_back(VE.getAttributeID(CI.getAttributes()));

    unsigned Flags = getOptimizationFlags(&I);
    Vals.push_back(CI.getCallingConv() << bitc::CALL_CCONV |
                   unsigned(CI.isTailCall()) << bitc::CALL_TAIL |
                   unsigned(CI.isMustTailCall()) << bitc::CALL_MUSTTAIL |
                   1 << bitc::CALL_EXPLICIT_TYPE |
                   unsigned(CI.isNoTailCall()) << bitc::CALL_NOTAIL |
                   unsigned(Flags != 0) << bitc::CALL_FMF);
    if (Flags != 0)
      Vals.push_back(Flags);

    Vals.push_back(VE.getTypeID(FTy));
    pushValueAndType(CI.getCalledValue(), InstID, Vals); // Callee

    // Emit value #'s for the fixed parameters.
    for (unsigned i = 0, e = FTy->getNumParams(); i != e; ++i) {
      // Check for labels (can happen with asm labels).
      if (FTy->getParamType(i)->isLabelTy())
        Vals.push_back(VE.getValueID(CI.getArgOperand(i)));
      else
        pushValue(CI.getArgOperand(i), InstID, Vals); // fixed param.
    }

    // Emit type/value pairs for varargs params.
    if (FTy->isVarArg()) {
      for (unsigned i = FTy->getNumParams(), e = CI.getNumArgOperands();
           i != e; ++i)
        pushValueAndType(CI.getArgOperand(i), InstID, Vals); // varargs
    }
    break;
  }
  case Instruction::VAArg:
    Code = bitc::FUNC_CODE_INST_VAARG;
    Vals.push_back(VE.getTypeID(I.getOperand(0)->getType()));   // valistty
    pushValue(I.getOperand(0), InstID, Vals);                   // valist.
    Vals.push_back(VE.getTypeID(I.getType())); // restype.
    break;
  }

  Stream.EmitRecord(Code, Vals, AbbrevToUse);
  Vals.clear();
}

/// Emit names for globals/functions etc. \p IsModuleLevel is true when
/// we are writing the module-level VST, where we are including a function
/// bitcode index and need to backpatch the VST forward declaration record.
void ModuleBitcodeWriter::writeValueSymbolTable(
    const ValueSymbolTable &VST, bool IsModuleLevel,
    DenseMap<const Function *, uint64_t> *FunctionToBitcodeIndex) {
  if (VST.empty()) {
    // writeValueSymbolTableForwardDecl should have returned early as
    // well. Ensure this handling remains in sync by asserting that
    // the placeholder offset is not set.
    assert(!IsModuleLevel || !hasVSTOffsetPlaceholder());
    return;
  }

  if (IsModuleLevel && hasVSTOffsetPlaceholder()) {
    // Get the offset of the VST we are writing, and backpatch it into
    // the VST forward declaration record.
    uint64_t VSTOffset = Stream.GetCurrentBitNo();
    // The BitcodeStartBit was the stream offset of the actual bitcode
    // (e.g. excluding any initial darwin header).
    VSTOffset -= bitcodeStartBit();
    assert((VSTOffset & 31) == 0 && "VST block not 32-bit aligned");
    Stream.BackpatchWord(VSTOffsetPlaceholder, VSTOffset / 32);
  }

  Stream.EnterSubblock(bitc::VALUE_SYMTAB_BLOCK_ID, 4);

  // For the module-level VST, add abbrev Ids for the VST_CODE_FNENTRY
  // records, which are not used in the per-function VSTs.
  unsigned FnEntry8BitAbbrev;
  unsigned FnEntry7BitAbbrev;
  unsigned FnEntry6BitAbbrev;
  if (IsModuleLevel && hasVSTOffsetPlaceholder()) {
    // 8-bit fixed-width VST_CODE_FNENTRY function strings.
    BitCodeAbbrev *Abbv = new BitCodeAbbrev();
    Abbv->Add(BitCodeAbbrevOp(bitc::VST_CODE_FNENTRY));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8)); // value id
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8)); // funcoffset
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 8));
    FnEntry8BitAbbrev = Stream.EmitAbbrev(Abbv);

    // 7-bit fixed width VST_CODE_FNENTRY function strings.
    Abbv = new BitCodeAbbrev();
    Abbv->Add(BitCodeAbbrevOp(bitc::VST_CODE_FNENTRY));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8)); // value id
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8)); // funcoffset
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 7));
    FnEntry7BitAbbrev = Stream.EmitAbbrev(Abbv);

    // 6-bit char6 VST_CODE_FNENTRY function strings.
    Abbv = new BitCodeAbbrev();
    Abbv->Add(BitCodeAbbrevOp(bitc::VST_CODE_FNENTRY));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8)); // value id
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8)); // funcoffset
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Char6));
    FnEntry6BitAbbrev = Stream.EmitAbbrev(Abbv);
  }

  // FIXME: Set up the abbrev, we know how many values there are!
  // FIXME: We know if the type names can use 7-bit ascii.
  SmallVector<unsigned, 64> NameVals;

  for (const ValueName &Name : VST) {
    // Figure out the encoding to use for the name.
    StringEncoding Bits =
        getStringEncoding(Name.getKeyData(), Name.getKeyLength());

    unsigned AbbrevToUse = VST_ENTRY_8_ABBREV;
    NameVals.push_back(VE.getValueID(Name.getValue()));

    Function *F = dyn_cast<Function>(Name.getValue());
    if (!F) {
      // If value is an alias, need to get the aliased base object to
      // see if it is a function.
      auto *GA = dyn_cast<GlobalAlias>(Name.getValue());
      if (GA && GA->getBaseObject())
        F = dyn_cast<Function>(GA->getBaseObject());
    }

    // VST_CODE_ENTRY:   [valueid, namechar x N]
    // VST_CODE_FNENTRY: [valueid, funcoffset, namechar x N]
    // VST_CODE_BBENTRY: [bbid, namechar x N]
    unsigned Code;
    if (isa<BasicBlock>(Name.getValue())) {
      Code = bitc::VST_CODE_BBENTRY;
      if (Bits == SE_Char6)
        AbbrevToUse = VST_BBENTRY_6_ABBREV;
    } else if (F && !F->isDeclaration()) {
      // Must be the module-level VST, where we pass in the Index and
      // have a VSTOffsetPlaceholder. The function-level VST should not
      // contain any Function symbols.
      assert(FunctionToBitcodeIndex);
      assert(hasVSTOffsetPlaceholder());

      // Save the word offset of the function (from the start of the
      // actual bitcode written to the stream).
      uint64_t BitcodeIndex = (*FunctionToBitcodeIndex)[F] - bitcodeStartBit();
      assert((BitcodeIndex & 31) == 0 && "function block not 32-bit aligned");
      NameVals.push_back(BitcodeIndex / 32);

      Code = bitc::VST_CODE_FNENTRY;
      AbbrevToUse = FnEntry8BitAbbrev;
      if (Bits == SE_Char6)
        AbbrevToUse = FnEntry6BitAbbrev;
      else if (Bits == SE_Fixed7)
        AbbrevToUse = FnEntry7BitAbbrev;
    } else {
      Code = bitc::VST_CODE_ENTRY;
      if (Bits == SE_Char6)
        AbbrevToUse = VST_ENTRY_6_ABBREV;
      else if (Bits == SE_Fixed7)
        AbbrevToUse = VST_ENTRY_7_ABBREV;
    }

    for (const auto P : Name.getKey())
      NameVals.push_back((unsigned char)P);

    // Emit the finished record.
    Stream.EmitRecord(Code, NameVals, AbbrevToUse);
    NameVals.clear();
  }
  Stream.ExitBlock();
}

/// Emit function names and summary offsets for the combined index
/// used by ThinLTO.
void IndexBitcodeWriter::writeCombinedValueSymbolTable() {
  assert(hasVSTOffsetPlaceholder() && "Expected non-zero VSTOffsetPlaceholder");
  // Get the offset of the VST we are writing, and backpatch it into
  // the VST forward declaration record.
  uint64_t VSTOffset = Stream.GetCurrentBitNo();
  assert((VSTOffset & 31) == 0 && "VST block not 32-bit aligned");
  Stream.BackpatchWord(VSTOffsetPlaceholder, VSTOffset / 32);

  Stream.EnterSubblock(bitc::VALUE_SYMTAB_BLOCK_ID, 4);

  BitCodeAbbrev *Abbv = new BitCodeAbbrev();
  Abbv->Add(BitCodeAbbrevOp(bitc::VST_CODE_COMBINED_ENTRY));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8)); // valueid
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8)); // refguid
  unsigned EntryAbbrev = Stream.EmitAbbrev(Abbv);

  SmallVector<uint64_t, 64> NameVals;
  for (const auto &GVI : valueIds()) {
    // VST_CODE_COMBINED_ENTRY: [valueid, refguid]
    NameVals.push_back(GVI.second);
    NameVals.push_back(GVI.first);

    // Emit the finished record.
    Stream.EmitRecord(bitc::VST_CODE_COMBINED_ENTRY, NameVals, EntryAbbrev);
    NameVals.clear();
  }
  Stream.ExitBlock();
}

void ModuleBitcodeWriter::writeUseList(UseListOrder &&Order) {
  assert(Order.Shuffle.size() >= 2 && "Shuffle too small");
  unsigned Code;
  if (isa<BasicBlock>(Order.V))
    Code = bitc::USELIST_CODE_BB;
  else
    Code = bitc::USELIST_CODE_DEFAULT;

  SmallVector<uint64_t, 64> Record(Order.Shuffle.begin(), Order.Shuffle.end());
  Record.push_back(VE.getValueID(Order.V));
  Stream.EmitRecord(Code, Record);
}

void ModuleBitcodeWriter::writeUseListBlock(const Function *F) {
  assert(VE.shouldPreserveUseListOrder() &&
         "Expected to be preserving use-list order");

  auto hasMore = [&]() {
    return !VE.UseListOrders.empty() && VE.UseListOrders.back().F == F;
  };
  if (!hasMore())
    // Nothing to do.
    return;

  Stream.EnterSubblock(bitc::USELIST_BLOCK_ID, 3);
  while (hasMore()) {
    writeUseList(std::move(VE.UseListOrders.back()));
    VE.UseListOrders.pop_back();
  }
  Stream.ExitBlock();
}

/// Emit a function body to the module stream.
void ModuleBitcodeWriter::writeFunction(
    const Function &F,
    DenseMap<const Function *, uint64_t> &FunctionToBitcodeIndex) {
  // Save the bitcode index of the start of this function block for recording
  // in the VST.
  FunctionToBitcodeIndex[&F] = Stream.GetCurrentBitNo();

  Stream.EnterSubblock(bitc::FUNCTION_BLOCK_ID, 4);
  VE.incorporateFunction(F);

  SmallVector<unsigned, 64> Vals;

  // Emit the number of basic blocks, so the reader can create them ahead of
  // time.
  Vals.push_back(VE.getBasicBlocks().size());
  Stream.EmitRecord(bitc::FUNC_CODE_DECLAREBLOCKS, Vals);
  Vals.clear();

  // If there are function-local constants, emit them now.
  unsigned CstStart, CstEnd;
  VE.getFunctionConstantRange(CstStart, CstEnd);
  writeConstants(CstStart, CstEnd, false);

  // If there is function-local metadata, emit it now.
  writeFunctionMetadata(F);

  // Keep a running idea of what the instruction ID is.
  unsigned InstID = CstEnd;

  bool NeedsMetadataAttachment = F.hasMetadata();

  DILocation *LastDL = nullptr;
  // Finally, emit all the instructions, in order.
  for (Function::const_iterator BB = F.begin(), E = F.end(); BB != E; ++BB)
    for (BasicBlock::const_iterator I = BB->begin(), E = BB->end();
         I != E; ++I) {
      writeInstruction(*I, InstID, Vals);

      if (!I->getType()->isVoidTy())
        ++InstID;

      // If the instruction has metadata, write a metadata attachment later.
      NeedsMetadataAttachment |= I->hasMetadataOtherThanDebugLoc();

      // If the instruction has a debug location, emit it.
      DILocation *DL = I->getDebugLoc();
      if (!DL)
        continue;

      if (DL == LastDL) {
        // Just repeat the same debug loc as last time.
        Stream.EmitRecord(bitc::FUNC_CODE_DEBUG_LOC_AGAIN, Vals);
        continue;
      }

      Vals.push_back(DL->getLine());
      Vals.push_back(DL->getColumn());
      Vals.push_back(VE.getMetadataOrNullID(DL->getScope()));
      Vals.push_back(VE.getMetadataOrNullID(DL->getInlinedAt()));
      Stream.EmitRecord(bitc::FUNC_CODE_DEBUG_LOC, Vals);
      Vals.clear();

      LastDL = DL;
    }

  // Emit names for all the instructions etc.
  writeValueSymbolTable(F.getValueSymbolTable());

  if (NeedsMetadataAttachment)
    writeFunctionMetadataAttachment(F);
  if (VE.shouldPreserveUseListOrder())
    writeUseListBlock(&F);
  VE.purgeFunction();
  Stream.ExitBlock();
}

// Emit blockinfo, which defines the standard abbreviations etc.
void ModuleBitcodeWriter::writeBlockInfo() {
  // We only want to emit block info records for blocks that have multiple
  // instances: CONSTANTS_BLOCK, FUNCTION_BLOCK and VALUE_SYMTAB_BLOCK.
  // Other blocks can define their abbrevs inline.
  Stream.EnterBlockInfoBlock(2);

  { // 8-bit fixed-width VST_CODE_ENTRY/VST_CODE_BBENTRY strings.
    BitCodeAbbrev *Abbv = new BitCodeAbbrev();
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 3));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 8));
    if (Stream.EmitBlockInfoAbbrev(bitc::VALUE_SYMTAB_BLOCK_ID, Abbv) !=
        VST_ENTRY_8_ABBREV)
      llvm_unreachable("Unexpected abbrev ordering!");
  }

  { // 7-bit fixed width VST_CODE_ENTRY strings.
    BitCodeAbbrev *Abbv = new BitCodeAbbrev();
    Abbv->Add(BitCodeAbbrevOp(bitc::VST_CODE_ENTRY));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 7));
    if (Stream.EmitBlockInfoAbbrev(bitc::VALUE_SYMTAB_BLOCK_ID, Abbv) !=
        VST_ENTRY_7_ABBREV)
      llvm_unreachable("Unexpected abbrev ordering!");
  }
  { // 6-bit char6 VST_CODE_ENTRY strings.
    BitCodeAbbrev *Abbv = new BitCodeAbbrev();
    Abbv->Add(BitCodeAbbrevOp(bitc::VST_CODE_ENTRY));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Char6));
    if (Stream.EmitBlockInfoAbbrev(bitc::VALUE_SYMTAB_BLOCK_ID, Abbv) !=
        VST_ENTRY_6_ABBREV)
      llvm_unreachable("Unexpected abbrev ordering!");
  }
  { // 6-bit char6 VST_CODE_BBENTRY strings.
    BitCodeAbbrev *Abbv = new BitCodeAbbrev();
    Abbv->Add(BitCodeAbbrevOp(bitc::VST_CODE_BBENTRY));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Char6));
    if (Stream.EmitBlockInfoAbbrev(bitc::VALUE_SYMTAB_BLOCK_ID, Abbv) !=
        VST_BBENTRY_6_ABBREV)
      llvm_unreachable("Unexpected abbrev ordering!");
  }



  { // SETTYPE abbrev for CONSTANTS_BLOCK.
    BitCodeAbbrev *Abbv = new BitCodeAbbrev();
    Abbv->Add(BitCodeAbbrevOp(bitc::CST_CODE_SETTYPE));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed,
                              VE.computeBitsRequiredForTypeIndicies()));
    if (Stream.EmitBlockInfoAbbrev(bitc::CONSTANTS_BLOCK_ID, Abbv) !=
        CONSTANTS_SETTYPE_ABBREV)
      llvm_unreachable("Unexpected abbrev ordering!");
  }

  { // INTEGER abbrev for CONSTANTS_BLOCK.
    BitCodeAbbrev *Abbv = new BitCodeAbbrev();
    Abbv->Add(BitCodeAbbrevOp(bitc::CST_CODE_INTEGER));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));
    if (Stream.EmitBlockInfoAbbrev(bitc::CONSTANTS_BLOCK_ID, Abbv) !=
        CONSTANTS_INTEGER_ABBREV)
      llvm_unreachable("Unexpected abbrev ordering!");
  }

  { // CE_CAST abbrev for CONSTANTS_BLOCK.
    BitCodeAbbrev *Abbv = new BitCodeAbbrev();
    Abbv->Add(BitCodeAbbrevOp(bitc::CST_CODE_CE_CAST));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 4));  // cast opc
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed,       // typeid
                              VE.computeBitsRequiredForTypeIndicies()));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));    // value id

    if (Stream.EmitBlockInfoAbbrev(bitc::CONSTANTS_BLOCK_ID, Abbv) !=
        CONSTANTS_CE_CAST_Abbrev)
      llvm_unreachable("Unexpected abbrev ordering!");
  }
  { // NULL abbrev for CONSTANTS_BLOCK.
    BitCodeAbbrev *Abbv = new BitCodeAbbrev();
    Abbv->Add(BitCodeAbbrevOp(bitc::CST_CODE_NULL));
    if (Stream.EmitBlockInfoAbbrev(bitc::CONSTANTS_BLOCK_ID, Abbv) !=
        CONSTANTS_NULL_Abbrev)
      llvm_unreachable("Unexpected abbrev ordering!");
  }

  // FIXME: This should only use space for first class types!

  { // INST_LOAD abbrev for FUNCTION_BLOCK.
    BitCodeAbbrev *Abbv = new BitCodeAbbrev();
    Abbv->Add(BitCodeAbbrevOp(bitc::FUNC_CODE_INST_LOAD));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 6)); // Ptr
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed,    // dest ty
                              VE.computeBitsRequiredForTypeIndicies()));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 4)); // Align
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 1)); // volatile
    if (Stream.EmitBlockInfoAbbrev(bitc::FUNCTION_BLOCK_ID, Abbv) !=
        FUNCTION_INST_LOAD_ABBREV)
      llvm_unreachable("Unexpected abbrev ordering!");
  }
  { // INST_BINOP abbrev for FUNCTION_BLOCK.
    BitCodeAbbrev *Abbv = new BitCodeAbbrev();
    Abbv->Add(BitCodeAbbrevOp(bitc::FUNC_CODE_INST_BINOP));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 6)); // LHS
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 6)); // RHS
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 4)); // opc
    if (Stream.EmitBlockInfoAbbrev(bitc::FUNCTION_BLOCK_ID, Abbv) !=
        FUNCTION_INST_BINOP_ABBREV)
      llvm_unreachable("Unexpected abbrev ordering!");
  }
  { // INST_BINOP_FLAGS abbrev for FUNCTION_BLOCK.
    BitCodeAbbrev *Abbv = new BitCodeAbbrev();
    Abbv->Add(BitCodeAbbrevOp(bitc::FUNC_CODE_INST_BINOP));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 6)); // LHS
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 6)); // RHS
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 4)); // opc
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 7)); // flags
    if (Stream.EmitBlockInfoAbbrev(bitc::FUNCTION_BLOCK_ID, Abbv) !=
        FUNCTION_INST_BINOP_FLAGS_ABBREV)
      llvm_unreachable("Unexpected abbrev ordering!");
  }
  { // INST_CAST abbrev for FUNCTION_BLOCK.
    BitCodeAbbrev *Abbv = new BitCodeAbbrev();
    Abbv->Add(BitCodeAbbrevOp(bitc::FUNC_CODE_INST_CAST));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 6));    // OpVal
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed,       // dest ty
                              VE.computeBitsRequiredForTypeIndicies()));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 4));  // opc
    if (Stream.EmitBlockInfoAbbrev(bitc::FUNCTION_BLOCK_ID, Abbv) !=
        FUNCTION_INST_CAST_ABBREV)
      llvm_unreachable("Unexpected abbrev ordering!");
  }

  { // INST_RET abbrev for FUNCTION_BLOCK.
    BitCodeAbbrev *Abbv = new BitCodeAbbrev();
    Abbv->Add(BitCodeAbbrevOp(bitc::FUNC_CODE_INST_RET));
    if (Stream.EmitBlockInfoAbbrev(bitc::FUNCTION_BLOCK_ID, Abbv) !=
        FUNCTION_INST_RET_VOID_ABBREV)
      llvm_unreachable("Unexpected abbrev ordering!");
  }
  { // INST_RET abbrev for FUNCTION_BLOCK.
    BitCodeAbbrev *Abbv = new BitCodeAbbrev();
    Abbv->Add(BitCodeAbbrevOp(bitc::FUNC_CODE_INST_RET));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 6)); // ValID
    if (Stream.EmitBlockInfoAbbrev(bitc::FUNCTION_BLOCK_ID, Abbv) !=
        FUNCTION_INST_RET_VAL_ABBREV)
      llvm_unreachable("Unexpected abbrev ordering!");
  }
  { // INST_UNREACHABLE abbrev for FUNCTION_BLOCK.
    BitCodeAbbrev *Abbv = new BitCodeAbbrev();
    Abbv->Add(BitCodeAbbrevOp(bitc::FUNC_CODE_INST_UNREACHABLE));
    if (Stream.EmitBlockInfoAbbrev(bitc::FUNCTION_BLOCK_ID, Abbv) !=
        FUNCTION_INST_UNREACHABLE_ABBREV)
      llvm_unreachable("Unexpected abbrev ordering!");
  }
  {
    BitCodeAbbrev *Abbv = new BitCodeAbbrev();
    Abbv->Add(BitCodeAbbrevOp(bitc::FUNC_CODE_INST_GEP));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 1));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, // dest ty
                              Log2_32_Ceil(VE.getTypes().size() + 1)));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));
    Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 6));
    if (Stream.EmitBlockInfoAbbrev(bitc::FUNCTION_BLOCK_ID, Abbv) !=
        FUNCTION_INST_GEP_ABBREV)
      llvm_unreachable("Unexpected abbrev ordering!");
  }

  Stream.ExitBlock();
}

/// Write the module path strings, currently only used when generating
/// a combined index file.
void IndexBitcodeWriter::writeModStrings() {
  Stream.EnterSubblock(bitc::MODULE_STRTAB_BLOCK_ID, 3);

  // TODO: See which abbrev sizes we actually need to emit

  // 8-bit fixed-width MST_ENTRY strings.
  BitCodeAbbrev *Abbv = new BitCodeAbbrev();
  Abbv->Add(BitCodeAbbrevOp(bitc::MST_CODE_ENTRY));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 8));
  unsigned Abbrev8Bit = Stream.EmitAbbrev(Abbv);

  // 7-bit fixed width MST_ENTRY strings.
  Abbv = new BitCodeAbbrev();
  Abbv->Add(BitCodeAbbrevOp(bitc::MST_CODE_ENTRY));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 7));
  unsigned Abbrev7Bit = Stream.EmitAbbrev(Abbv);

  // 6-bit char6 MST_ENTRY strings.
  Abbv = new BitCodeAbbrev();
  Abbv->Add(BitCodeAbbrevOp(bitc::MST_CODE_ENTRY));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Char6));
  unsigned Abbrev6Bit = Stream.EmitAbbrev(Abbv);

  // Module Hash, 160 bits SHA1. Optionally, emitted after each MST_CODE_ENTRY.
  Abbv = new BitCodeAbbrev();
  Abbv->Add(BitCodeAbbrevOp(bitc::MST_CODE_HASH));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 32));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 32));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 32));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 32));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Fixed, 32));
  unsigned AbbrevHash = Stream.EmitAbbrev(Abbv);

  SmallVector<unsigned, 64> Vals;
  for (const auto &MPSE : Index.modulePaths()) {
    if (!doIncludeModule(MPSE.getKey()))
      continue;
    StringEncoding Bits =
        getStringEncoding(MPSE.getKey().data(), MPSE.getKey().size());
    unsigned AbbrevToUse = Abbrev8Bit;
    if (Bits == SE_Char6)
      AbbrevToUse = Abbrev6Bit;
    else if (Bits == SE_Fixed7)
      AbbrevToUse = Abbrev7Bit;

    Vals.push_back(MPSE.getValue().first);

    for (const auto P : MPSE.getKey())
      Vals.push_back((unsigned char)P);

    // Emit the finished record.
    Stream.EmitRecord(bitc::MST_CODE_ENTRY, Vals, AbbrevToUse);

    Vals.clear();
    // Emit an optional hash for the module now
    auto &Hash = MPSE.getValue().second;
    bool AllZero = true; // Detect if the hash is empty, and do not generate it
    for (auto Val : Hash) {
      if (Val)
        AllZero = false;
      Vals.push_back(Val);
    }
    if (!AllZero) {
      // Emit the hash record.
      Stream.EmitRecord(bitc::MST_CODE_HASH, Vals, AbbrevHash);
    }

    Vals.clear();
  }
  Stream.ExitBlock();
}

// Helper to emit a single function summary record.
void ModuleBitcodeWriter::writePerModuleFunctionSummaryRecord(
    SmallVector<uint64_t, 64> &NameVals, GlobalValueSummary *Summary,
    unsigned ValueID, unsigned FSCallsAbbrev, unsigned FSCallsProfileAbbrev,
    const Function &F) {
  NameVals.push_back(ValueID);

  FunctionSummary *FS = cast<FunctionSummary>(Summary);
  NameVals.push_back(getEncodedGVSummaryFlags(FS->flags()));
  NameVals.push_back(FS->instCount());
  NameVals.push_back(FS->refs().size());

  unsigned SizeBeforeRefs = NameVals.size();
  for (auto &RI : FS->refs())
    NameVals.push_back(VE.getValueID(RI.getValue()));
  // Sort the refs for determinism output, the vector returned by FS->refs() has
  // been initialized from a DenseSet.
  std::sort(NameVals.begin() + SizeBeforeRefs, NameVals.end());

  std::vector<FunctionSummary::EdgeTy> Calls = FS->calls();
  std::sort(Calls.begin(), Calls.end(),
            [this](const FunctionSummary::EdgeTy &L,
                   const FunctionSummary::EdgeTy &R) {
              return VE.getValueID(L.first.getValue()) <
                     VE.getValueID(R.first.getValue());
            });
  bool HasProfileData = F.getEntryCount().hasValue();
  for (auto &ECI : Calls) {
    NameVals.push_back(VE.getValueID(ECI.first.getValue()));
    assert(ECI.second.CallsiteCount > 0 && "Expected at least one callsite");
    NameVals.push_back(ECI.second.CallsiteCount);
    if (HasProfileData)
      NameVals.push_back(ECI.second.ProfileCount);
  }

  unsigned FSAbbrev = (HasProfileData ? FSCallsProfileAbbrev : FSCallsAbbrev);
  unsigned Code =
      (HasProfileData ? bitc::FS_PERMODULE_PROFILE : bitc::FS_PERMODULE);

  // Emit the finished record.
  Stream.EmitRecord(Code, NameVals, FSAbbrev);
  NameVals.clear();
}

// Collect the global value references in the given variable's initializer,
// and emit them in a summary record.
void ModuleBitcodeWriter::writeModuleLevelReferences(
    const GlobalVariable &V, SmallVector<uint64_t, 64> &NameVals,
    unsigned FSModRefsAbbrev) {
  // Only interested in recording variable defs in the summary.
  if (V.isDeclaration())
    return;
  NameVals.push_back(VE.getValueID(&V));
  NameVals.push_back(getEncodedGVSummaryFlags(V));
  auto *Summary = Index->getGlobalValueSummary(V);
  GlobalVarSummary *VS = cast<GlobalVarSummary>(Summary);

  unsigned SizeBeforeRefs = NameVals.size();
  for (auto &RI : VS->refs())
    NameVals.push_back(VE.getValueID(RI.getValue()));
  // Sort the refs for determinism output, the vector returned by FS->refs() has
  // been initialized from a DenseSet.
  std::sort(NameVals.begin() + SizeBeforeRefs, NameVals.end());

  Stream.EmitRecord(bitc::FS_PERMODULE_GLOBALVAR_INIT_REFS, NameVals,
                    FSModRefsAbbrev);
  NameVals.clear();
}

// Current version for the summary.
// This is bumped whenever we introduce changes in the way some record are
// interpreted, like flags for instance.
static const uint64_t INDEX_VERSION = 1;

/// Emit the per-module summary section alongside the rest of
/// the module's bitcode.
void ModuleBitcodeWriter::writePerModuleGlobalValueSummary() {
  if (Index->begin() == Index->end())
    return;

  Stream.EnterSubblock(bitc::GLOBALVAL_SUMMARY_BLOCK_ID, 4);

  Stream.EmitRecord(bitc::FS_VERSION, ArrayRef<uint64_t>{INDEX_VERSION});

  // Abbrev for FS_PERMODULE.
  BitCodeAbbrev *Abbv = new BitCodeAbbrev();
  Abbv->Add(BitCodeAbbrevOp(bitc::FS_PERMODULE));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));   // valueid
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 6));   // flags
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));   // instcount
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 4));   // numrefs
  // numrefs x valueid, n x (valueid, callsitecount)
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));
  unsigned FSCallsAbbrev = Stream.EmitAbbrev(Abbv);

  // Abbrev for FS_PERMODULE_PROFILE.
  Abbv = new BitCodeAbbrev();
  Abbv->Add(BitCodeAbbrevOp(bitc::FS_PERMODULE_PROFILE));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));   // valueid
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 6));   // flags
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));   // instcount
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 4));   // numrefs
  // numrefs x valueid, n x (valueid, callsitecount, profilecount)
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));
  unsigned FSCallsProfileAbbrev = Stream.EmitAbbrev(Abbv);

  // Abbrev for FS_PERMODULE_GLOBALVAR_INIT_REFS.
  Abbv = new BitCodeAbbrev();
  Abbv->Add(BitCodeAbbrevOp(bitc::FS_PERMODULE_GLOBALVAR_INIT_REFS));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8)); // valueid
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 6)); // flags
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));  // valueids
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));
  unsigned FSModRefsAbbrev = Stream.EmitAbbrev(Abbv);

  // Abbrev for FS_ALIAS.
  Abbv = new BitCodeAbbrev();
  Abbv->Add(BitCodeAbbrevOp(bitc::FS_ALIAS));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));   // valueid
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 6));   // flags
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));   // valueid
  unsigned FSAliasAbbrev = Stream.EmitAbbrev(Abbv);

  SmallVector<uint64_t, 64> NameVals;
  // Iterate over the list of functions instead of the Index to
  // ensure the ordering is stable.
  for (const Function &F : M) {
    if (F.isDeclaration())
      continue;
    // Summary emission does not support anonymous functions, they have to
    // renamed using the anonymous function renaming pass.
    if (!F.hasName())
      report_fatal_error("Unexpected anonymous function when writing summary");

    auto *Summary = Index->getGlobalValueSummary(F);
    writePerModuleFunctionSummaryRecord(NameVals, Summary, VE.getValueID(&F),
                                        FSCallsAbbrev, FSCallsProfileAbbrev, F);
  }

  // Capture references from GlobalVariable initializers, which are outside
  // of a function scope.
  for (const GlobalVariable &G : M.globals())
    writeModuleLevelReferences(G, NameVals, FSModRefsAbbrev);

  for (const GlobalAlias &A : M.aliases()) {
    auto *Aliasee = A.getBaseObject();
    if (!Aliasee->hasName())
      // Nameless function don't have an entry in the summary, skip it.
      continue;
    auto AliasId = VE.getValueID(&A);
    auto AliaseeId = VE.getValueID(Aliasee);
    NameVals.push_back(AliasId);
    NameVals.push_back(getEncodedGVSummaryFlags(A));
    NameVals.push_back(AliaseeId);
    Stream.EmitRecord(bitc::FS_ALIAS, NameVals, FSAliasAbbrev);
    NameVals.clear();
  }

  Stream.ExitBlock();
}

/// Emit the combined summary section into the combined index file.
void IndexBitcodeWriter::writeCombinedGlobalValueSummary() {
  Stream.EnterSubblock(bitc::GLOBALVAL_SUMMARY_BLOCK_ID, 3);
  Stream.EmitRecord(bitc::FS_VERSION, ArrayRef<uint64_t>{INDEX_VERSION});

  // Abbrev for FS_COMBINED.
  BitCodeAbbrev *Abbv = new BitCodeAbbrev();
  Abbv->Add(BitCodeAbbrevOp(bitc::FS_COMBINED));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));   // valueid
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));   // modid
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 6));   // flags
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));   // instcount
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 4));   // numrefs
  // numrefs x valueid, n x (valueid, callsitecount)
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));
  unsigned FSCallsAbbrev = Stream.EmitAbbrev(Abbv);

  // Abbrev for FS_COMBINED_PROFILE.
  Abbv = new BitCodeAbbrev();
  Abbv->Add(BitCodeAbbrevOp(bitc::FS_COMBINED_PROFILE));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));   // valueid
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));   // modid
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 6));   // flags
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));   // instcount
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 4));   // numrefs
  // numrefs x valueid, n x (valueid, callsitecount, profilecount)
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));
  unsigned FSCallsProfileAbbrev = Stream.EmitAbbrev(Abbv);

  // Abbrev for FS_COMBINED_GLOBALVAR_INIT_REFS.
  Abbv = new BitCodeAbbrev();
  Abbv->Add(BitCodeAbbrevOp(bitc::FS_COMBINED_GLOBALVAR_INIT_REFS));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));   // valueid
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));   // modid
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 6));   // flags
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));    // valueids
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));
  unsigned FSModRefsAbbrev = Stream.EmitAbbrev(Abbv);

  // Abbrev for FS_COMBINED_ALIAS.
  Abbv = new BitCodeAbbrev();
  Abbv->Add(BitCodeAbbrevOp(bitc::FS_COMBINED_ALIAS));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));   // valueid
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));   // modid
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 6));   // flags
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 8));   // valueid
  unsigned FSAliasAbbrev = Stream.EmitAbbrev(Abbv);

  // The aliases are emitted as a post-pass, and will point to the value
  // id of the aliasee. Save them in a vector for post-processing.
  SmallVector<AliasSummary *, 64> Aliases;

  // Save the value id for each summary for alias emission.
  DenseMap<const GlobalValueSummary *, unsigned> SummaryToValueIdMap;

  SmallVector<uint64_t, 64> NameVals;

  // For local linkage, we also emit the original name separately
  // immediately after the record.
  auto MaybeEmitOriginalName = [&](GlobalValueSummary &S) {
    if (!GlobalValue::isLocalLinkage(S.linkage()))
      return;
    NameVals.push_back(S.getOriginalName());
    Stream.EmitRecord(bitc::FS_COMBINED_ORIGINAL_NAME, NameVals);
    NameVals.clear();
  };

  for (const auto &I : *this) {
    GlobalValueSummary *S = I.second;
    assert(S);

    assert(hasValueId(I.first));
    unsigned ValueId = getValueId(I.first);
    SummaryToValueIdMap[S] = ValueId;

    if (auto *AS = dyn_cast<AliasSummary>(S)) {
      // Will process aliases as a post-pass because the reader wants all
      // global to be loaded first.
      Aliases.push_back(AS);
      continue;
    }

    if (auto *VS = dyn_cast<GlobalVarSummary>(S)) {
      NameVals.push_back(ValueId);
      NameVals.push_back(Index.getModuleId(VS->modulePath()));
      NameVals.push_back(getEncodedGVSummaryFlags(VS->flags()));
      for (auto &RI : VS->refs()) {
        NameVals.push_back(getValueId(RI.getGUID()));
      }

      // Emit the finished record.
      Stream.EmitRecord(bitc::FS_COMBINED_GLOBALVAR_INIT_REFS, NameVals,
                        FSModRefsAbbrev);
      NameVals.clear();
      MaybeEmitOriginalName(*S);
      continue;
    }

    auto *FS = cast<FunctionSummary>(S);
    NameVals.push_back(ValueId);
    NameVals.push_back(Index.getModuleId(FS->modulePath()));
    NameVals.push_back(getEncodedGVSummaryFlags(FS->flags()));
    NameVals.push_back(FS->instCount());
    NameVals.push_back(FS->refs().size());

    for (auto &RI : FS->refs()) {
      NameVals.push_back(getValueId(RI.getGUID()));
    }

    bool HasProfileData = false;
    for (auto &EI : FS->calls()) {
      HasProfileData |= EI.second.ProfileCount != 0;
      if (HasProfileData)
        break;
    }

    for (auto &EI : FS->calls()) {
      // If this GUID doesn't have a value id, it doesn't have a function
      // summary and we don't need to record any calls to it.
      if (!hasValueId(EI.first.getGUID()))
        continue;
      NameVals.push_back(getValueId(EI.first.getGUID()));
      assert(EI.second.CallsiteCount > 0 && "Expected at least one callsite");
      NameVals.push_back(EI.second.CallsiteCount);
      if (HasProfileData)
        NameVals.push_back(EI.second.ProfileCount);
    }

    unsigned FSAbbrev = (HasProfileData ? FSCallsProfileAbbrev : FSCallsAbbrev);
    unsigned Code =
        (HasProfileData ? bitc::FS_COMBINED_PROFILE : bitc::FS_COMBINED);

    // Emit the finished record.
    Stream.EmitRecord(Code, NameVals, FSAbbrev);
    NameVals.clear();
    MaybeEmitOriginalName(*S);
  }

  for (auto *AS : Aliases) {
    auto AliasValueId = SummaryToValueIdMap[AS];
    assert(AliasValueId);
    NameVals.push_back(AliasValueId);
    NameVals.push_back(Index.getModuleId(AS->modulePath()));
    NameVals.push_back(getEncodedGVSummaryFlags(AS->flags()));
    auto AliaseeValueId = SummaryToValueIdMap[&AS->getAliasee()];
    assert(AliaseeValueId);
    NameVals.push_back(AliaseeValueId);

    // Emit the finished record.
    Stream.EmitRecord(bitc::FS_COMBINED_ALIAS, NameVals, FSAliasAbbrev);
    NameVals.clear();
    MaybeEmitOriginalName(*AS);
  }

  Stream.ExitBlock();
}

void ModuleBitcodeWriter::writeIdentificationBlock() {
  Stream.EnterSubblock(bitc::IDENTIFICATION_BLOCK_ID, 5);

  // Write the "user readable" string identifying the bitcode producer
  BitCodeAbbrev *Abbv = new BitCodeAbbrev();
  Abbv->Add(BitCodeAbbrevOp(bitc::IDENTIFICATION_CODE_STRING));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Array));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::Char6));
  auto StringAbbrev = Stream.EmitAbbrev(Abbv);
  writeStringRecord(bitc::IDENTIFICATION_CODE_STRING,
                    "LLVM" LLVM_VERSION_STRING, StringAbbrev);

  // Write the epoch version
  Abbv = new BitCodeAbbrev();
  Abbv->Add(BitCodeAbbrevOp(bitc::IDENTIFICATION_CODE_EPOCH));
  Abbv->Add(BitCodeAbbrevOp(BitCodeAbbrevOp::VBR, 6));
  auto EpochAbbrev = Stream.EmitAbbrev(Abbv);
  SmallVector<unsigned, 1> Vals = {bitc::BITCODE_CURRENT_EPOCH};
  Stream.EmitRecord(bitc::IDENTIFICATION_CODE_EPOCH, Vals, EpochAbbrev);
  Stream.ExitBlock();
}

void ModuleBitcodeWriter::writeModuleHash(size_t BlockStartPos) {
  // Emit the module's hash.
  // MODULE_CODE_HASH: [5*i32]
  SHA1 Hasher;
  Hasher.update(ArrayRef<uint8_t>((const uint8_t *)&(Buffer)[BlockStartPos],
                                  Buffer.size() - BlockStartPos));
  auto Hash = Hasher.result();
  SmallVector<uint64_t, 20> Vals;
  auto LShift = [&](unsigned char Val, unsigned Amount)
                    -> uint64_t { return ((uint64_t)Val) << Amount; };
  for (int Pos = 0; Pos < 20; Pos += 4) {
    uint32_t SubHash = LShift(Hash[Pos + 0], 24);
    SubHash |= LShift(Hash[Pos + 1], 16) | LShift(Hash[Pos + 2], 8) |
               (unsigned)(unsigned char)Hash[Pos + 3];
    Vals.push_back(SubHash);
  }

  // Emit the finished record.
  Stream.EmitRecord(bitc::MODULE_CODE_HASH, Vals);
}

void BitcodeWriter::write() {
  // Emit the file header first.
  writeBitcodeHeader();

  writeBlocks();
}

void ModuleBitcodeWriter::writeBlocks() {
  writeIdentificationBlock();
  writeModule();
}

void IndexBitcodeWriter::writeBlocks() {
  // Index contains only a single outer (module) block.
  writeIndex();
}

void ModuleBitcodeWriter::writeModule() {
  Stream.EnterSubblock(bitc::MODULE_BLOCK_ID, 3);
  size_t BlockStartPos = Buffer.size();

  SmallVector<unsigned, 1> Vals;
  unsigned CurVersion = 1;
  Vals.push_back(CurVersion);
  Stream.EmitRecord(bitc::MODULE_CODE_VERSION, Vals);

  // Emit blockinfo, which defines the standard abbreviations etc.
  writeBlockInfo();

  // Emit information about attribute groups.
  writeAttributeGroupTable();

  // Emit information about parameter attributes.
  writeAttributeTable();

  // Emit information describing all of the types in the module.
  writeTypeTable();

  writeComdats();

  // Emit top-level description of module, including target triple, inline asm,
  // descriptors for global variables, and function prototype info.
  writeModuleInfo();

  // Emit constants.
  writeModuleConstants();

  // Emit metadata kind names.
  writeModuleMetadataKinds();

  // Emit metadata.
  writeModuleMetadata();

  // Emit module-level use-lists.
  if (VE.shouldPreserveUseListOrder())
    writeUseListBlock(nullptr);

  writeOperandBundleTags();

  // Emit function bodies.
  DenseMap<const Function *, uint64_t> FunctionToBitcodeIndex;
  for (Module::const_iterator F = M.begin(), E = M.end(); F != E; ++F)
    if (!F->isDeclaration())
      writeFunction(*F, FunctionToBitcodeIndex);

  // Need to write after the above call to WriteFunction which populates
  // the summary information in the index.
  if (Index)
    writePerModuleGlobalValueSummary();

  writeValueSymbolTable(M.getValueSymbolTable(),
                        /* IsModuleLevel */ true, &FunctionToBitcodeIndex);

  if (GenerateHash) {
    writeModuleHash(BlockStartPos);
  }

  Stream.ExitBlock();
}

static void writeInt32ToBuffer(uint32_t Value, SmallVectorImpl<char> &Buffer,
                               uint32_t &Position) {
  support::endian::write32le(&Buffer[Position], Value);
  Position += 4;
}

/// If generating a bc file on darwin, we have to emit a
/// header and trailer to make it compatible with the system archiver.  To do
/// this we emit the following header, and then emit a trailer that pads the
/// file out to be a multiple of 16 bytes.
///
/// struct bc_header {
///   uint32_t Magic;         // 0x0B17C0DE
///   uint32_t Version;       // Version, currently always 0.
///   uint32_t BitcodeOffset; // Offset to traditional bitcode file.
///   uint32_t BitcodeSize;   // Size of traditional bitcode file.
///   uint32_t CPUType;       // CPU specifier.
///   ... potentially more later ...
/// };
static void emitDarwinBCHeaderAndTrailer(SmallVectorImpl<char> &Buffer,
                                         const Triple &TT) {
  unsigned CPUType = ~0U;

  // Match x86_64-*, i[3-9]86-*, powerpc-*, powerpc64-*, arm-*, thumb-*,
  // armv[0-9]-*, thumbv[0-9]-*, armv5te-*, or armv6t2-*. The CPUType is a magic
  // number from /usr/include/mach/machine.h.  It is ok to reproduce the
  // specific constants here because they are implicitly part of the Darwin ABI.
  enum {
    DARWIN_CPU_ARCH_ABI64      = 0x01000000,
    DARWIN_CPU_TYPE_X86        = 7,
    DARWIN_CPU_TYPE_ARM        = 12,
    DARWIN_CPU_TYPE_POWERPC    = 18
  };

  Triple::ArchType Arch = TT.getArch();
  if (Arch == Triple::x86_64)
    CPUType = DARWIN_CPU_TYPE_X86 | DARWIN_CPU_ARCH_ABI64;
  else if (Arch == Triple::x86)
    CPUType = DARWIN_CPU_TYPE_X86;
  else if (Arch == Triple::ppc)
    CPUType = DARWIN_CPU_TYPE_POWERPC;
  else if (Arch == Triple::ppc64)
    CPUType = DARWIN_CPU_TYPE_POWERPC | DARWIN_CPU_ARCH_ABI64;
  else if (Arch == Triple::arm || Arch == Triple::thumb)
    CPUType = DARWIN_CPU_TYPE_ARM;

  // Traditional Bitcode starts after header.
  assert(Buffer.size() >= BWH_HeaderSize &&
         "Expected header size to be reserved");
  unsigned BCOffset = BWH_HeaderSize;
  unsigned BCSize = Buffer.size() - BWH_HeaderSize;

  // Write the magic and version.
  unsigned Position = 0;
  writeInt32ToBuffer(0x0B17C0DE, Buffer, Position);
  writeInt32ToBuffer(0, Buffer, Position); // Version.
  writeInt32ToBuffer(BCOffset, Buffer, Position);
  writeInt32ToBuffer(BCSize, Buffer, Position);
  writeInt32ToBuffer(CPUType, Buffer, Position);

  // If the file is not a multiple of 16 bytes, insert dummy padding.
  while (Buffer.size() & 15)
    Buffer.push_back(0);
}

/// Helper to write the header common to all bitcode files.
void BitcodeWriter::writeBitcodeHeader() {
  // Emit the file header.
  Stream.Emit((unsigned)'B', 8);
  Stream.Emit((unsigned)'C', 8);
  Stream.Emit(0x0, 4);
  Stream.Emit(0xC, 4);
  Stream.Emit(0xE, 4);
  Stream.Emit(0xD, 4);
}

/// WriteBitcodeToFile - Write the specified module to the specified output
/// stream.
void llvm::WriteBitcodeToFile(const Module *M, raw_ostream &Out,
                              bool ShouldPreserveUseListOrder,
                              const ModuleSummaryIndex *Index,
                              bool GenerateHash) {
  SmallVector<char, 0> Buffer;
  Buffer.reserve(256*1024);

  // If this is darwin or another generic macho target, reserve space for the
  // header.
  Triple TT(M->getTargetTriple());
  if (TT.isOSDarwin() || TT.isOSBinFormatMachO())
    Buffer.insert(Buffer.begin(), BWH_HeaderSize, 0);

  // Emit the module into the buffer.
  ModuleBitcodeWriter ModuleWriter(M, Buffer, ShouldPreserveUseListOrder, Index,
                                   GenerateHash);
  ModuleWriter.write();

  if (TT.isOSDarwin() || TT.isOSBinFormatMachO())
    emitDarwinBCHeaderAndTrailer(Buffer, TT);

  // Write the generated bitstream to "Out".
  Out.write((char*)&Buffer.front(), Buffer.size());
}

void IndexBitcodeWriter::writeIndex() {
  Stream.EnterSubblock(bitc::MODULE_BLOCK_ID, 3);

  SmallVector<unsigned, 1> Vals;
  unsigned CurVersion = 1;
  Vals.push_back(CurVersion);
  Stream.EmitRecord(bitc::MODULE_CODE_VERSION, Vals);

  // If we have a VST, write the VSTOFFSET record placeholder.
  writeValueSymbolTableForwardDecl();

  // Write the module paths in the combined index.
  writeModStrings();

  // Write the summary combined index records.
  writeCombinedGlobalValueSummary();

  // Need a special VST writer for the combined index (we don't have a
  // real VST and real values when this is invoked).
  writeCombinedValueSymbolTable();

  Stream.ExitBlock();
}

// Write the specified module summary index to the given raw output stream,
// where it will be written in a new bitcode block. This is used when
// writing the combined index file for ThinLTO. When writing a subset of the
// index for a distributed backend, provide a \p ModuleToSummariesForIndex map.
void llvm::WriteIndexToFile(
    const ModuleSummaryIndex &Index, raw_ostream &Out,
    std::map<std::string, GVSummaryMapTy> *ModuleToSummariesForIndex) {
  SmallVector<char, 0> Buffer;
  Buffer.reserve(256 * 1024);

  IndexBitcodeWriter IndexWriter(Buffer, Index, ModuleToSummariesForIndex);
  IndexWriter.write();

  Out.write((char *)&Buffer.front(), Buffer.size());
}
