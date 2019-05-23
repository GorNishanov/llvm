//===- CXXSimplifyEH.cpp - Code to simplify C++ EH patterns -------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===--------------------------------------------------------------===//

#include "llvm/Analysis/EHPersonalities.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Pass.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/circular_raw_ostream.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"

using namespace llvm;

#define DEBUG_TYPE "cxx-eh-simplify"

static bool CheckFnName(const CallBase *I, StringRef Name) {
  if (auto *CalledF = I->getCalledFunction())
    if (CalledF->getName() == Name)
      return true;
  return false;
}

static bool CheckFnNames(const CallBase *I, StringRef Name1, StringRef Name2) {
  if (auto *CalledF = I->getCalledFunction()) {
    StringRef FnName = CalledF->getName();
    return (FnName == Name1 || FnName == Name2);
  }
  return false;
}

/// This represents the cxa_allocate_exception instruction.
class LLVM_LIBRARY_VISIBILITY CxaAllocateExceptionInst : public CallInst {
  enum { Size };

public:
  Constant *getSize() const {
    // TODO: decide on undef.
    return cast<Constant>(getArgOperand(Size));
  }

  // Methods to support type inquiry through isa, cast, and dyn_cast:
  static bool classof(const CallInst *I) {
    return CheckFnName(I, "__cxa_allocate_exception");
  }
  static bool classof(const Value *V) {
    return isa<CallInst>(V) && classof(cast<CallInst>(V));
  }
};

/// This represents the __cxa_begin_catch instruction.
class LLVM_LIBRARY_VISIBILITY CxaBeginCatch : public CallInst {
public:
  // Try to find the landingpad for which this begin belongs in a simple case
  // without memory stores or phi nodes interfering.
  LandingPadInst *tryGetLandingPad() const {
    if (auto *EI = dyn_cast<ExtractValueInst>(getArgOperand(0)))
      return dyn_cast_or_null<LandingPadInst>(EI->getAggregateOperand());
    return nullptr;
  }

  // Methods to support type inquiry through isa, cast, and dyn_cast:
  static bool classof(const CallInst *I) {
    if (auto *CalledF = I->getCalledFunction())
      if (CalledF->getName() == "__cxa_begin_catch")
        return true;
    return false;
  }
  static bool classof(const Value *V) {
    return isa<CallInst>(V) && classof(cast<CallInst>(V));
  }
};

/// This represents the __cxa_throw instruction.
class LLVM_LIBRARY_VISIBILITY CxaThrowInst : public InvokeInst {
  enum { ExceptionObject, TypeInfo, Destructor };

public:
  Value *getRawExceptionObject() const {
    return getArgOperand(ExceptionObject);
  }

  CxaAllocateExceptionInst *getExceptionObject() const {
    // TODO: decide on undef.
    return cast<CxaAllocateExceptionInst>(getRawExceptionObject());
  }

  Function *getDestructor() const {
    auto *Raw = getArgOperand(Destructor);
    if (auto *TI = dyn_cast<Constant>(Raw))
      if (auto *Fn = dyn_cast<Function>(TI->stripPointerCasts()))
        return Fn;

    return nullptr;
  }

  Constant *getTypeInfo() const {
    if (auto *TI = dyn_cast<Constant>(getArgOperand(TypeInfo)))
      return TI->stripPointerCasts();
    return nullptr;
  }

  // Methods to support type inquiry through isa, cast, and dyn_cast:
  static bool classof(const InvokeInst *I) {
    return CheckFnName(I, "__cxa_throw");
  }
  static bool classof(const Value *V) {
    return isa<InvokeInst>(V) && classof(cast<InvokeInst>(V));
  }
};

/// This represents the llvm.eh.typeid.for instruction.
class LLVM_LIBRARY_VISIBILITY EhTypeidForInst : public IntrinsicInst {
  enum { TypeInfo };

public:
  Constant *getTypeInfo() const {
    if (auto *TI = dyn_cast<Constant>(getArgOperand(TypeInfo)))
      return TI->stripPointerCasts();
    return nullptr;
  }

  // Methods to support type inquiry through isa, cast, and dyn_cast:
  static bool classof(const IntrinsicInst *I) {
    return I->getIntrinsicID() == Intrinsic::eh_typeid_for;
  }
  static bool classof(const Value *V) {
    return isa<IntrinsicInst>(V) && classof(cast<IntrinsicInst>(V));
  }
};

// The cxa_allocate_exceptions can be shared between several throw instructions.
// While a sophisticated analysis can gracefully split them among different
// users, for now, if we have a throw candidate that shares its exception
// memory with some other throw that is not being shortcicuited, remove it
// from the list of candidates.

struct BlockColor {
  std::bitset<2> Colors;
  int Nesting = -1;

  bool contains(std::bitset<2> Val) const {
    Val &= ~Colors;
    return Val.none();
  }

  std::string getName() const {
    std::string result;
    if (Colors[0])
      result.push_back('0');
    if (Colors[1])
      result.push_back('1');
    return result;
  }

  bool wontShortcircuitUnknownFunction() const {
    return Colors[0] && Nesting == 0;
  }
};

enum { TYPEID_INDEX = 1 };

static bool handleShortCircuitBranch(BranchInst *Br, LandingPadInst *LP,
                                     Constant *TypeInfo) {
  if (Br->isUnconditional())
    return false;

  BasicBlock *TrueSucc = Br->getSuccessor(0);
  BasicBlock *FalseSucc = Br->getSuccessor(1);
  // Avoid multiple edges early.
  if (TrueSucc == FalseSucc)
    return false;

  auto *Cmp = dyn_cast<ICmpInst>(Br->getCondition());
  if (!Cmp || !Cmp->isEquality())
    return false;

  if (Cmp->getPredicate() == ICmpInst::ICMP_NE)
    std::swap(TrueSucc, FalseSucc);

  Value *LHS = Cmp->getOperand(0);
  Value *RHS = Cmp->getOperand(1);

  auto *TypeIdInst = dyn_cast<EhTypeidForInst>(RHS);
  if (!TypeIdInst) {
    std::swap(LHS, RHS);
    TypeIdInst = dyn_cast<EhTypeidForInst>(RHS);
    if (!TypeIdInst)
      return false;
  }

  if (TypeIdInst->getTypeInfo() != TypeInfo)
    return false;

  // Verify that LHS is an extract instruction asking for the passed in LPad.
  if (auto EI = dyn_cast<ExtractValueInst>(LHS))
    if (EI->getAggregateOperand() == LP)
      if (EI->getNumIndices() == 1)
        if (*EI->idx_begin() == TYPEID_INDEX) {
          dbgs() << "GOOD BRANCH: " << TrueSucc->getName() << "\n";
          return true;
        }

  return false;
}

static void simplifyCompare(ICmpInst *Cmp) {
  // Compare should look like this:
  //
  //     %27 = tail call i32 @llvm.eh.typeid.for(i8* bitcast ({ i8*, i8* }*
  //     @_ZTI6cancel to i8*)) #7 %matches.sc2 = icmp eq i32 %7, %27 br i1
  //     %matches.sc2, label %catch9.sc16, label %unreachable
  //
  //  Replace with:
  //
  //     br i1 true, label %catch9.sc16, label %unreachable

  auto *TypeIdInst = dyn_cast<EhTypeidForInst>(Cmp->getOperand(0));
  if (!TypeIdInst) {
    // Already confirmed this when checking eligibility.
    TypeIdInst = cast<EhTypeidForInst>(Cmp->getOperand(1));
  }

  auto *True = ConstantInt::getTrue(Cmp->getContext());
  Cmp->replaceAllUsesWith(True);
  Cmp->eraseFromParent();

  if (TypeIdInst->use_empty())
    TypeIdInst->eraseFromParent();
}

static void addDestructorCall(CallInst *End, Value *BeginCatchReplacement,
                              Function *Dtor) {
  FunctionType *FnTy = Dtor->getFunctionType();
  if (FnTy->getNumParams() != 1)
    report_fatal_error("unexpcted number of args to a destructor call");

  Type *ParamTy = FnTy->getParamType(0);
  if (ParamTy != BeginCatchReplacement->getType())
    BeginCatchReplacement =
        new BitCastInst(BeginCatchReplacement, ParamTy, "", End);

  CallInst::Create(FnTy, Dtor, BeginCatchReplacement, "", End);
}

static bool updateThrows(ValueToValueMapTy &VMap, LandingPadInst *OrigLP,
                         SmallVectorImpl<CallInst *> const &OrigCatchEnds,
                         SmallPtrSetImpl<CxaThrowInst *> &Throws) {
  auto *const LP = cast<LandingPadInst>(VMap[OrigLP]);

  // Replace all __cxa_allocate_exception with Alloca
  Function &F = *LP->getParent()->getParent();
  const DataLayout &DL = F.getParent()->getDataLayout();
  auto &EntryBlock = F.getEntryBlock();

  Function *Dtor = (*Throws.begin())->getDestructor();
  if (Dtor)
    Dtor->dump();

  // In case we have more than one alloca, we will need to create a phi
  // node joining allocas from multiple throws. Remember them here.
  SmallVector<std::pair<AllocaInst *, BasicBlock *>, 1> ThrowEdgesWithAllocas;

  for (CxaThrowInst *Th : Throws) {
    auto *AI = dyn_cast<AllocaInst>(Th->getRawExceptionObject());
    if (!AI) {
      CxaAllocateExceptionInst *EO = Th->getExceptionObject();
      AI = new AllocaInst(Type::getInt8Ty(LP->getContext()),
                          DL.getAllocaAddrSpace(), EO->getSize(), "",
                          &EntryBlock.front());
      AI->takeName(EO);
      EO->replaceAllUsesWith(AI);
      EO->eraseFromParent();
    }

    BranchInst::Create(LP->getParent(), Th);

    ThrowEdgesWithAllocas.emplace_back(AI, Th->getParent());
    Th->eraseFromParent();
  }

  // Optimistically assume that we only have one edge.
  Value *BeginCatchReplacement = ThrowEdgesWithAllocas.front().first;
  const auto IncomingEdges = ThrowEdgesWithAllocas.size();
  if (IncomingEdges > 1) {
    // Otherwise, create a Phi instruction.
    auto *PN = PHINode::Create(BeginCatchReplacement->getType(), IncomingEdges,
                               "", &LP->getParent()->front());
    for (auto Edge : ThrowEdgesWithAllocas)
      PN->addIncoming(Edge.first, Edge.second);

    BeginCatchReplacement = PN;
  }

  // Classify all users of LPAD
  // 1. resume => should be undef, since it will be on dead branches
  // 2. extractvalue 0 and extractvalue 1, classify those independently

  TinyPtrVector<CxaBeginCatch *> Catches;
  TinyPtrVector<ICmpInst *> Compares;

  for (const auto &User : LP->users()) {
    User->dump();
    if (auto *EI = dyn_cast<ExtractValueInst>(User)) {
      if (EI->getNumIndices() != 1)
        return false;

      const auto Index = *EI->idx_begin();
      if (Index == 0) {
        for (const auto &User : EI->users())
          if (auto *BegCatch = dyn_cast<CxaBeginCatch>(User))
            Catches.push_back(BegCatch);
          else {
            dbgs() << "UNEXPECTED USER OF ExceptionObject: ";
            User->dump();
            return false;
          }
      } else if (Index == 1) {
        for (const auto &User : EI->users())
          // Should be ICmp
          if (auto *Cmp = dyn_cast<ICmpInst>(User))
            Compares.push_back(Cmp);
          else {
            dbgs() << "UNEXPECTED USER OF TypeInfo: ";
            User->dump();
            return false;
          }
      } else {
        dbgs() << "UNEXPECTED Index when unpacking Lpad result: ";
        EI->dump();
        return false;
      }
    } else if (!isa<ResumeInst>(User)) {
      // Unexpected user. Don't know what to do with it.
      dbgs() << "UNEXPECTED USER OF LPAD: ";
      User->dump();
      return false;
    }
  }

  // When we were duplicating, we should have already
  // clone only the blocks related to the exception
  // being shortcicuited. We expect to see only one
  // icmp and one catch.

  if (Compares.size() != 1 || Catches.size() != 1) {
    dbgs() << "UNEXPECTED NUMBER OF Icmps " << Compares.size()
           << " and Catches " << Catches.size() << "\n";
    return false;
  }

  for (auto *Catch : Catches) {
    Catch->replaceAllUsesWith(BeginCatchReplacement);
    Catch->eraseFromParent();
  }

  for (auto *OrigEnd : OrigCatchEnds) {
    // If catch belongs to the shortcicuit type, it will be cloned, if so,
    // VMap will have a mapping for it.
    if (auto *End = cast_or_null<CallInst>(VMap[OrigEnd])) {
      if (Dtor)
        addDestructorCall(End, BeginCatchReplacement, Dtor);
      // TODO: Add dtor call.
      End->eraseFromParent();
    }
  }

  for (auto *Compare : Compares)
    simplifyCompare(Compare);

  // TODO: Be smarter and cleanup all of the users.
  // Replace LandingPad with undef and remove it.
  auto *Undef = UndefValue::get(LP->getType());
  LP->replaceAllUsesWith(Undef);
  LP->eraseFromParent();

  return true;
}

static void trimUsersIfNotAllEligibleForShortCircuit(
    CxaAllocateExceptionInst *EhAlloc,
    SmallPtrSetImpl<CxaThrowInst *> &Throws) {

  bool AllThrowsEligible = true;
  for (const auto &User : EhAlloc->users())
    if (auto *Throw = dyn_cast<CxaThrowInst>(User))
      if (Throws.count(Throw) == 0) {
        AllThrowsEligible = false;
        break;
      }

  if (AllThrowsEligible)
    return;

  dbgs() << "Found ineligible cxa_allocate_exception: ";
  EhAlloc->dump();

  // TODO: Add erase_if for the set.
  SmallVector<CxaThrowInst *, 4> RemoveCandidates;
  for (auto *TI : Throws)
    if (TI->getExceptionObject() == EhAlloc)
      RemoveCandidates.push_back(TI);

  for (auto *TI : RemoveCandidates) {
    dbgs() << "REMOVE: ";
    TI->dump();
    Throws.erase(TI);
  }
}

static bool examineBlocksAndSimplify(LandingPadInst *LP) {
  DenseMap<BasicBlock *, BlockColor> BlockColors;
  SmallVector<std::pair<BasicBlock *, BlockColor>, 16> Worklist;
  SmallVector<CallInst *, 4> CatchEnds;
  SmallVector<InvokeInst *, 4> CatchEndInvokes;
  bool UnknownFunctionInCleanup = false;

  // Candidate LP must have at least one clause.
  Constant *TypeInfo = LP->getClause(0)->stripPointerCasts();

  BasicBlock *InitialBlock = LP->getParent();
  BlockColor InitialColor;
  InitialColor.Colors.set(0);
  if (!InitialBlock->getSinglePredecessor()) {
    InitialColor.Colors.set(1);
  }
  InitialColor.Nesting = 0;

  Worklist.push_back({InitialBlock, InitialColor});

  while (!Worklist.empty()) {
    BasicBlock *Visiting;
    BlockColor Color;
    std::tie(Visiting, Color) = Worklist.pop_back_val();

    // TODO: add DEBUG_WITH_TYPE
    dbgs() << "Visiting " << Visiting->getName() << " " << Color.getName()
           << " nest: " << Color.Nesting << "\n";

    BlockColor &Colors = BlockColors[Visiting];
    dbgs() << "Old color " << Colors.getName() << " nest: " << Colors.Nesting
           << "\n";
    if (Colors.Nesting != -1)
      assert(Colors.Nesting == Color.Nesting && "Nesting Must Match");

    if (Colors.contains(Color.Colors)) {
      dbgs() << "SKIPPING. No color change\n";
      continue;
    }
    Colors.Colors |= Color.Colors;

    // TODO: add DEBUG_WITH_TYPE
    dbgs() << "Assigned new color " << Colors.getName() << "\n";

    Instruction *Current = Visiting->getFirstNonPHIOrDbgOrLifetime();
    while (!Current->isTerminator()) {
      if (isa<LandingPadInst>(Current))
        ++Color.Nesting;
      else if (isa<IntrinsicInst>(Current))
        ; // assume intrinsics are safe
      else if (auto *CI = dyn_cast<CallInst>(Current)) {
        if (CheckFnName(CI, "__cxa_begin_catch")) {
          assert(Color.Nesting > 0 && "unexpected nesting");
          --Color.Nesting;
        } else if (CheckFnName(CI, "__cxa_end_catch")) {
          ++Color.Nesting;
          if (Color.Nesting == 1) {
            CatchEnds.push_back(CI);
            goto pull_next_block;
          }
        } else if (CheckFnName(CI, "__clang_call_terminate"))
          ; // Do Nothing (Yet), but we may take advantage of this later.

        // If we encounter an unknown function in the catch, don't shortcircuit
        // for now.
        else if (Color.wontShortcircuitUnknownFunction())
          return false;
        else
          UnknownFunctionInCleanup = true;
      }
      Current = Current->getNextNode();
    }

    if (auto *Inv = dyn_cast<InvokeInst>(Current)) {
      if (CheckFnName(Inv, "__cxa_end_catch")) {
        ++Color.Nesting;
        if (Color.Nesting == 1)
          CatchEndInvokes.push_back(Inv);
        else
          --Color.Nesting;
      }
      // If we encounter an unknown function in the catch, don't shortcircuit
      // for now.
      else if (Color.wontShortcircuitUnknownFunction())
        return false;
      else
        UnknownFunctionInCleanup = true;
    } else if (Color.Nesting == 1) {
      if (auto *Br = dyn_cast<BranchInst>(Current))
        if (handleShortCircuitBranch(Br, LP, TypeInfo)) {
          // For now assume it is always the left branch.
          auto ColorLeft = Color;
          auto ColorRight = Color;
          ColorLeft.Colors.reset(1);
          ColorRight.Colors.reset(0);
          Worklist.push_back({Br->getSuccessor(0), ColorLeft});
          Worklist.push_back({Br->getSuccessor(1), ColorRight});
          continue;
        }
    }
    for (BasicBlock *Succ : successors(Visiting))
      Worklist.push_back({Succ, Color});
  pull_next_block:;
  }

  dbgs() << "-----------------------------------------\n";

  for (auto const &Entry : BlockColors) {
    BasicBlock *Visiting;
    BlockColor Color;
    std::tie(Visiting, Color) = Entry;

    // TODO: add DEBUG_WITH_TYPE
    dbgs() << "Block \"" << Visiting->getName() << "\" => " << Color.getName()
           << " nest: " << Color.Nesting << "\n";
  }

  // DO THE WORK

  // Find all the throws.
  SmallPtrSet<CxaThrowInst *, 4> Throws;
  SmallPtrSet<CxaAllocateExceptionInst *, 4> EhAllocs;

  for (BasicBlock *Pred : predecessors(LP->getParent()))
    if (auto *Throw = dyn_cast<CxaThrowInst>(Pred->getTerminator()))
      if (TypeInfo == Throw->getTypeInfo()) {
        Throws.insert(Throw);
        EhAllocs.insert(Throw->getExceptionObject());
      }

  if (Throws.empty())
    return false;

  // Check that none of the referred allocas have throws that are not in the
  // list of the ones being short-circuited.

  for (CxaAllocateExceptionInst *EhAlloc : EhAllocs)
    trimUsersIfNotAllEligibleForShortCircuit(EhAlloc, Throws);

  if (Throws.empty())
    return false;

  // TODO: If EndCatch blocks are shared and there are more instructions after
  // the end.catch besides terminator. Split the end catch block.

  BasicBlock *UnreachBB = (*Throws.begin())->getNormalDest();

  // TODO: Do not duplicate if there is no other throw edges of different types.
  // Need to duplicate all of the blocks that has 0 in them.
  ValueToValueMapTy VMap;
  std::vector<std::pair<BasicBlock *, BasicBlock *>> Orig2Clone;
  for (auto const &Entry : BlockColors) {
    BasicBlock *BB;
    BlockColor Color;
    std::tie(BB, Color) = Entry;

    if (!Color.Colors[0]) {
      VMap[BB] = UnreachBB;
      continue;
    }

    BasicBlock *CBB = CloneBasicBlock(BB, VMap, ".sc");
    CBB->insertInto(BB->getParent(), BB->getNextNode());
    VMap[BB] = CBB;
    Orig2Clone.emplace_back(BB, CBB);
  }

  for (auto &Entry : Orig2Clone) {
    for (Instruction &I : *Entry.second)
      RemapInstruction(&I, VMap,
                       RF_IgnoreMissingLocals | RF_NoModuleLevelChanges);
  }

  return updateThrows(VMap, LP, CatchEnds, Throws);
}

static LandingPadInst *isShortCircuitCandidate(BasicBlock &BB) {
  // It is a throw instruction.
  auto *Throw = dyn_cast<CxaThrowInst>(BB.getTerminator());
  if (!Throw)
    return nullptr;

  // It unwinds into a landing pad.
  auto *Lpad = Throw->getUnwindDest()->getLandingPadInst();
  if (!Lpad)
    return nullptr;

  // The type being thrown is the first type in the catch clause.
  if (Lpad->getNumClauses() == 0 || !Lpad->isCatch(0))
    return nullptr;

  Constant *CatchClause = Lpad->getClause(0);
  Constant *CatchTypeInfo = CatchClause->stripPointerCasts();

  auto *ThrowTypeInfo = Throw->getTypeInfo();
  if (ThrowTypeInfo != CatchTypeInfo)
    return nullptr;

  return Lpad;
}

////////////////////////////////////////////////////////////////////////////
// Implementation of a simple exception_pointer shortcircuiting.

static bool isEptrRethrow(const CallBase *I) {
  return CheckFnNames(
      I, "_ZSt17rethrow_exceptionNSt15__exception_ptr13exception_ptrE", // gcc
      "_ZSt17rethrow_exceptionSt13exception_ptr"); // libcxx
}
static bool isEptrCopyCtor(const CallBase *I) {
  return CheckFnNames(I, "_ZNSt15__exception_ptr13exception_ptrC1ERKS0_",
                      "_ZNSt13exception_ptrC1ERKS_");
}
static bool isEptrDtor(const CallBase *I) {
  return CheckFnNames(I, "_ZNSt15__exception_ptr13exception_ptrD1Ev",
                      "_ZNSt13exception_ptrD1Ev");
}
static bool isCurrentEptr(const CallBase *I) {
  return CheckFnName(I, "_ZSt17current_exceptionv");
}

/// This represents rethrow_exception(eptr) instruction.
class LLVM_LIBRARY_VISIBILITY EptrRethrowInst : public InvokeInst {
public:
  AllocaInst *getExceptionAlloca() const {
    return dyn_cast<AllocaInst>(getArgOperand(0));
  }
  // Methods to support type inquiry through isa, cast, and dyn_cast:
  static bool classof(const InvokeInst *I) { return isEptrRethrow(I); }
  static bool classof(const Value *V) {
    return isa<InvokeInst>(V) && classof(cast<InvokeInst>(V));
  }
};

static EptrRethrowInst *isEptrShortCircuitCandidate(BasicBlock &BB) {
  // It is a throw instruction.
  auto *Rethrow = dyn_cast<EptrRethrowInst>(BB.getTerminator());
  if (!Rethrow)
    return nullptr;

  // It unwinds into a landing pad.
  auto *Lpad = Rethrow->getUnwindDest()->getLandingPadInst();
  if (!Lpad)
    return nullptr;

  // It has to have exactly one catch clause.
  if (Lpad->getNumClauses() != 1 || !Lpad->isCatch(0))
    return nullptr;

  // It must be catch(...).
  Constant *CatchClause = Lpad->getClause(0);
  if (!isa<ConstantPointerNull>(CatchClause))
    return nullptr;

  // For simplicity, only consider single predecessor landing pads.
  auto *LandingPadBB = Lpad->getParent();
  if (LandingPadBB->getSinglePredecessor())
    return Rethrow;

  return nullptr;
}

namespace {
struct EptrRethrowOptimizer {
  EptrRethrowInst *Rethrow = nullptr;
  AllocaInst *EptrAlloca = nullptr;
  CallInst *EptrCopyCtor = nullptr;
  CallInst *EptrDtor = nullptr;
  LandingPadInst *LandingPad = nullptr;
  CallInst *CxaBegin = nullptr;
  CallInst *CxaEnd = nullptr;
  CallInst *CurrentEptr = nullptr;

  EptrRethrowOptimizer(EptrRethrowInst *R)
      : Rethrow(R), EptrAlloca(R->getExceptionAlloca()) {
    if (EptrAlloca)
      if ((EptrCopyCtor = getCopyCtor(EptrAlloca)))
        if ((LandingPad = Rethrow->getUnwindDest()->getLandingPadInst()))
          if (getTheRestFromLandingPad())
            return;

    Rethrow = nullptr;
  }

  explicit operator bool() const { return Rethrow; }

  static bool onlyUsedByLifetimeIntrinsics(BitCastInst *BC) {
    for (const auto &User : BC->users()) {
      if (auto *I = dyn_cast<Instruction>(User))
        if (I->isLifetimeStartOrEnd())
          continue;

      return false;
    }
    return true;
  }

  static CallInst *getCopyCtor(AllocaInst *AI) {
    int UserCount = 0;
    CallInst *CopyCtor = nullptr;
    for (const auto &User : AI->users()) {
      User->dump();
      ++UserCount;
      if (auto *CI = dyn_cast<CallInst>(User)) {
        if (isEptrCopyCtor(CI))
          CopyCtor = CI;
      } else if (auto *BC = dyn_cast<BitCastInst>(User)) {
        if (onlyUsedByLifetimeIntrinsics(BC))
          --UserCount; // Don't count it as use.
      }
    }
    // Should only be used by rethrow, copyctor and dtor.
    if (UserCount == 3)
      return CopyCtor;

    return nullptr;
  }

  static void RemoveAndReplaceWithUndef(Instruction *I) {
    I->replaceAllUsesWith(UndefValue::get(I->getType()));
    I->eraseFromParent();
  }

  bool tryOptimize() {
    ///////////////////////////////////////////////////////////////////////////
    //
    //  Transforms (conceptually):
    //
    //       copy = COPY_EPTR(src)
    //       RETHROW(copy) into LPAD
    //
    //       CATCH(...)
    //       <cleanup>
    //       DTOR(copy)
    //       dst = CURRENT_EPTR()
    //
    //   into (if lifetime of src allows):
    //
    //       <cleanup>
    //       dst = COPY_EPTR(src)
    //
    //   or into
    //
    //       copy = COPY_EPTR(src)
    //       <cleanup>
    //       dst = COPY_EPTR(copy)
    //       DTOR(copy)

    // Grab destination from: dst = CURRENT_EPTR().
    Value *Dst = CurrentEptr->getArgOperand(0);

    // Move CopyCtor just before CurrentException and replace destnation.
    EptrCopyCtor->moveBefore(CurrentEptr);
    EptrCopyCtor->setArgOperand(0, Dst);

    // Replace RethrowInvoke with regular branch.
    BranchInst::Create(LandingPad->getParent(), Rethrow);

    // Remove the rest of the instructions.
    RemoveAndReplaceWithUndef(Rethrow);
    RemoveAndReplaceWithUndef(LandingPad);
    RemoveAndReplaceWithUndef(EptrDtor);
    RemoveAndReplaceWithUndef(CurrentEptr);
    RemoveAndReplaceWithUndef(CxaBegin);
    RemoveAndReplaceWithUndef(CxaEnd);
    return true;
  }

  bool getTheRestFromLandingPad() {
    // The rest of the interesting instructions are in the LandingPadBlock
    // between the LandingPadInst and the CxaCatchEnd.
    for (Instruction *Current = LandingPad->getNextNode();
         !Current->isTerminator();
         Current = Current->getNextNode()) {
      if (auto *CI = dyn_cast<CallInst>(Current)) {
        if (isEptrDtor(CI)) {
          // It must be the one referring to the EptrAlloca that is being
          // rethrown and we have not seen this dtor before.
          if (CI->getArgOperand(0) == EptrAlloca && !EptrDtor) {
            EptrDtor = CI;
            continue;
          }
        } else if (auto BC = dyn_cast<CxaBeginCatch>(CI)) {
          // It must belong to our lpad and we should not have seen another one.
          if (BC->tryGetLandingPad() == LandingPad && !CxaBegin) {
            CxaBegin = BC;
            continue;
          }
        } else if (isCurrentEptr(CI) && !CurrentEptr) {
          CurrentEptr = CI;
          continue;
        } else if (CheckFnName(CI, "__cxa_end_catch") && !CxaEnd) {
          CxaEnd = CI;
          break;
        }
        // If any other call found or other checks failed, we are not in the
        // simple case. Bail out.
        return false;
      }
    }

    // Found all.
    if (EptrDtor && CxaBegin && CxaEnd && CurrentEptr)
      return true;

    return false;
  }
};
} // namespace

static bool simplifyGNU_CXX(Function &F) {
  bool anyChanges = false;
  SmallPtrSet<LandingPadInst *, 4> SimplificationCandidates;
  SmallVector<EptrRethrowInst *, 1> EptrSimplificationCandidates;

  for (auto &BB : F)
    if (LandingPadInst *LP = isShortCircuitCandidate(BB))
      SimplificationCandidates.insert(LP);
    else if (auto *EptrRethrow = isEptrShortCircuitCandidate(BB))
      EptrSimplificationCandidates.push_back(EptrRethrow);

  for (auto *Rethrow : EptrSimplificationCandidates)
    if (EptrRethrowOptimizer opt{Rethrow})
      anyChanges |= opt.tryOptimize();

  for (auto *LP : SimplificationCandidates)
    anyChanges |= examineBlocksAndSimplify(LP);

  return anyChanges;
}

//===----------------------------------------------------------------------===//
//                              Top Level Driver
//===----------------------------------------------------------------------===//

namespace {

struct CXXSimplifyEH : public FunctionPass {
  static char ID; // Pass identification, replacement for typeid.
  CXXSimplifyEH() : FunctionPass(ID) {
    initializeCXXSimplifyEHPass(*PassRegistry::getPassRegistry());
  }

  bool runOnFunction(Function &F) override {
    if (!F.hasPersonalityFn())
      return false;

    auto Personality = classifyEHPersonality(F.getPersonalityFn());
    if (Personality == EHPersonality::GNU_CXX)
      return simplifyGNU_CXX(F);

    return false;
  }

  StringRef getPassName() const override { return "Simplify C++ EH patterns"; }
};
} // namespace

char CXXSimplifyEH::ID = 0;
INITIALIZE_PASS(CXXSimplifyEH, "cxx-simplify-eh", "Simplify C++ EH patterns",
                false, false)

FunctionPass *llvm::createCXXExceptionSimplificationPass() {
  return new CXXSimplifyEH();
}
