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

using namespace llvm;

#define DEBUG_TYPE "cxx-eh-simplify"

static bool CheckFnName(const CallBase *I, StringRef Name) {
  if (auto *CalledF = I->getCalledFunction())
    if (CalledF->getName() == Name)
      return true;
  return false;
}

/// This represents the __cxa_throw instruction.
class LLVM_LIBRARY_VISIBILITY CxaThrowInst : public InvokeInst {
  enum { ExceptionObject, TypeInfo, Destructor };

public:
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

struct BlockColor {
  std::bitset<2> Colors{1};
  unsigned Nesting = 0;

  std::string getName() {
    std::string result;
    if (Colors[0]) result.push_back('0');
    if (Colors[1]) result.push_back('1');
    return result;
  }
};

enum {TYPEID_INDEX = 1};

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

bool examineBlocks(LandingPadInst* LP, Constant* TypeInfo) {
  DenseMap<BasicBlock *, BlockColor> Colors;
  SmallVector<std::pair<BasicBlock*, BlockColor>, 16> Worklist;
  SmallVector<CallInst *, 4> CatchEnds;
  SmallVector<InvokeInst *, 4> CatchEndInvokes;
  bool UnknownFunctionInCleanup = false;

  BasicBlock *InitialBlock = LP->getParent();
  BlockColor InitialColor;
  if (!InitialBlock->getSinglePredecessor()) {
    InitialColor.Colors.set(1);
  }

  Worklist.push_back({InitialBlock, InitialColor});

  while (!Worklist.empty()) {
    BasicBlock *Visiting;
    BlockColor Color;
    std::tie(Visiting, Color) = Worklist.pop_back_val();

    // TODO: add DEBUG_WITH_TYPE
    dbgs() << "Visiting " << Visiting->getName() << " " << Color.getName()
           << " nest: " << Color.Nesting << "\n";

    Instruction *Current = Visiting->getFirstNonPHIOrDbgOrLifetime();
    while (!Current->isTerminator()) {
      if (isa<IntrinsicInst>(Current))
        ; // assume intrinsics are safe
      else if (auto *CI = dyn_cast<CallInst>(Current)) {
        if (CheckFnName(CI, "__cxa_end_catch")) {
          if (Color.Nesting == 0) {
            CatchEnds.push_back(CI);
            Current = Visiting->getTerminator();
            break; // need to go to next block
          }
          else
            --Color.Nesting;
        }
        else if (CheckFnName(CI, "__clang_call_terminate"))
          ; // Do Nothing (Yet), but we may take advantage of this later.

        // If we encounter an unknown function in the catch, don't shortcircuit
        // for now.
        else if (Color.Nesting == 0)
          return false;
        else
          UnknownFunctionInCleanup = true;
      }
      Current = Current->getNextNode();
    }
    if (auto *Inv = dyn_cast<InvokeInst>(Current)) {
        if (CheckFnName(Inv, "__cxa_end_catch")) {
          if (Color.Nesting == 0)
            CatchEndInvokes.push_back(Inv);
          else
            --Color.Nesting;
        }
        // If we encounter an unknown function in the catch, don't shortcircuit
        // for now.
        else if (Color.Nesting == 0)
          return false;
        else
          UnknownFunctionInCleanup = true;
    }
    else if (Color.Nesting == 0) {
      if (auto *Br = dyn_cast<BranchInst>(Current))
        if (handleShortCircuitBranch(Br, LP, TypeInfo))
          ;
    }

  }

  return true;
}

namespace {

struct ShortCircuitThrowWorker {
  LandingPadInst *LandingPad;
  TinyPtrVector<CxaThrowInst*> Throws;
  Constant *TypeInfo;

  ShortCircuitThrowWorker() {}
  ShortCircuitThrowWorker(ShortCircuitThrowWorker const&) = delete;

  bool isShortCircuitCandidate(BasicBlock &BB) {
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

    this->TypeInfo = ThrowTypeInfo;
    this->LandingPad = Lpad;
    return true;
  }

  bool trySimplify(BasicBlock &BB) {
    if (isShortCircuitCandidate(BB)) {
      if (examineBlocks(LandingPad, TypeInfo))
        return true;
    }

    return false;
  }


};
}

bool trySimplify(CxaThrowInst *) { return nullptr; }
/// This represents the __cxa_throw instruction.
class LLVM_LIBRARY_VISIBILITY CxaBeginCatch : public CallInst {
public:
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

// TODO: Fix comment:
// At the moment, C++ exception simplification is limited to removal of try
// catch in the following pattern:  try { whatever } catch(...) { throw; }

// On GNU GCC EH Look for the pattern:
//
//    %4 = call i8* @__cxa_BeginCatch(i8* %3)
//    invoke void @__cxa_throw() #6 to label % unreachable unwind label %lpad1
//
//  lpad1:;
//    landingpad{i8 *, i32} cleanup
//    invoke void @__cxa_end_catch() to label %invoke.cont2
//
// and replace it with:
//    br %invoke.cont2

namespace {
struct ThrowSimplifier {
  CxaThrowInst *Throw;
  //  CallInst *BeginCatch;
  LandingPadInst *Lpad;
  // InvokeInst *EndCatch;

  ThrowSimplifier(ThrowSimplifier const &) = default;

  // Checks for
  //   1. Throws into a LandingPad with a single incoming edge
  //   2. LandingPad has only one catch clause that matches the type being
  //   thrown

  explicit ThrowSimplifier(BasicBlock &BB) : Throw(getThrow(BB)) {
    if (Throw)
      if ((Lpad = getLpad(Throw)))
        return;
    Throw = nullptr;
  }

  explicit operator bool() const { return Throw; }

  static CxaThrowInst *getThrow(BasicBlock &BB) {
    if (auto Inv = dyn_cast<CxaThrowInst>(BB.getTerminator()))
      return Inv;

    return nullptr;
  }

#if 0
  static CallInst *getBeginCatch(CxaThrowInst *Throw) {
    if (auto *CI = dyn_cast_or_null<CallInst>(Throw->getPrevNode()))
      if (auto *CalledFn = CI->getCalledFunction())
        if (CalledFn->getName() == "__cxa_begin_catch")
          if (CI->user_empty()) // If it has uses cannot simplify.
            return CI;

    return nullptr;
  }

  static InvokeInst *getEndCatch(LandingPadInst *Lpad) {
    if (auto *CI = dyn_cast_or_null<InvokeInst>(Lpad->getNextNode()))
      if (auto *CalledFn = CI->getCalledFunction())
        if (CalledFn->getName() == "__cxa_end_catch")
          return CI;

    return nullptr;
  }
#endif
  static LandingPadInst *getLpad(CxaThrowInst *Throw) {
    auto *Lpad = Throw->getUnwindDest()->getLandingPadInst();
    if (!Lpad)
      return nullptr;

    // TODO: Handle cases with multiple predecessor. That requires a bit of
    // work of cloning blocks so that we can separate the short-cicuit
    // handling from other exception handling.
    // This is similar to WinEHPrepare::cloneCommonBlocks and funcletColoring.
    // Possibly we can refactor the logic out of WinEHPrepare to be reusable.
    BasicBlock *BB = Lpad->getParent();
    if (!BB->getSinglePredecessor())
      return nullptr;

    // Should have exactly one case clause with the catch type matching the
    // type being thrown.
    if (Lpad->getNumClauses() != 1)
      return nullptr;

    if (!Lpad->isCatch(0))
      return nullptr;

    Constant *CatchClause = Lpad->getClause(0);
    Constant *TypeInfo = CatchClause->stripPointerCasts();
    TypeInfo->dump();

    auto *TI2 = Throw->getTypeInfo();
    TI2->dump();
    if (TI2 != TypeInfo)
      return nullptr;

    // Classify all users of LPAD
    // 1. resume => should be undef, since it will be on dead branches
    // 2. extractvalue 0 and extractvalue 1, classify those independently

    SmallVector<CxaBeginCatch *, 1> Catches;
    SmallVector<ICmpInst *, 2> Compares;

    for (const auto &User : Lpad->users()) {
      User->dump();
      if (auto *EI = dyn_cast<ExtractValueInst>(User)) {
        if (EI->getNumIndices() != 1)
          return nullptr;

        const auto Index = *EI->idx_begin();
        for (const auto &User : EI->users())
          if (Index == 0) { // Should be begin catch
            if (auto *BegCatch = dyn_cast<CxaBeginCatch>(User))
              Catches.push_back(BegCatch);
            else
              return nullptr;
          } else if (Index == 1) { // Should be ICmp
            if (auto *Cmp = dyn_cast<ICmpInst>(User))
              Compares.push_back(Cmp);
            else
              return nullptr;
          } else
            return nullptr;

      } else if (!isa<ResumeInst>(User))
        return nullptr;
    }

    // We except to have only one begin catch.
    if (Catches.size() != 1)
      return nullptr;

    // We except to have at least one compare
    if (Compares.size() != 1)
      return nullptr;

    // Now we need to make sure that there is no unknown calls
    // between begin catch and end catch.
    // Think what to do if dtor throws. LATER

    SmallVector<CallInst *, 4> CatchEnds;
    SmallVector<InvokeInst *, 4> CatchEndInvokes;

    SmallPtrSet<BasicBlock *, 4> Visited;
    SmallVector<BasicBlock *, 4> WorkList;

    Instruction *Current = Catches[0]->getNextNode();
    Visited.insert(Current->getParent());
    for (;;) {
      while (!Current->isTerminator()) {
        if (isa<IntrinsicInst>(Current))
          ; // assume intrinsics are safe
        else if (auto *CI = dyn_cast<CallInst>(Current)) {
          if (CheckFnName(CI, "__cxa_end_catch"))
            CatchEnds.push_back(CI);
          else
            return nullptr;
        }
        Current = Current->getNextNode();
      }
      // TODO: Check if magical icmp
      if (auto *II = dyn_cast<InvokeInst>(Current)) {
        if (CheckFnName(II, "__cxa_end_catch"))
          CatchEndInvokes.push_back(II);
        else
          return nullptr;
      } else {
        for (auto *Successor : successors(Current->getParent()))
          if (Visited.count(Successor) == 0)
            WorkList.push_back(Successor);
      }
      if (WorkList.empty())
        break;
      auto *NextBlock = WorkList.pop_back_val();
      Visited.insert(NextBlock);
      Current = NextBlock->getFirstNonPHIOrDbgOrLifetime();
    }

    for (auto *E : CatchEnds)
      E->dump();
    for (auto *E : CatchEndInvokes)
      E->dump();

    return Lpad;
  }

  bool simplify() {
#if 0
    auto *BB = BeginCatch->getParent();
    auto *CatchAll = BB->getLandingPadInst();
    if (!CatchAll)
      return false;

    ExtractValueInst *Extract = nullptr;
    for (Use &U : CatchAll->uses())
      if (Extract)
        return false;
      else if (auto EVI = dyn_cast<ExtractValueInst>(U.getUser()))
        Extract = EVI;
      else
        return false; // don't know how to handle this.

    BeginCatch->eraseFromParent();
    BranchInst::Create(EndCatch->getNormalDest(), Throw);
    Throw->eraseFromParent();

    auto *LpadClone = Lpad->clone();
    LpadClone->insertBefore(CatchAll);
    Lpad->replaceAllUsesWith(LpadClone);

    auto *Undef = UndefValue::get(CatchAll->getType());
    CatchAll->replaceAllUsesWith(Undef);
    CatchAll->eraseFromParent();

    if (Extract->user_empty())
      Extract->eraseFromParent();
#endif
    return true;
  }
};
} // namespace

static bool simplifyGNU_CXX(Function &F) {
  bool anyChanges = false;
  bool changed = false;
  ShortCircuitThrowWorker ShortCircuitWorker;
  do {
    for (auto &BB : F) {
      if (ShortCircuitWorker.trySimplify(BB)) {
        changed = true;
        anyChanges |= true;
        break;
      }
    }
  } while (changed);
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
