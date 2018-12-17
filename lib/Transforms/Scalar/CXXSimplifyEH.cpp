//===- CXXSimplifyEH.cpp - Code to simplify C++ EH patterns -------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===--------------------------------------------------------------===//

#include "llvm/Analysis/EHPersonalities.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/circular_raw_ostream.h"

using namespace llvm;

#define DEBUG_TYPE "cxx-eh-simplify"

// At the moment, C++ exception simplification is limited to removal of try catch
// in the following pattern:  try { whatever } catch(...) { throw; }

// On GNU GCC EH Look for the pattern:
//
//    %4 = call i8* @__cxa_BeginCatch(i8* %3)
//    invoke void @__cxa_rethrow() #6 to label % unreachable unwind label %lpad1
//
//  lpad1:;
//    landingpad{i8 *, i32} cleanup
//    invoke void @__cxa_end_catch() to label %invoke.cont2
//
// and replace it with:
//    br %invoke.cont2

namespace {
  struct RethrowSimplifier {
    InvokeInst *Rethrow;
    CallInst *BeginCatch;
    LandingPadInst *Lpad;
    InvokeInst *EndCatch;

    RethrowSimplifier(RethrowSimplifier const&) = default;

    explicit RethrowSimplifier(BasicBlock &BB)
      : Rethrow(getRethrow(BB))
    {
      if (Rethrow)
        if ((BeginCatch = getBeginCatch(Rethrow)))
          if ((Lpad = getLpad(Rethrow)))
            if ((EndCatch = getEndCatch(Lpad)))
              return;
      Rethrow = nullptr;
    }

    explicit operator bool() const { return Rethrow; }

    static InvokeInst *getRethrow(BasicBlock &BB) {
      if (auto Inv = dyn_cast<InvokeInst>(BB.getTerminator()))
        if (auto *CalledF = Inv->getCalledFunction())
          if (CalledF->getName() == "__cxa_rethrow")
            return Inv;

      return nullptr;
    }

    static CallInst *getBeginCatch(InvokeInst *Rethrow) {
      if (auto *CI = dyn_cast_or_null<CallInst>(Rethrow->getPrevNode()))
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

    static LandingPadInst *getLpad(InvokeInst *Rethrow) {
      if (auto *Lpad = Rethrow->getUnwindDest()->getLandingPadInst())
        if (Lpad->isCleanup() && Lpad->getNumClauses() == 0)
          if (Lpad->getParent()->getSinglePredecessor())
            return Lpad;

      return nullptr;
    }

    bool simplify() {
      auto *BB = BeginCatch->getParent();
      auto *CatchAll = BB->getLandingPadInst();
      if (!CatchAll)
        return false;

      ExtractValueInst *Extract = nullptr;
      for (Use &U: CatchAll->uses())
        if (Extract)
          return false;
        else if (auto EVI = dyn_cast<ExtractValueInst>(U.getUser()))
          Extract = EVI;
        else
          return false; // don't know how to handle this.

      BeginCatch->eraseFromParent();
      BranchInst::Create(EndCatch->getNormalDest(), Rethrow);
      Rethrow->eraseFromParent();

      auto *LpadClone = Lpad->clone();
      LpadClone->insertBefore(CatchAll);
      Lpad->replaceAllUsesWith(LpadClone);

      auto *Undef = UndefValue::get(CatchAll->getType());
      CatchAll->replaceAllUsesWith(Undef);
      CatchAll->eraseFromParent();

      if (Extract->user_empty())
        Extract->eraseFromParent();

      return true;
    }
  };
}

static bool simplifyGNU_CXX(Function& F) {
  SmallVector<RethrowSimplifier, 4> Rethrows;
  for (auto &BB: F)
    if (RethrowSimplifier RS{BB})
      Rethrows.push_back(RS);

  if (Rethrows.empty())
    return false;

  bool changed = false;

  for (auto &RS: Rethrows)
    changed |= RS.simplify();

  return changed;
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

  StringRef getPassName() const override {
    return "Simplify C++ EH patterns";
  }
};
}

char CXXSimplifyEH::ID = 0;
INITIALIZE_PASS(CXXSimplifyEH, "cxx-simplify-eh", "Simplify C++ EH patterns",
                false, false)

FunctionPass *llvm::createCXXExceptionSimplificationPass() { return new CXXSimplifyEH(); }


