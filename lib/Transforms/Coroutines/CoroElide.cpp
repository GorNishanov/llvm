//===- CoroElide.cpp - Coroutine Frame Allocation Elision Pass ------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements coro-elide pass that replaces dynamic allocation 
// of coroutine frame with alloca and replaces calls to @llvm.coro.resume and
// @llvm.coro.destroy with direct calls to coroutine sub-functions
// see ./Coroutines.rst for details
//
//===----------------------------------------------------------------------===//

#include "CoroutineCommon.h"
#include "CoroInstr.h"
#include "llvm/Transforms/Coroutines.h"

#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/Debug.h"
using namespace llvm;

#define DEBUG_TYPE "coro-elide"

namespace {

  // TODO: paste explanation
  struct CoroElide : FunctionPass {
    static char ID;
    CoroElide() : FunctionPass(ID) {}
    bool runOnFunction(Function &F) override;
    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.addRequired<AAResultsWrapperPass>();
    }
  };

}

char CoroElide::ID = 0;
INITIALIZE_PASS_BEGIN(
    CoroElide, "coro-elide",
    "Coroutine frame allocation elision and indirect calls replacement", false,
    false)
INITIALIZE_PASS_DEPENDENCY(AAResultsWrapperPass)
INITIALIZE_PASS_END(
    CoroElide, "coro-elide",
    "Coroutine frame allocation elision and indirect calls replacement", false,
    false)

Pass *llvm::createCoroElidePass() { return new CoroElide(); }

static void replaceWithConstant(Constant *Value,
                                SmallVectorImpl<CoroSubFnInst *> &Users) {
  if (Users.empty())
    return;

  // All intrinsics in Users list should have the same type  
  auto IntrTy = Users.front()->getType();
  auto ValueTy = Value->getType();
  if (ValueTy != IntrTy) {
    assert(ValueTy->isPointerTy() && IntrTy->isPointerTy());
    Value = ConstantExpr::getBitCast(Value, IntrTy);
  }

  for (CoroSubFnInst *I : Users) {
    I->replaceAllUsesWith(Value);
    I->eraseFromParent();
  }
  
  // do constant propagation
  CoroCommon::constantFoldUsers(Value);
}

static bool operandReferences(CallSite CS, AllocaInst* Frame, AAResults& AA) {
  for (Value* Op : CS->operand_values())
    if (AA.alias(Op, Frame) != NoAlias)
      return true;
  return false;
}

static void removeTailCalls(AllocaInst* Frame, AAResults& AA) {
  Function& F = *Frame->getFunction();
  for (Instruction& I : instructions(F))
    if (auto CS = CallSite(&I))
      if (CS.isTailCall() && operandReferences(CS, Frame, AA)) {
        if (auto C = dyn_cast<CallInst>(&I))
          C->setTailCall(false);
        else if (auto Inv = dyn_cast<InvokeInst>(&I))
          C->setTailCall(false);
      }
}

static void elideHeapAllocations(CoroBeginInst *CoroBegin, Function *Resume,
                                 AAResults &AA) {
  auto ArgType = Resume->getArgumentList().front().getType();
  auto FrameTy = cast<PointerType>(ArgType)->getElementType();
  LLVMContext& C = CoroBegin->getContext();

  auto Frame = new AllocaInst(FrameTy, "");
  auto vFrame = new BitCastInst(Frame, Type::getInt8PtrTy(C), "vFrame");

  if (auto AllocInst = CoroBegin->getAlloc()) {
    vFrame->insertBefore(AllocInst);
    AllocInst->replaceAllUsesWith(vFrame);
    AllocInst->eraseFromParent();
  }
  else {
    vFrame->insertBefore(CoroBegin);
  }
  Frame->insertBefore(vFrame);

  CoroCommon::replaceCoroFree(CoroBegin, nullptr);
  CoroBegin->replaceAllUsesWith(vFrame);
  CoroBegin->eraseFromParent();

  // Since now coroutine frame lives on the stack we need to make sure that
  // any tail call referencing it, must be made non-tail call.
  removeTailCalls(Frame, AA);
}

static bool replaceIndirectCalls(CoroBeginInst *CoroBegin, AAResults& AA) {
  SmallVector<CoroSubFnInst*, 8> ResumeAddr;
  SmallVector<CoroSubFnInst*, 8> DestroyAddr;

  for (auto U : CoroBegin->users())
    if (auto II = dyn_cast<CoroSubFnInst>(U))
      (II->getIndex() == 0 ? ResumeAddr : DestroyAddr).push_back(II);

  if (ResumeAddr.empty() && DestroyAddr.empty())
    return false;

  ConstantArray* Resumers = CoroBegin->getInfo().Resumers;

  auto ResumeAddrConstant = ConstantFolder().CreateExtractValue(Resumers, 0);
  auto CleanupAddrConstant = ConstantFolder().CreateExtractValue(Resumers, 2);

  replaceWithConstant(ResumeAddrConstant, ResumeAddr);
  replaceWithConstant(CleanupAddrConstant, DestroyAddr);
  if (!DestroyAddr.empty())
    elideHeapAllocations(CoroBegin, cast<Function>(ResumeAddrConstant), AA);

  return true;
}

bool CoroElide::runOnFunction(Function &F) {
  bool changed = false;
  AAResults& AA = getAnalysis<AAResultsWrapperPass>().getAAResults();

  // Collect all coro inits
  SmallVector<CoroBeginInst*, 4> CoroBegins;
  for (auto& I : instructions(F))
    if (auto CB = dyn_cast<CoroBeginInst>(&I))
      if (CB->getInfo().postSplit())
        CoroBegins.push_back(CB);

  for (auto CB : CoroBegins)
    changed |= replaceIndirectCalls(CB, AA);

  return changed;
}
