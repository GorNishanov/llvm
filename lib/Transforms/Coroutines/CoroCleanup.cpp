//===- CoroCleanup.cpp - Coroutine Cleanup Pass ---------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
// This pass lowers all remaining coroutine intrinsics.
//===----------------------------------------------------------------------===//

#include "CoroInternal.h"
#include "llvm/Analysis/InstructionSimplify.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Pass.h"
#include "llvm/Transforms/Scalar.h"

using namespace llvm;

#define DEBUG_TYPE "coro-cleanup"

namespace {
// Created on demand if CoroCleanup pass has work to do.
struct Lowerer : coro::LowererBase {
  IRBuilder<> Builder;
  Lowerer(Module &M) : LowererBase(M), Builder(Context) {}
  bool lowerRemainingCoroIntrinsics(Function &F);
};
}

static void simplifyCFG(Function &F) {
  llvm::legacy::FunctionPassManager FPM(F.getParent());
  FPM.add(createCFGSimplificationPass());

  FPM.doInitialization();
  FPM.run(F);
  FPM.doFinalization();
}

// TODO: Make these two functions members and pull common constants into Lowerer.
static void lowerSubFn(IRBuilder<> &Builder, CoroSubFnInst *SubFn) {
  Builder.SetInsertPoint(SubFn);
  Value *FrameRaw = SubFn->getFrame();
  int Index = SubFn->getIndex();
  auto *IntPtrTy = Builder.getInt8PtrTy();

  auto *FrameTy = StructType::get(
      SubFn->getContext(), {IntPtrTy, IntPtrTy, IntPtrTy});
  PointerType *FramePtrTy = FrameTy->getPointerTo();

  Builder.SetInsertPoint(SubFn);
  auto *FramePtr = Builder.CreateBitCast(FrameRaw, FramePtrTy);
  auto *Gep = Builder.CreateConstInBoundsGEP2_32(FrameTy, FramePtr, 0, Index);
  auto *Load = Builder.CreateLoad(Gep);

  SubFn->replaceAllUsesWith(Load);
}

static void lowerGetCcAddr(IRBuilder<> &Builder, IntrinsicInst *II) {
  auto *IntPtrTy = Builder.getInt8PtrTy();
  auto *FrameTy =
      StructType::get(II->getContext(), {IntPtrTy, IntPtrTy, IntPtrTy});
  PointerType *FramePtrTy = FrameTy->getPointerTo();

  Value *FrameRaw = II->getArgOperand(0);

  Builder.SetInsertPoint(II);
  auto *FramePtr = Builder.CreateBitCast(FrameRaw, FramePtrTy);
  auto *Gep = Builder.CreateConstInBoundsGEP2_32(FrameTy, FramePtr, 0, 2);
  auto *Load = Builder.CreateLoad(Gep);

  II->replaceAllUsesWith(Load);
}

//llvm.coro.subfn.addr.from.beg

static void replaceWithConstants(Constant *Resume, Constant *Destroy,
                                SmallVectorImpl<CoroSubFromBegInst *> &Users) {
  if (Users.empty())
    return;

  // See if we need to bitcast the constant to match the type of the intrinsic
  // being replaced. Note: All coro.subfn.addr intrinsics return the same type,
  // so we only need to examine the type of the first one in the list.
  Type *IntrTy = Users.front()->getType();
  Type *ValueTy = Resume->getType();
  if (ValueTy != IntrTy) {
    // May need to tweak the function type to match the type expected at the
    // use site.
    assert(ValueTy->isPointerTy() && IntrTy->isPointerTy());
    Resume = ConstantExpr::getBitCast(Resume, IntrTy);
    Destroy = ConstantExpr::getBitCast(Destroy, IntrTy);
  }

  // Now the value type matches the type of the intrinsic. Replace them all!
  for (CoroSubFromBegInst *I : Users) {
    auto *Value = (I->getIndex() == CoroSubFromBegInst::ResumeKind::ResumeIndex)
      ? Resume : Destroy;
    replaceAndRecursivelySimplify(I, Value);
  }
}

static void lowerGetAddrFromBeg(CoroIdInst* CoroId) {
  SmallVector<CoroSubFromBegInst *, 2> SB;
  for (auto *User: CoroId->users())
    if (auto *SBI = dyn_cast<CoroSubFromBegInst>(User))
      SB.push_back(SBI);

  if (SB.empty())
    return;

  ConstantArray *Resumers = CoroId->getInfo().Resumers;
  assert(Resumers && "PostSplit coro.id Info argument must refer to an array"
                     "of coroutine subfunctions");
  auto *ResumeAddrConstant =
      ConstantExpr::getExtractValue(Resumers, CoroSubFnInst::ResumeIndex);
  auto *DestroyAddrConstant =
      ConstantExpr::getExtractValue(Resumers, CoroSubFnInst::DestroyIndex);

  replaceWithConstants(ResumeAddrConstant, DestroyAddrConstant, SB);
}

bool Lowerer::lowerRemainingCoroIntrinsics(Function &F) {
  bool Changed = false;

  for (auto IB = inst_begin(F), E = inst_end(F); IB != E;) {
    Instruction &I = *IB++;
    if (auto *II = dyn_cast<IntrinsicInst>(&I)) {
      switch (II->getIntrinsicID()) {
      default:
        continue;
      case Intrinsic::coro_begin:
        II->replaceAllUsesWith(II->getArgOperand(1));
        break;
      case Intrinsic::coro_free:
        II->replaceAllUsesWith(II->getArgOperand(1));
        break;
      case Intrinsic::coro_alloc:
        II->replaceAllUsesWith(ConstantInt::getTrue(Context));
        break;
      case Intrinsic::coro_id:
        lowerGetAddrFromBeg(cast<CoroIdInst>(II));
        II->replaceAllUsesWith(ConstantTokenNone::get(Context));
        break;
      case Intrinsic::coro_subfn_addr:
        lowerSubFn(Builder, cast<CoroSubFnInst>(II));
        break;
      case Intrinsic::coro_cc_addr:
        lowerGetCcAddr(Builder, II);
        break;
      }
      II->eraseFromParent();
      Changed = true;
    }
  }

  if (Changed) {
    // After replacement were made we can cleanup the function body a little.
    simplifyCFG(F);
  }
  return Changed;
}

//===----------------------------------------------------------------------===//
//                              Top Level Driver
//===----------------------------------------------------------------------===//

namespace {

struct CoroCleanup : FunctionPass {
  static char ID; // Pass identification, replacement for typeid

  CoroCleanup() : FunctionPass(ID) {
    initializeCoroCleanupPass(*PassRegistry::getPassRegistry());
  }

  std::unique_ptr<Lowerer> L;

  // This pass has work to do only if we find intrinsics we are going to lower
  // in the module.
  bool doInitialization(Module &M) override {
    if (coro::declaresIntrinsics(M, {"llvm.coro.alloc", "llvm.coro.begin",
                                     "llvm.coro.subfn.addr", "llvm.coro.free",
                                     "llvm.coro.id",
                                     "llvm.coro.subfn.addr.from.beg"}))
      L = llvm::make_unique<Lowerer>(M);
    return false;
  }

  bool runOnFunction(Function &F) override {
    if (L)
      return L->lowerRemainingCoroIntrinsics(F);
    return false;
  }
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    if (!L)
      AU.setPreservesAll();
  }
  StringRef getPassName() const override { return "Coroutine Cleanup"; }
};
}

char CoroCleanup::ID = 0;
INITIALIZE_PASS(CoroCleanup, "coro-cleanup",
                "Lower all coroutine related intrinsics", false, false)

Pass *llvm::createCoroCleanupPass() { return new CoroCleanup(); }
