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
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Pass.h"
#include "llvm/Transforms/Scalar.h"

using namespace llvm;
using namespace llvm::coro;

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

bool Lowerer::lowerRemainingCoroIntrinsics(Function &F) {
  bool Changed = false;

  SmallPtrSet<CoroIdInst*, 2> CoroIds;
  for (auto &I: instructions(F))
    if (auto *CID = dyn_cast<CoroIdInst>(&I))
      CoroIds.insert(CID);

  for (auto *CID: CoroIds)
    lowerGetAddrFromBeg(cast<CoroIdInst>(CID));

  for (auto *CID: CoroIds) {
    CID->replaceAllUsesWith(ConstantTokenNone::get(Context));
    CID->eraseFromParent();
    Changed = true;
  }

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
      case Intrinsic::coro_subfn_addr:
        lowerSubFn(Builder, cast<CoroSubFnInst>(II));
        break;
      case Intrinsic::coro_cc_addr:
        lowerGetCcAddr(Builder, II);
        break;
      case Intrinsic::coro_rinline_request:
        // Just remove this one.
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
    if (coro::declaresIntrinsics(
            M, {"llvm.coro.alloc", "llvm.coro.begin", "llvm.coro.subfn.addr",
                "llvm.coro.free", "llvm.coro.id", "llvm.coro.rinline.request",
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
