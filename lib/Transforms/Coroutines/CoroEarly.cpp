//===- CoroEarly.cpp - Coroutine Early Function Pass ----------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// CoroEarly - FunctionPass ran at extension point EP_EarlyAsPossible
// see ./Coroutines.rst for details
//
//===----------------------------------------------------------------------===//

#include "CoroUtils.h"

#include "llvm/IR/Module.h"
#include "llvm/IR/CFG.h"
#include "llvm/Pass.h"
#include "llvm/Support/Debug.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/TinyPtrVector.h"
#include "llvm/ADT/StringSwitch.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IRBuilder.h"
#include <llvm/Transforms/Utils/BasicBlockUtils.h>

using namespace llvm;

#define DEBUG_TYPE "coro-early"

// Keeps data common to all lowering functions.
class Lowerer {
  Module& M;
  LLVMContext& C;
  IRBuilder<> Builder;
  Type* Int8Ty;
  PointerType* Int8PtrTy;

  PointerType* AnyResumeFnPtrTy;

  Lowerer(Module &M)
      : M(M), C(M.getContext()), Builder(C),
        Int8Ty(Type::getInt8Ty(C)), Int8PtrTy(Int8Ty->getPointerTo()),
        AnyResumeFnPtrTy(FunctionType::get(Type::getVoidTy(C), Int8PtrTy,
                                           /*isVarArg=*/false)
                             ->getPointerTo()) {}

  void replaceCoroPromise(IntrinsicInst *Intrin, bool from = false);
  void lowerResumeOrDestroy(IntrinsicInst* II, unsigned Index);
  void lowerCoroDone(IntrinsicInst* II);
public:
  ~Lowerer(){}
  static std::unique_ptr<Lowerer> createIfNeeded(Module& M);
  bool lowerEarlyIntrinsics(Function& F);
};

void Lowerer::replaceCoroPromise(IntrinsicInst *Intrin, bool from) {
  Value *Operand = Intrin->getArgOperand(0);
  auto PromisePtr = cast<PointerType>(
    from ? Operand->getType() : Intrin->getFunctionType()->getReturnType());
  auto PromiseType = PromisePtr->getElementType();

  // FIXME: this should be queried from FrameBuilding layer, not here
  auto SampleStruct = StructType::get(C, 
      {AnyResumeFnPtrTy, AnyResumeFnPtrTy, Int8Ty, PromiseType});
  const DataLayout &DL = M.getDataLayout();
  const int64_t Offset = DL.getStructLayout(SampleStruct)->getElementOffset(3);

  Value* Replacement = nullptr;

  Builder.SetInsertPoint(Intrin);
  if (from) {
    auto BCI = Builder.CreateBitCast(Operand, Int8PtrTy);
    auto Gep = Builder.CreateConstInBoundsGEP1_32(Int8Ty, BCI, -Offset);
    Replacement = Gep;
  }
  else {
    auto Gep = Builder.CreateConstInBoundsGEP1_32(Int8Ty, Operand, Offset);
    auto BCI = Builder.CreateBitCast(Gep, PromisePtr);
    Replacement = BCI;
  }

  Intrin->replaceAllUsesWith(Replacement);
  Intrin->eraseFromParent();
}

void Lowerer::lowerResumeOrDestroy(IntrinsicInst* II, unsigned Index) {
  auto IndexVal = ConstantInt::get(Type::getInt8Ty(C), Index);
  auto Fn = Intrinsic::getDeclaration(&M, Intrinsic::coro_subfn_addr);

  SmallVector<Value*, 2> Args{ II->getArgOperand(0), IndexVal };
  auto Call = CallInst::Create(Fn, Args, "", II);

  auto FTy = FunctionType::get(Type::getVoidTy(C), Type::getInt8PtrTy(C),
                               /*isVarArg=*/false);
  auto Bitcast = new BitCastInst(Call, FTy->getPointerTo(), "", II);

  auto Indirect = CallInst::Create(Bitcast, II->getArgOperand(0), "");
  Indirect->setCallingConv(CallingConv::Fast);
  ReplaceInstWithInst(II, Indirect);
}

void Lowerer::lowerCoroDone(IntrinsicInst* II) {
  Value *Operand = II->getArgOperand(0);
#if CORO_USE_INDEX_FOR_DONE
// FIXME: this should be queried from FrameBuilding layer, not here
  auto FrameTy = StructType::get(C, 
      {AnyResumeFnPtrTy, AnyResumeFnPtrTy, Int8Ty});
  PointerType* FramePtrTy = FrameTy->getPointerTo();

  Builder.SetInsertPoint(II);
  auto BCI = Builder.CreateBitCast(Operand, FramePtrTy);
  auto Gep = Builder.CreateConstInBoundsGEP2_32(FrameTy, BCI, 0, 2);
  auto Load = Builder.CreateLoad(Gep);
  auto Cond = Builder.CreateICmpEQ(Load, ConstantInt::get(Int8Ty, 0));
#else
  // FIXME: this should be queried from FrameBuilding layer, not here
  auto FrameTy = Int8PtrTy;
  PointerType* FramePtrTy = FrameTy->getPointerTo();

  Builder.SetInsertPoint(II);
  auto BCI = Builder.CreateBitCast(Operand, FramePtrTy);
  auto Gep = Builder.CreateConstInBoundsGEP1_32(FrameTy, BCI, 0);
  auto Load = Builder.CreateLoad(Gep);
  auto Cond = Builder.CreateICmpEQ(
      Load, ConstantPointerNull::get(Int8PtrTy));
#endif
  II->replaceAllUsesWith(Cond);
  II->eraseFromParent();
}

// TODO: handle invoke coro.resume and coro.destroy
bool Lowerer::lowerEarlyIntrinsics(Function& F) {
  bool changed = false;
  for (auto IB = inst_begin(F), IE = inst_end(F); IB != IE;) 
    if (auto II = dyn_cast<IntrinsicInst>(&*IB++)) {
      switch (II->getIntrinsicID()) {
      default:
        continue;
      case Intrinsic::coro_resume:
        lowerResumeOrDestroy(II, 0);
        break;
      case Intrinsic::coro_destroy:
        lowerResumeOrDestroy(II, 1);
        break;
      case Intrinsic::coro_done:
        lowerCoroDone(II);
        break;
      case Intrinsic::coro_promise:
        replaceCoroPromise(II);
        break;
      case Intrinsic::coro_from_promise:
        replaceCoroPromise(II, /*from=*/true);
        break;
      }
      changed = true;
    }
  return changed;
}

std::unique_ptr<Lowerer> Lowerer::createIfNeeded(Module& M) {
  if (M.getNamedValue(CoroBeginInst::getIntrinsicName()) ||
    M.getNamedValue(CoroResumeInst::getIntrinsicName()) ||
    M.getNamedValue(CoroDestroyInst::getIntrinsicName()) ||
    M.getNamedValue(CoroDoneInst::getIntrinsicName()) ||
    M.getNamedValue(CoroPromiseInst::getIntrinsicName()) ||
    M.getNamedValue(CoroFromPromiseInst::getIntrinsicName()))
    return std::unique_ptr<Lowerer>(new Lowerer(M));

  return{};
}

//===----------------------------------------------------------------------===//
//                              Top Level Driver
//===----------------------------------------------------------------------===//

namespace {
struct CoroEarly : public FunctionPass {
  static char ID; // Pass identification, replacement for typeid
  CoroEarly() : FunctionPass(ID) {}

  std::unique_ptr<Lowerer> L;

  bool doInitialization(Module& M) override {
    L = Lowerer::createIfNeeded(M);
    return false;
  }

  bool runOnFunction(Function &F) override { 
    if (!L)
      return false;

    return L->lowerEarlyIntrinsics(F); 
  }
};
}

char CoroEarly::ID = 0;
INITIALIZE_PASS(CoroEarly, "coro-early", "Lower early coroutine intrinsics",
                false, false)
Pass *llvm::createCoroEarlyPass() { return new CoroEarly(); }
