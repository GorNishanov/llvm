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

#include "CoroutineCommon.h"

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

// Need metadata helper
//   Coroutine comes out of front end with !"" in place of the metadata
// 
// CoroEarly, will replace it with the tuple:
//   (!func,!"",!"",!"")

#if 0
static void initMetadata(CoroInitInst& CoroInit, Function& F) {
  if (auto S = dyn_cast<MDString>(CoroInit.getRawMeta())) {
    assert(S->getLength() != 0 && "Unexpected metadata string on coro.init");
    SmallVector<Metadata *, 4> Args{ValueAsMetadata::get(&F), S, S, S};
    CoroInit.setMeta(MDNode::get(F.getContext(), Args));
  }
}
#endif
#if 0
static void addBranchToCoroEnd(CoroutineShape &S, Function &F) {
  S.buildFrom(F);
  auto Zero = ConstantInt::get(S.CoroSuspend.back()->getType(), 0);
  auto RetBB = S.CoroEndFinal.back()->getParent();
  assert(isa<CoroEndInst>(RetBB->front()) &&
         "coro.end must be a first instruction in a block");
  for (CoroSuspendInst* CI : S.CoroSuspend) {
    auto InsertPt = CI->getNextNode();
    auto Cond =
      new ICmpInst(InsertPt, CmpInst::Predicate::ICMP_SLT, CI, Zero);
    SplitBlockAndInsertIfThen(Cond, InsertPt, /*unreachable=*/false);
  }
}
#endif

static void finalizeCoroutine(Function& F) {
  CoroutineShape CoroShape(F);
  F.addFnAttr(Attribute::Coroutine);

  auto SuspendCount = CoroShape.CoroSuspend.size();
  if (SuspendCount == 0)
    return;
}

// Keeps data common to all lowering functions.
struct Lowerer {
  Module& M;
  LLVMContext& C;
  IRBuilder<> Builder;
  Type* Int8Ty;
  Type* Int8PtrTy;

  PointerType* AnyResumeFnPtrTy;

  Lowerer(Function &F)
      : M(*F.getParent()), C(F.getContext()), Builder(C),
        Int8Ty(Type::getInt8Ty(C)), Int8PtrTy(Int8Ty->getPointerTo()),
        AnyResumeFnPtrTy(FunctionType::get(Type::getVoidTy(C), Int8PtrTy,
                                           /*isVarArg=*/false)
                             ->getPointerTo()) {}

  void replaceCoroPromise(IntrinsicInst *Intrin, bool from = false);
  void lowerResumeOrDestroy(IntrinsicInst* II, unsigned Index);
  void lowerCoroDone(IntrinsicInst* II);

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

  auto Indirect = CallInst::Create(Bitcast, II->getArgOperand(0), "", II);
  Indirect->setCallingConv(CallingConv::Fast);

  II->eraseFromParent();
}

void Lowerer::lowerCoroDone(IntrinsicInst* II) {
  Value *Operand = II->getArgOperand(0);

// FIXME: this should be queried from FrameBuilding layer, not here
  auto FrameTy = StructType::get(C, 
      {AnyResumeFnPtrTy, AnyResumeFnPtrTy, Int8Ty});
  PointerType* FramePtrTy = FrameTy->getPointerTo();

  Builder.SetInsertPoint(II);
  auto BCI = Builder.CreateBitCast(Operand, FramePtrTy);
  auto Gep = Builder.CreateConstInBoundsGEP2_32(FrameTy, BCI, 0, 2);
  auto Load = Builder.CreateLoad(Gep);
  auto Cond = Builder.CreateICmpEQ(Load, ConstantInt::get(Int8Ty, 0));

  II->replaceAllUsesWith(Cond);
  II->eraseFromParent();
}

// TODO: handle invoke coro.resume and coro.destroy
bool lowerEarlyIntrinsics(Function& F) {
  Lowerer L(F);
  bool changed = false;
  for (auto IB = inst_begin(F), IE = inst_end(F); IB != IE;)
    if (auto II = dyn_cast<IntrinsicInst>(&*IB++)) {
      switch (II->getIntrinsicID()) {
      default:
        continue;
      case Intrinsic::coro_resume:
        L.lowerResumeOrDestroy(II, 0);
        break;
      case Intrinsic::coro_destroy:
        L.lowerResumeOrDestroy(II, 1);
        break;
      case Intrinsic::coro_done:
        L.lowerCoroDone(II);
        break;
      case Intrinsic::coro_promise:
        L.replaceCoroPromise(II);
        break;
      case Intrinsic::coro_from_promise:
        L.replaceCoroPromise(II, /*from=*/true);
        break;
      }
      changed = true;
    }
  return changed;
}

//===----------------------------------------------------------------------===//
//                              Top Level Driver
//===----------------------------------------------------------------------===//

namespace {
struct CoroEarly : public FunctionPass {
  static char ID; // Pass identification, replacement for typeid
  CoroEarly() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override {
    bool changed = lowerEarlyIntrinsics(F);
    if (!F.hasFnAttribute(Attribute::Coroutine))
      return changed;

    Shape.buildFrom(F);

    return changed;
  }

  CoroutineShape Shape;
};
}

char CoroEarly::ID = 0;
INITIALIZE_PASS(
    CoroEarly, "coro-early",
    "Coroutine frame allocation elision and indirect calls replacement", false,
    false)
Pass *llvm::createCoroEarlyPass() { return new CoroEarly(); }
