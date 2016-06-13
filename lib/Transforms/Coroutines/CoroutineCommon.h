//===- CoroutineCommon.h - utilities for coroutine passes-------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
/// \file
///
/// This file provides internal interfaces used to implement coroutine passes.
///
//===----------------------------------------------------------------------===//

#ifndef LLVM_LIB_TRANSFORMS_COROUTINES_COROUTINECOMMON_H
#define LLVM_LIB_TRANSFORMS_COROUTINES_COROUTINECOMMON_H

#include "llvm/Support/Compiler.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/IR/IntrinsicInst.h"

#define coro_suspend2 ObsoleteIntrinsic
#define coro_save2 ObsoleteIntrinsic
#define coro_elide ObsoleteIntrinsic

#define coro_init ObsoleteIntrinsic
#define coro_suspend ObsoleteIntrinsic
#define coro_param ObsoleteIntrinsic
#define coro_frame ObsoleteIntrinsic
#define coro_delete ObsoleteIntrinsic
#define coro_size ObsoleteIntrinsic
#define coro_frame2 ObsoleteIntrinsic
#define coro_size2 ObsoleteIntrinsic
#define coro_kill ObsoleteIntrinsic
#define coro_kill2 ObsoleteIntrinsic
#define coro_promise ObsoleteIntrinsic
#define coro_from_promise ObsoleteIntrinsic
#define coro_save ObsoleteIntrinsic
#define coro_load ObsoleteIntrinsic
#define coro_end ObsoleteIntrinsic

#define coro_resume ObsoleteIntrinsic
#define coro_destroy ObsoleteIntrinsic
#define coro_done ObsoleteIntrinsic

namespace llvm {
class Module;
class Type;
class PointerType;
class IntegerType;
class ConstantInt;
class PointerType;
class IntrinsicInst;
class StructType;
class Function;
class BasicBlock;
class AllocaInst;
class PassRegistry;

#define CORO_CLEANUP_SUFFIX ".cleanup"
#define CORO_RESUME_SUFFIX ".resume"
#define CORO_DESTROY_SUFFIX ".destroy"

struct LLVM_LIBRARY_VISIBILITY CoroutineCommon {
  Module *M = nullptr;
  Type *voidTy = nullptr;
  PointerType *bytePtrTy = nullptr;
  PointerType *anyResumeFnPtrTy = nullptr;
  IntegerType *int32Ty = nullptr;
  IntegerType *boolTy = nullptr;
  ConstantInt *zeroConstant = nullptr;
  ConstantInt *oneConstant = nullptr;
  ConstantInt *twoConstant = nullptr;
  PointerType *awaitSuspendFnPtrTy = nullptr;

  StructType *anyFrameTy = nullptr;
  PointerType *anyFramePtrTy = nullptr;

  using BlockSet = SmallPtrSet<BasicBlock *, 16>;
  using InstrSetVector = SmallSetVector<Instruction *, 32>;

  void PerModuleInit(Module &M);

  static IntrinsicInst *FindIntrinsic(BasicBlock &B, Intrinsic::ID intrinID);

  static IntrinsicInst *FindIntrinsic(Function &F, Intrinsic::ID intrinID);

  static IntrinsicInst *GetCoroElide(IntrinsicInst *CoroInit);

  static void ComputeDefChainNotIn(Instruction *instr, BlockSet const &source,
                                   InstrSetVector &result);

  static void ComputeDefChain(Instruction *instr, BlockSet const &source,
                              InstrSetVector &result);

  static void MoveInReverseOrder(InstrSetVector const &Instrs,
                                 Instruction *InsertBefore);

  static void ReplaceIntrinsicWith(Function &F, Intrinsic::ID id, Value *framePtr);
  static void ReplaceIntrinsicWithIntConstant(Function &F, Intrinsic::ID id, unsigned int Val);

  void ReplaceCoroDone(IntrinsicInst *intrin);

  void ReplaceCoroPromise(IntrinsicInst *intrin, bool from = false);

  void ReplaceWithIndirectCall(IntrinsicInst *intrin, ConstantInt *index, bool Erase = true);

  static bool simplifyAndConstantFoldTerminators(Function& F);
};

/// TODO: move to llvm/InitializePasses.h?
/// initializeCoroutines - Initialize all passes linked into the Coroutines
/// library.
void initializeCoroEarlyPass(PassRegistry &Registry);
void initializeCoroElidePass(PassRegistry &Registry);
void initializeCoroCleanupPass(PassRegistry &registry);
void initializeCoroInlinePass(PassRegistry &registry);
}

#endif