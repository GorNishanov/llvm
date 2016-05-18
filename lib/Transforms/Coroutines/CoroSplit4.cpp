//===- CoroSplit2.cpp - Manager for Coroutine Passes -----------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// wait for it
//
//===----------------------------------------------------------------------===//

#include "CoroutineCommon.h"
#include "CoroSplit4.h"
#include "llvm/ADT/SmallBitVector.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/InlineCost.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/Pass.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Coroutines.h"
#include "llvm/Transforms/IPO/InlinerPass.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Scalar.h"
using namespace llvm;

#define DEBUG_TYPE "coro-split4"

namespace {

struct CoroSplit4 : CoroutineCommon {

  struct SuspendPoint {
    IntrinsicInst* SuspendInst;
    BranchInst* SuspendBr;
    IntrinsicInst* SaveInst;

    SuspendPoint(Instruction &I) : SuspendInst(dyn_cast<IntrinsicInst>(&I)) {
      if (!SuspendInst)
        return;
      if (SuspendInst->getIntrinsicID() != Intrinsic::coro_suspend2) {
        SuspendInst = nullptr;
        return;
      }
      SaveInst = cast<IntrinsicInst>(SuspendInst->getArgOperand(0));
      assert(SaveInst->getIntrinsicID() == Intrinsic::coro_save2);


      SuspendBr = dyn_cast<BranchInst>(SuspendInst->getNextNode());
      if (!SuspendBr)
        return;

      if (isFinalSuspend()) {
        assert(SuspendBr->getNumSuccessors() == 1);
      }
      else {
        assert(SuspendBr->getNumSuccessors() == 2);
        assert(SuspendBr->getOperand(0) == SuspendInst);
      }
    }

    bool isCanonical() const { return SuspendBr; }

    void remapSuspendInst(BasicBlock* BB, ConstantInt* CI) {
      ValueToValueMapTy VMap;
      VMap[SuspendInst] = CI;
      for (Instruction &I : *BB)
        RemapInstruction(&I, VMap,
          RF_NoModuleLevelChanges | RF_IgnoreMissingEntries);
    }

    static void fixupPhiNodes(BasicBlock *ResumeBB, BasicBlock *CleanupBB,
                              ValueToValueMapTy &VMap) {
      for (BasicBlock* BB : successors(CleanupBB)) {
        for (Instruction& I : *BB) {
          PHINode* PN = dyn_cast<PHINode>(&I);
          if (!PN)
            break;

          auto N = PN->getNumIncomingValues();
          SmallBitVector remapNeeded(N);
          for (unsigned i = 0; i != N; ++i)
            if (PN->getIncomingBlock(i) == ResumeBB)
              remapNeeded.set(i);

          for (int i = remapNeeded.find_first(); i != -1;
               i = remapNeeded.find_next(i)) {
            auto NewValue = VMap[PN->getIncomingValue(i)];
            PN->addIncoming(NewValue, CleanupBB);
          }
        }
      }
    }

    bool canonicalize() {
      if (isCanonical())
        return false;
      BasicBlock* BB = SuspendInst->getParent();
      Function* F = BB->getParent();
      Module* M = F->getParent();
      BasicBlock* ResumeBB =
        BB->splitBasicBlock(SuspendInst->getNextNode(), BB->getName() + ".resume");

      ValueToValueMapTy VMap;
      auto CleanupBB = CloneBasicBlock(ResumeBB, VMap, ".cleanup", F);
      CleanupBB->setName(BB->getName() + ".cleanup");
      remapSuspendInst(CleanupBB, ConstantInt::getFalse(M->getContext()));
      remapSuspendInst(ResumeBB, ConstantInt::getTrue(M->getContext()));
      
      BB->getTerminator()->eraseFromParent();
      SuspendBr = BranchInst::Create(ResumeBB, CleanupBB, SuspendInst, BB);

      fixupPhiNodes(ResumeBB, CleanupBB, VMap);

      DEBUG(dbgs() << "Canonicalize block " << BB->getName() << ". New edges: "
        << ResumeBB->getName() << " " << CleanupBB->getName() << "\n");
      return true;
    }

    BasicBlock* getResumeBlock() const {
      return isFinalSuspend() ? nullptr : SuspendBr->getSuccessor(0);
    }
    BasicBlock* getCleanupBlock() const {
      return isFinalSuspend() ? SuspendBr->getSuccessor(0)
        : SuspendBr->getSuccessor(1);
    }

    ConstantInt *getIndex() const {
      return cast<ConstantInt>(SaveInst->getOperand(0));
    }

    bool isFinalSuspend() const { return getIndex()->isZero(); }
    explicit operator bool() const { return SuspendInst; }
  };

  struct SuspendInfo {
    SmallPtrSet<BasicBlock*, 8> SuspendBlocks;
    SmallPtrSet<BasicBlock*, 8> EndBlocks;
    SmallVector<SuspendPoint, 8> SuspendPoints;
    bool HasFinalSuspend;

    void splitBlockOnCoroEnd(BasicBlock& BB) {
      for (auto &I : BB)
        if (auto II = dyn_cast<IntrinsicInst>(&I))
          if (II->getIntrinsicID() == Intrinsic::experimental_coro_end) {
            EndBlocks.insert(&BB);
            Instruction* NextInstr = II->getNextNode();
            if (!NextInstr->isTerminator())
              SplitBlock(&BB, NextInstr);
            return;
          }
    }

    // go through all blocks and split blocks on coro end
    // COMMENT: explain why we need to split
    void splitEnds(Function& F) {
      EndBlocks.clear();
      for (auto BI = F.begin(), BE = F.end(); BI != BE;)
        splitBlockOnCoroEnd(*BI++);
    }

    // Canonical suspend is where
    // an @llvm.coro.suspend is followed by a
    // branch instruction 
    bool canonicalizeSuspends(Function& F) {
      bool changed = false;
      SuspendPoints.clear();
      HasFinalSuspend = false;
      for (auto BI = F.begin(), BE = F.end(); BI != BE;) {
        auto& BB = *BI++;
        for (auto &I : BB)
          if (SuspendPoint SI{ I }) {
            changed |= SI.canonicalize();
            SuspendPoints.push_back(SI);
            HasFinalSuspend |= SI.isFinalSuspend();
            break;
          }
      }
      if (changed)
        CoroutineCommon::simplifyAndConstantFoldTerminators(F);

      SuspendBlocks.clear();
      for (auto SP : SuspendPoints)
        SuspendBlocks.insert(SP.SuspendInst->getParent());

      return changed;
    }

    bool isSuspendBlock(BasicBlock* BB) const { return SuspendBlocks.count(BB); }
  };

  Function* ThisFunction;

  coro::CoroutineData* CD;

  void processValue(IntrinsicInst* CoroInit, Value *DefInst, DominatorTree &DT,
                    SuspendInfo const &Info,
                    SmallVectorImpl<AllocaInst *> &SharedAllocas) {

    Instruction* AllocaInsertPt = ThisFunction->getEntryBlock().getTerminator();
    Instruction* StoreInsertPt = nullptr;
    BasicBlock* DefBlock = nullptr;
    if (auto I = dyn_cast<Instruction>(DefInst)) {
      if (auto Inv = dyn_cast<InvokeInst>(I)) {
        DefBlock = Inv->getNormalDest();
        StoreInsertPt = DefBlock->getFirstNonPHI();
      }
      else {
        DefBlock = I->getParent();
        StoreInsertPt = I->getNextNode();
        while (isa<PHINode>(StoreInsertPt))
          StoreInsertPt = StoreInsertPt->getNextNode();
      }
    }
    else {
      StoreInsertPt = CoroInit->getNextNode();
    }

    AllocaInst* Spill = nullptr;

    for (auto UI = DefInst->use_begin(), UE = DefInst->use_end(); UI != UE;) {
      Use &U = *UI++;
      Instruction* I = cast<Instruction>(U.getUser());
      auto UseBlock = I->getParent();
      if (UseBlock == DefBlock)
        continue;
      if (auto II = dyn_cast<IntrinsicInst>(I))
        if (II->getIntrinsicID() == Intrinsic::coro_kill2)
          continue;

      BasicBlock* BB = nullptr;
      PHINode* PI = dyn_cast<PHINode>(I);
      if (PI)
        BB = PI->getIncomingBlock(U);
      else {
        BB = DT[UseBlock]->getIDom()->getBlock();
      }
      for (;;) {
        if (Info.isSuspendBlock(BB)) {
          Instruction* InsertPt = I;

          // if it is used in a Phi instruction, split the edge
          if (PI) {
            BasicBlock *NewBB = SplitEdge(PI->getIncomingBlock(U), UseBlock, &DT);
            InsertPt = NewBB->getTerminator();
          }

          // we may be able to recreate instruction
          if (auto Gep = dyn_cast<GetElementPtrInst>(DefInst)) {
            if (isa<AllocaInst>(Gep->getPointerOperand()))
              if (Gep->hasAllConstantIndices()) {
                auto Dup = Gep->clone();
                DEBUG(dbgs() << "Cloned: " << *Dup << "\n");
                Dup->insertBefore(InsertPt);
                U.set(Dup);
                break;
              }
          }

          // see if we already created a spill slot
          // otherwise, create a spill slot
          if (!Spill) {
            Spill = new AllocaInst(DefInst->getType(),
                                   DefInst->getName() + ".spill.alloca",
                                   AllocaInsertPt);
            new StoreInst(DefInst, Spill, StoreInsertPt);
            SharedAllocas.push_back(Spill);
          }

          // load from the spill slot
          auto Reload = new LoadInst(Spill, DefInst->getName() + ".spill", InsertPt);
          U.set(Reload);
          DEBUG(dbgs() << "Created spill: " << *Reload << "\n");
          break;
        }
        if (BB == DefBlock)
          break;
        auto* Node = DT[BB]->getIDom();
        if (Node == nullptr) // possible if DefInst is an Argument
          break;
        BB = DT[BB]->getIDom()->getBlock();
      }
    }
  }

  void insertSpills(IntrinsicInst* CoroInit, Function &F, DominatorTree &DT, SuspendInfo const &Info,
                    SmallVectorImpl<AllocaInst *>& SharedAllocas) {

    SmallVector<Instruction*, 8> Values;
    ThisFunction = &F;

    for (auto &BB : F) {
      for (auto &I : BB) {
        if (I.user_empty())
          continue;
        if (isa<AllocaInst>(&I))
          continue;

        for (User* U: I.users())
          if (auto UI = dyn_cast<Instruction>(U)) {
            BasicBlock* UseBlock = UI->getParent();
            if (UseBlock == &BB)
              continue; 
            if (!DT.isReachableFromEntry(UseBlock))
              continue;
            Values.push_back(&I);
            break;
          }
      }
    }

    for (auto Value: Values) {
      processValue(CoroInit, Value, DT, Info, SharedAllocas);
    }
    for (auto& Arg : F.getArgumentList()) {
      if (Arg.hasInAllocaAttr()) {
        llvm_unreachable("cannot handle coroutines with inalloca arguments yet");
        return;
      }
      processValue(CoroInit, &Arg, DT, Info, SharedAllocas);
    }
  }

  struct CoroutineInfo {
    SmallVector<AllocaInst*, 4> ResumeAllocas;
    SmallVector<AllocaInst*, 8> SharedAllocas;
    SmallPtrSet<BasicBlock*, 16> PostStartBlocks;
    SmallPtrSet<BasicBlock*, 16> StartBlocks;
    BasicBlock* ReturnBlock;
    IntrinsicInst* CoroInit;
    IntrinsicInst* CoroFork;
    BasicBlock* Unreachable;

    CoroutineInfo() {}
    CoroutineInfo(CoroutineInfo const&) = delete;
    CoroutineInfo& operator=(CoroutineInfo const&) = delete;

    BasicBlock *findReturnBlock(Function &F) {
      for (auto &I : instructions(F))
        if (auto II = dyn_cast<IntrinsicInst>(&I))
          if (II->getIntrinsicID() == Intrinsic::experimental_coro_fork) {
            assert(II->getNumUses() == 1 &&
                   "@llvm.coro.done unexpected num users");
            CoroFork = II;
            auto BR = cast<BranchInst>(II->user_back());
            auto ReturnBlock = BR->getSuccessor(0);
            assert(isa<ReturnInst>(ReturnBlock->getTerminator()));
            return ReturnBlock;
          }
      llvm_unreachable("did not find @llvm.coro.done marking the return block");
    }

    void ComputeAllSuccessorsButDontFollowTheseBlocks(
        SmallPtrSetImpl<BasicBlock *> const &NotThese, BasicBlock *B,
        SmallPtrSetImpl<BasicBlock *> &result) {

      SmallSetVector<BasicBlock *, 16> workList;

      workList.insert(B);
      while (!workList.empty()) {
        B = workList.pop_back_val();
        result.insert(B);

        // do not follow successors of indicated blocks
        if (NotThese.count(B) != 0)
          continue;

        for (BasicBlock *SI : successors(B))
          if (result.count(SI) == 0)
            workList.insert(SI);
      }
    }
#if 0
    void ComputeAllSuccessorsButDontFollowSuspendBlocks(
        BasicBlock *B, SuspendInfo &Info,
        SmallPtrSetImpl<BasicBlock *> &result) {
      SmallSetVector<BasicBlock *, 16> workList;

      workList.insert(B);
      while (!workList.empty()) {
        B = workList.pop_back_val();
        result.insert(B);

        // do not follow successors of suspend blocks
        if (Info.isSuspendBlock(B))
          continue;

        for (BasicBlock *SI : successors(B))
          if (result.count(SI) == 0)
            workList.insert(SI);
      }
    }
#endif

    void analyzeFunction(Function &F, SuspendInfo &Info) {
      ReturnBlock = findReturnBlock(F);
      CoroInit = FindIntrinsic(F, Intrinsic::coro_init);
      CoroInit->addAttribute(AttributeSet::ReturnIndex, Attribute::NonNull);
      assert(CoroInit && "missing @llvm.coro.init");

      ResumeAllocas.clear();
      SharedAllocas.clear();

      StartBlocks.clear();
      ComputeAllSuccessorsButDontFollowTheseBlocks(Info.SuspendBlocks, &*F.begin(), StartBlocks);

      Unreachable = BasicBlock::Create(F.getContext(), "unreach", &F);
      new UnreachableInst(F.getContext(), Unreachable);

      PostStartBlocks.clear();
      for (auto SP : Info.SuspendPoints) {
        ComputeAllSuccessorsButDontFollowTheseBlocks(Info.EndBlocks, SP.getCleanupBlock(), PostStartBlocks);
        if (!SP.isFinalSuspend())
          ComputeAllSuccessorsButDontFollowTheseBlocks(Info.EndBlocks, SP.getResumeBlock(), PostStartBlocks);
      }

      for (auto& I : instructions(F)) {
        if (auto AI = dyn_cast<AllocaInst>(&I)) {
          assert(isa<ConstantInt>(AI->getArraySize()) && "cannot handle non-const allocas yet");
          if (AI->getName() == "__promise") {
            // promise must be always in the shared state
            // and it must be the first field
            SharedAllocas.push_back(AI);
            if (SharedAllocas.size() > 1)
              std::swap(SharedAllocas.front(), SharedAllocas.back());
            continue;
          }
          bool seenInStart = false;
          bool seenInResume = false;
          for (User* U : AI->users()) {
            Instruction *UI = cast<Instruction>(U);
            bool inResume = PostStartBlocks.count(UI->getParent());
            bool inStart = StartBlocks.count(UI->getParent());
            //            seenInStart |= !inResume; // bug here
            seenInStart |= inStart; // bug here
            seenInResume |= inResume;
          }
          if (seenInResume)
            if (seenInStart)
              SharedAllocas.push_back(AI);
            else
              ResumeAllocas.push_back(AI);
          else
            if (!seenInStart)
              errs() << "dead alloca: " << *AI << "\n";
        }
      }
    }
  };

#if 0
  // TODO: move them to some struct
  SmallString<16> smallString;
  StructType *frameTy = nullptr;
  PointerType *framePtrTy = nullptr;
  FunctionType *resumeFnTy = nullptr;
  PointerType *resumeFnPtrTy = nullptr;

  void init(Function &F) {
    this->ThisFunction = &F;
    smallString.clear();
    frameTy = StructType::create(
      M->getContext(), (F.getName() + ".frame").toStringRef(smallString));
    framePtrTy = PointerType::get(frameTy, 0);
    resumeFnTy = FunctionType::get(voidTy, framePtrTy, false);
    resumeFnPtrTy = PointerType::get(resumeFnTy, 0);
  }

  Function *CreateAuxillaryFunction(Twine suffix, Value *&frame) {
    auto func = Function::Create(resumeFnTy, GlobalValue::InternalLinkage,
      ThisFunction->getName() + suffix, M);
    func->setCallingConv(CallingConv::Fast);
    frame = &*func->arg_begin();
    frame->setName("frame.ptr" + suffix);
    return func;
  }

  Function *resumeFn = nullptr;
  Function *destroyFn = nullptr;
  Function *cleanupFn = nullptr;
  Value *frameInDestroy = nullptr;
  Value *frameInResume = nullptr;
  Value *frameInRamp = nullptr;
  Value *frameInCleanup = nullptr;

  void CreateAuxillaryFunctions() {
    resumeFn = CreateAuxillaryFunction(".resume", frameInResume);
    destroyFn = CreateAuxillaryFunction(".destroy", frameInDestroy);
    cleanupFn = CreateAuxillaryFunction(".cleanup", frameInCleanup);
  }
#endif
  void createFrameStruct(SmallVectorImpl<AllocaInst *>& SharedAllocas) {
    SmallVector<Type *, 8> typeArray;

    const DataLayout &DL = M->getDataLayout();

    typeArray.clear();
    typeArray.push_back(CD->ResumeFnPtrTy); // 0 res-type
    typeArray.push_back(CD->ResumeFnPtrTy); // 1 dtor-type
    typeArray.push_back(int32Ty);       // 2 index
#if 0
    typeArray.push_back(int32Ty);       // 3 padding // TODO: make it conditional on arch?
#endif
    // TODO: optimize storage layout

    for (AllocaInst *AI : SharedAllocas) {
      typeArray.push_back(AI->getType()->getElementType());
    }
    CD->FrameTy->setBody(typeArray);

    APInt size(32, DL.getTypeAllocSize(CD->FrameTy));
    ReplaceIntrinsicWith(*ThisFunction, Intrinsic::coro_size, ConstantInt::get(int32Ty, size));
  }

  SmallString<16> Scratch;

  // replace all uses of allocas with gep from frame struct
  void ReplaceSharedUses(CoroutineInfo const& Info) {
    enum { kStartingField = 2 };
    APInt fieldNo(32, kStartingField); // Fields start with after 2

    for (AllocaInst *AI : Info.SharedAllocas) {
      auto& Name = Scratch;
      Name = AI->getName();
      if (Name == "__promise") {
        assert(fieldNo == kStartingField && "promise shall be the first field");
      }
      AI->setName(""); // FIXME: use TakeName
      auto index = ConstantInt::get(M->getContext(), ++fieldNo);

      while (!AI->use_empty()) {
        Use &U = *AI->use_begin();
        User *user = U.getUser();
        Value *frame = CD->Ramp.Frame;
        auto gep =
          GetElementPtrInst::Create(CD->FrameTy, frame, { zeroConstant, index },
            Name, cast<Instruction>(user));
        U.set(gep);
      }
      AI->eraseFromParent();
    }
#if 0
    // we may end up replacing allocas with gep before frame is defined
    // move definition of frame to the beginning of function
    InstrSetVector coroFrameUses;
    ComputeDefChainNotIn(Info.CoroInit, Info.PostStartBlocks, coroFrameUses);
    MoveInReverseOrder(coroFrameUses, &*inst_begin(ThisFunction));
#endif
  }

  static void fixupPhiNodes(BasicBlock *Target, BasicBlock *OldPred,
                            BasicBlock *NewPred) {
    for (Instruction& I : *Target) {
      PHINode* PN = dyn_cast<PHINode>(&I);
      if (!PN)
        break;

      auto N = PN->getNumIncomingValues();
      for (unsigned i = 0; i != N; ++i)
        if (PN->getIncomingBlock(i) == OldPred)
          PN->setIncomingBlock(i, NewPred);
    }
  }

  void prepareFrame(CoroutineInfo& CoroInfo) {
    createFrameStruct(CoroInfo.SharedAllocas);
    auto InsertPt = CoroInfo.CoroInit->getNextNode();

    CD->Ramp.Frame = new BitCastInst(CoroInfo.CoroInit, CD->FramePtrTy, "frame",
      InsertPt);
    auto gep0 = GetElementPtrInst::Create(
      CD->FrameTy, CD->Ramp.Frame, { zeroConstant, zeroConstant }, "", InsertPt);
    new StoreInst(CD->Resume.Func, gep0, InsertPt);

    auto gep1 = GetElementPtrInst::Create(
      CD->FrameTy, CD->Ramp.Frame, { zeroConstant, oneConstant }, "", InsertPt);

    auto CoroElide = GetCoroElide(CoroInfo.CoroInit);
    auto ICmp = new ICmpInst(InsertPt, ICmpInst::ICMP_EQ, CoroElide,
                             ConstantPointerNull::get(bytePtrTy));
    auto Sel = SelectInst::Create(ICmp, CD->Destroy.Func, CD->Cleanup.Func, "", InsertPt);
    new StoreInst(Sel, gep1, InsertPt);

#if 0
    auto gepIndex = GetElementPtrInst::Create(frameTy, frameInRamp,
    { zeroConstant, oneConstant }, "", InsertPt);
    auto fnAddr = new LoadInst(gepIndex, "", InsertPt); // FIXME: alignment
    auto call = CallInst::Create(fnAddr, frameInRamp, "", InsertPt);
    call->setCallingConv(CallingConv::Fast);
#endif
  }

  bool replaceCoroPromise(Function& F) {
    bool changed = false;
    for (auto it = inst_begin(F), end = inst_end(F); it != end;) {
      Instruction &I = *it++;
      if (auto intrin = dyn_cast<IntrinsicInst>(&I)) {
        switch (intrin->getIntrinsicID()) {
        default:
          continue;
        case Intrinsic::coro_promise:
          ReplaceCoroPromise(intrin);
          changed = true;
          break;
        case Intrinsic::coro_from_promise:
          ReplaceCoroPromise(intrin, /*From=*/true);
          changed = true;
          break;
#if 0
        case Intrinsic::coro_resume:
          ReplaceWithIndirectCall(intrin, zeroConstant);
          changed = true;
          break;
#endif          
        case Intrinsic::coro_destroy:
          ReplaceWithIndirectCall(intrin, oneConstant, /*EraseIntrin=*/false);
          changed = true;
          break;
          /*
        case Intrinsic::coro_done:
          ReplaceCoroDone(intrin);
          changed = true;
          break;
          */
        }
      }
    }
    return changed;
  }

  void runOn(coro::CoroutineData& CoroData) {
    CD = &CoroData;
    ThisFunction = CD->Ramp.Func;
    runOnCoroutine(*ThisFunction);
  }

  void removeLifetimeIntrinsics(Function& F) {
    for (auto it = inst_begin(F), end = inst_end(F); it != end;) {
      Instruction &I = *it++;
      if (auto II = dyn_cast<IntrinsicInst>(&I))
        switch (II->getIntrinsicID()) {
        default:
          continue;
        case Intrinsic::lifetime_start:
        case Intrinsic::lifetime_end:
          II->eraseFromParent();
          break;
        }
    }
  }

  bool runOnCoroutine(Function& F) {
    DEBUG(dbgs() << "CoroSplit function: " << F.getName() << "\n");

    removeLifetimeIntrinsics(F);

    SuspendInfo Suspends;
    CoroutineInfo CoroInfo;

#if 0
    init(F);
    CreateAuxillaryFunctions();
#endif
    //assert(F.getPrefixData() == nullptr && "coroutine should not have function prefix");
    //F.setPrefixData(destroyFn);

    Suspends.splitEnds(F);
    Suspends.canonicalizeSuspends(F);
    CoroInfo.analyzeFunction(F, Suspends);

    DominatorTree DT;
    DT.recalculate(F);
    insertSpills(CoroInfo.CoroInit, F, DT, Suspends, CoroInfo.SharedAllocas);

    // move this into PrepareFrame func
    prepareFrame(CoroInfo);

    ReplaceSharedUses(CoroInfo);

    for (auto InResume : CoroInfo.ResumeAllocas)
      errs() << "resume alloca: " << *InResume << "\n";

    BasicBlock* ResumeEntry = createSwitch("resume.entry", CoroInfo, Suspends);
    BasicBlock *DestroyEntry =
        createSwitch("destroy.entry", CoroInfo, Suspends, /*destroy=*/true);

    replaceSuspends(CoroInfo, Suspends);

    ThisFunction->removeFnAttr(Attribute::Coroutine);

    createResumeOrDestroy(CD->Resume.Func, ResumeEntry, CD->Resume.Frame, CoroInfo, Suspends);
    createResumeOrDestroy(CD->Destroy.Func, DestroyEntry, CD->Destroy.Frame, CoroInfo, Suspends);
    CoroInfo.CoroFork->replaceAllUsesWith(ConstantInt::getFalse(M->getContext()));
    CoroInfo.CoroFork->eraseFromParent();
    removeUnreachableBlocks(F);
    simplifyAndConstantFoldTerminators(F);
    removeUnreachableBlocks(F);

    ReplaceIntrinsicWith(*ThisFunction, Intrinsic::coro_frame, CoroInfo.CoroInit);
    PrepareForHeapElision();
    return true;
  }

  void replaceDelete(coro::CoroutineData::SubInfo& S, IntrinsicInst* CoroDelete) {
    if (!CoroDelete)
      return;

    assert(CoroDelete->hasOneUse());
    auto User = cast<ICmpInst>(CoroDelete->user_back());
    User->replaceAllUsesWith(ConstantInt::getFalse(M->getContext()));
    User->eraseFromParent();
    CoroDelete->eraseFromParent();
    simplifyAndConstantFoldTerminators(*S.Func);
  }

  void PrepareForHeapElision()
  {
    IntrinsicInst* DeleteInResume = FindIntrinsic(*CD->Resume.Func, Intrinsic::coro_delete);
    IntrinsicInst* DeleteInRamp = FindIntrinsic(*ThisFunction, Intrinsic::coro_delete);
    IntrinsicInst* DeleteInDestroy = FindIntrinsic(*CD->Destroy.Func, Intrinsic::coro_delete);

    // if we found delete in Resume or Ramp, the coroutine is not eligible
    // for heap elision, so we don't have to create a .cleanup function

    if (!DeleteInResume && !DeleteInRamp) {
      // clone the Destroy function and eliminate the delete block
      ValueToValueMapTy VMap;
      VMap[CD->Destroy.Frame] = CD->Cleanup.Frame;
      SmallVector<ReturnInst*, 4> Returns;
      CloneFunctionInto(CD->Cleanup.Func, CD->Destroy.Func, VMap, false, Returns);

      // remove dummy entry block
      CD->Cleanup.Func->begin()->eraseFromParent();

      IntrinsicInst* CoroDelete = cast<IntrinsicInst>(VMap[DeleteInDestroy]);
      CoroDelete->replaceAllUsesWith(ConstantPointerNull::get(bytePtrTy));
      CoroDelete->eraseFromParent();

      simplifyAndConstantFoldTerminators(*CD->Cleanup.Func);
    }

    replaceDelete(CD->Resume, DeleteInResume);
    replaceDelete(CD->Ramp, DeleteInRamp);
    replaceDelete(CD->Destroy, DeleteInDestroy);
  }

  BasicBlock* createSwitch(StringRef Name, CoroutineInfo &Info, SuspendInfo &Suspends,
                    bool Destroy = false) {
    auto Entry = BasicBlock::Create(M->getContext(), Name, ThisFunction);
    auto CaseCount =
      Suspends.SuspendPoints.size() - ((Destroy || Suspends.HasFinalSuspend) ? 1 : 0);

    auto gepIndex = GetElementPtrInst::Create(
      CD->FrameTy, CD->Ramp.Frame, { zeroConstant, twoConstant }, "", Entry);
    auto index = new LoadInst(gepIndex, "index", Entry);
    auto switchInst = SwitchInst::Create(index, Info.Unreachable, CaseCount, Entry);

    for (auto SP : Suspends.SuspendPoints) {
      BasicBlock* Target = nullptr;
      if (Destroy)
        Target = SP.getCleanupBlock();
      else if (SP.isFinalSuspend())
        continue;
      else 
        Target = SP.getResumeBlock();
      switchInst->addCase(SP.getIndex(), Target);
      fixupPhiNodes(Target, SP.SuspendInst->getParent(), Entry);
    }
    return Entry;
  }

  void CallAwaitSuspend(IntrinsicInst *I, Value *FramePtr) {
    auto vFrame = new BitCastInst(FramePtr, bytePtrTy, "", I);
    Value *op = I->getArgOperand(1);
    while (const ConstantExpr *CE = dyn_cast<ConstantExpr>(op)) {
      if (!CE->isCast())
        break;
      // Look through the bitcast
      op = cast<ConstantExpr>(op)->getOperand(0);
    }
    Function* fn = cast<Function>(op);
    assert(fn->getType() == awaitSuspendFnPtrTy && "unexpected await_suspend fn type");

    CallInst::Create(fn, { I->getArgOperand(0), vFrame }, "", I);
  }

  void replaceSuspends(CoroutineInfo &Info, SuspendInfo const &Suspends) {
    if (Suspends.SuspendPoints.size() == 1) {
      // if we have only one suspend point, move
      // the save instruction to the init part
      auto SI = Suspends.SuspendPoints.front().SaveInst;
      SI->moveBefore(Info.CoroInit->getNextNode());
    }
    for (auto SP : Suspends.SuspendPoints) {
      BranchInst::Create(Info.ReturnBlock, SP.SuspendBr);
      SP.SuspendBr->eraseFromParent();
      auto gep = GetElementPtrInst::Create(CD->FrameTy, CD->Ramp.Frame,
                                           {zeroConstant, twoConstant}, "",
                                           SP.SaveInst);
      new StoreInst(SP.getIndex(), gep, SP.SaveInst);
      SP.SuspendInst->eraseFromParent();
      SP.SaveInst->eraseFromParent();
      //CallAwaitSuspend(SP.SuspendInst, CD->Ramp.Frame);
    }
  }

  void createResumeOrDestroy(
    Function * NewFn,
    BasicBlock* CaseBlock,
    Value* FramePtr,
    CoroutineInfo &CoroInfo, SuspendInfo& Suspends) {

    ValueToValueMapTy VMap;
    for (auto &A : ThisFunction->args())
      VMap[&A] = UndefValue::get(A.getType());

    VMap[CD->Ramp.Frame] = FramePtr;

    SmallVector<ReturnInst*, 4> Returns;
    CloneFunctionInto(NewFn, ThisFunction, VMap, false, Returns);

    auto Entry = cast<BasicBlock>(VMap[CaseBlock]);
    Entry->removeFromParent();
    Entry->insertInto(NewFn, &*NewFn->begin());

    auto Exit = BasicBlock::Create(M->getContext(), "exit", NewFn);
    ReturnInst::Create(M->getContext(), Exit);
    for (auto RI : Returns) {
      auto RB = RI->getParent();
      RB->replaceAllUsesWith(Exit);
      RB->eraseFromParent();
    }

    auto InsertPt = &Entry->front();

    for (auto & AI : CoroInfo.ResumeAllocas) {
      auto clone = cast<AllocaInst>(VMap[AI]);
      clone->removeFromParent();
      clone->insertBefore(InsertPt);
    }

    VMap[CD->Ramp.Frame]->replaceAllUsesWith(FramePtr);

    BlockSet OldEntryBlocks;
    InstrSetVector Used;
    auto OldEntry = cast<BasicBlock>(VMap[CoroInfo.CoroInit->getParent()]);
    OldEntryBlocks.insert(OldEntry);
    for (auto& I : *OldEntry)
      for (User* U : I.users())
        if (cast<Instruction>(U)->getParent() != OldEntry) {
          ComputeDefChain(&I, OldEntryBlocks, Used);
          break;
        }
    MoveInReverseOrder(Used, InsertPt);

    auto vFrame = new BitCastInst(FramePtr, bytePtrTy, "", InsertPt);
    ReplaceIntrinsicWith(*NewFn, Intrinsic::coro_frame, vFrame);

    removeUnreachableBlocks(*NewFn);
    simplifyAndConstantFoldTerminators(*NewFn);
    removeUnreachableBlocks(*NewFn);
    NewFn->setCallingConv(CallingConv::Fast);
  }

#if 0

  void inlineCoroutine(Function& F) {
    SmallVector<CallSite, 8> CSes;

    for (auto U : F.users()) 
      if (auto I = dyn_cast<Instruction>(U)) 
        if (I->getParent()->getParent() != &F) 
          if (auto CS = CallSite(I))
            CSes.push_back(CS);

    for (auto CS : CSes) {
      InlineFunctionInfo IFI;
      InlineFunction(CS, IFI);
    }
  }
  void replaceCoroPromises(Function& F) {
    for (auto it = inst_begin(F), end = inst_end(F); it != end;)
      if (auto II = dyn_cast<IntrinsicInst>(&*it++))
        if (II->getIntrinsicID() == Intrinsic::coro_from_promise)
          ReplaceCoroPromise(II, true);
  }
#endif
#if 0
  bool runOnModule(Module &M) override {
    CoroutineCommon::PerModuleInit(M);

    Function* CoroInit =
      Intrinsic::getDeclaration(&M, Intrinsic::coro_init);

    CoroInit->addAttribute(AttributeSet::ReturnIndex, Attribute::NonNull);

    bool changed = false;
    for (Function &F : M.getFunctionList()) {
      if (F.hasFnAttribute(Attribute::Coroutine)) {
        changed = true;
        runOnCoroutine(F);
      }
      changed |= replaceCoroPromise(F);
    }
    return changed;
  }
#else
#if 0
  bool doInitialization(Module& M) override {
    CoroutineCommon::PerModuleInit(M);
    return false;
  }

  bool runOnFunction(Function &F) override {
    bool changed = false;
    if (F.hasFnAttribute(Attribute::Coroutine)) {
      changed |= runOnCoroutine(F);
    }
    changed |= replaceCoroPromise(F);
    return changed;
  }
#endif
#endif
};
}

void llvm::coro::CoroutineData::SubInfo::Init(Function& F, Twine Suffix, CoroutineData& Data) {
  Func = Function::Create(Data.ResumeFnTy, GlobalValue::InternalLinkage,
    F.getName() + Suffix, F.getParent());
  Func->setCallingConv(CallingConv::Fast);
  Frame = &*Func->arg_begin();
  Frame->setName("frame.ptr" + Suffix);

  // start with unreachable body
  auto BB = BasicBlock::Create(F.getContext(), "entry", Func);
  new UnreachableInst(F.getContext(), BB);

  // NotNull attribute
  Argument* A = cast<Argument>(Frame);
  AttrBuilder B;
  B.addAttribute(Attribute::NonNull);
  A->addAttr(AttributeSet::get(A->getContext(), A->getArgNo() + 1, B));
}

llvm::coro::CoroutineData::CoroutineData(Function& F) {
  SmallString<16> smallString;
  FrameTy = StructType::create(
    F.getContext(), (F.getName() + ".frame").toStringRef(smallString));
  FramePtrTy = PointerType::get(FrameTy, 0);
  ResumeFnTy = FunctionType::get(Type::getVoidTy(F.getContext()), FramePtrTy, false);
  ResumeFnPtrTy = PointerType::get(ResumeFnTy, 0);

  Ramp.Func = &F;
  Ramp.Frame = Ramp.vFrame = nullptr;

  Resume.Init(F, ".resume", *this);
  Destroy.Init(F, ".destroy", *this);
  Cleanup.Init(F, ".cleanup", *this);
}

void llvm::coro::CoroutineData::split(CoroutineCommon*) {
  auto &F = *Ramp.Func;
  auto &M = *F.getParent();
  {
    legacy::FunctionPassManager FPM(&M);
    FPM.add(createCFGSimplificationPass());     // Merge & remove BBs
    FPM.doInitialization();
    FPM.run(F);
    FPM.doFinalization();
  }

  CoroSplit4 pass;
  pass.PerModuleInit(M);
  pass.runOn(*this);
}