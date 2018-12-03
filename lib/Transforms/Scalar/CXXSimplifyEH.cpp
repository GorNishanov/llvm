//===- CXXSimplifyEH.cpp - Code to simplify C++ EH patterns -------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===--------------------------------------------------------------===//

#include "llvm/Analysis/EHPersonalities.h"
#include "llvm/Pass.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/circular_raw_ostream.h"

using namespace llvm;

#define DEBUG_TYPE "cxx-eh-simplify"

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
    dbgs() << "EH SIMPLIFICATION PATH RUNS\n";
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


