//===-- TE.cpp ------------------------------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/TE.h"
#include "llvm-c/Initialization.h"
#include "llvm-c/Transforms/TE.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/InitializePasses.h"
#include "llvm/PassManager.h"

using namespace llvm;

void llvm::initializeTE(PassRegistry &Registry) {
  initializeTimedExecutionPass(Registry);
}

void LLVMInitializeTE(LLVMPassRegistryRef R) {
  initializeTE(*unwrap(R));
}

void LLVMAddTimedExecutionPass(LLVMPassManagerRef PM) {
  unwrap(PM)->add(createTimedExecutionPass());
}
