/*
  Copyright 2015 Google LLC All rights reserved.

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at:

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
*/

/*
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   This library is plugged into LLVM when invoking clang through afl-clang-fast.
   It tells the compiler to add code roughly equivalent to the bits discussed
   in ../afl-as.h.
*/

#define AFL_LLVM_PASS

#include "../config.h"
#include "../debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

using namespace llvm;

namespace {

  class AFLCoverage : public ModulePass {

    public:

      static char ID;
      AFLCoverage() : ModulePass(ID) { }

      bool runOnModule(Module &M) override;

      // StringRef getPassName() const override {
      //  return "American Fuzzy Lop Instrumentation";
      // }

  };

}

std::vector<std::string> syscall_routines = {
    // memory allocation
    "calloc",  "malloc",   "realloc",  "free",
    // memory operation
    "memcpy",  "memmove",  "memchr",   "memset",
    "memcmp",
    // string operation
    "strcpy",  "strncpy",  "strerror", "strlen",
    "strcat",  "strncat",  "strcmp",   "strspn",
    "strcoll", "strncmp",  "strxfrm",  "strstr",
    "strchr",  "strcspn",  "strpbrk",  "strrchr",
    "strtok",
    // TODO... add more interesting functions
};

bool is_syscal(std::string fn_name) {
    for (std::vector<std::string>::size_type i = 0; i < syscall_routines.size(); i++) {
        if (fn_name.compare(0, syscall_routines[i].size(), syscall_routines[i]) == 0)
            return true;
    }
}

char AFLCoverage::ID = 0;


bool AFLCoverage::runOnModule(Module &M) {

  LLVMContext &C = M.getContext();

  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);

  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    SAYF(cCYA "afl-llvm-pass " cBRI VERSION cRST " by <lszekeres@google.com>\n");

  } else be_quiet = 1;

  /* Decide instrumentation ratio */

  char* inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;

  if (inst_ratio_str) {

    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");

  }

  /* Get globals for the SHM region and the previous location. Note that
     __afl_prev_loc is thread-local. */

  GlobalVariable *AFLMapPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

  GlobalVariable* AFLSyscallPtr =
      new GlobalVariable(M, PointerType::get(Int32Ty, 0), false,
          GlobalValue::ExternalLinkage, 0, "__afl_syscall_ptr");

  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
      0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  /* Instrument all the things! */

  int inst_blocks = 0;

  for (auto &F : M)
    for (auto &BB : F) {

        int  syscall_num = 0;

      BasicBlock::iterator IP = BB.getFirstInsertionPt();
      IRBuilder<> IRB(&(*IP));

      if (AFL_R(100) >= inst_ratio) continue;

      //遍历基本块中的指令，获取危险函数调用数目
      for (auto Inst = BB.begin(); Inst != BB.end(); Inst++) {
          Instruction& inst = *Inst;

          // 如果 inst 是 CallInst，那么 dyn_cast 就能成功，否则就会返回空指针
          if (CallInst* call_inst = dyn_cast<CallInst>(&instt)) { 
              Function* fn = call_inst->getCalledFunction(); //获取被调用的函数

              if (fn == NULL) {
                  Value* v = call_inst->getCalledValue(); //获取被调用的值
                  fn = dyn_cast<Function>(v->stripPointerCasts());
                  if (fn == NULL) {
                      continue;
                  }
              }

              std::string fn_name = fn->getName();
              if (fn_name.compare(0, 5, "llvm.") == 0) { //过滤 llvm 的函数
                  continue;
              }

              if (is_syscal(fn_name)) {
                  syscall_num++;
                  outs() << fn_name << "\n";
              }
          }
      }

      /* Make up cur_loc */

      unsigned int cur_loc = AFL_R(MAP_SIZE); //每次都新创建 cur_loc？怎么处理循环基本块？

      ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);

      /* Load prev_loc */

      LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);
      PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty());

      /* Load SHM pointer */

      LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
      MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *MapPtrIdx =
          IRB.CreateGEP(MapPtr, IRB.CreateXor(PrevLocCasted, CurLoc));

      /* Update bitmap */

      LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
      Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));
      IRB.CreateStore(Incr, MapPtrIdx)
          ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      // 获得 边[危险函数命中数] 数组
      if (syscall_num > 0) {
          LoadInst* SyscallPtr = IRB.CreateLoad(AFLSyscallPtr); //相当于对全局变量指针AFLSyscallPtr的一个解引用
          SyscallPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
          //如何解释GEP呢？ 当前解释：第一个参数：基址，第二个参数：偏移，返回一个
          // SyscallPtr[Prev^Cur]
          Value* SyscallPtrIdx = IRB.CreateGEP(SyscallPtr, IRB.CreateXor(PrevLocCasted, CurLoc));
          
          LoadInst* SyscallCounter = IRB.CreateLoad(SyscallPtrIdx); //指针解引用
          SyscallCounter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(c, None));
          Value* SyscallIncr = IRB.CreateAdd(SyscallCounter, ConstantInt::get(Int32Ty, syscall_num));
          IRB.CreateStore(SyscallIncr, SyscallPtrIdx)
              ->setMetadata(M.getMDKindId("nosanitize"), MDNode::get(C, Node));
      }

      /* Set prev_loc to cur_loc >> 1 */

      StoreInst *Store =
          IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> 1), AFLPrevLoc);
      Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      inst_blocks++;

    }

  /* Say something nice. */

  if (!be_quiet) {

    if (!inst_blocks) WARNF("No instrumentation targets found.");
    else OKF("Instrumented %u locations (%s mode, ratio %u%%).",
             inst_blocks, getenv("AFL_HARDEN") ? "hardened" :
             ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN")) ?
              "ASAN/MSAN" : "non-hardened"), inst_ratio);

  }

  return true;

}


static void registerAFLPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM) {

  PM.add(new AFLCoverage());

}


static RegisterStandardPasses RegisterAFLPass(
    PassManagerBuilder::EP_ModuleOptimizerEarly, registerAFLPass);

static RegisterStandardPasses RegisterAFLPass0(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerAFLPass);
