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

#include "llvm/Support/raw_ostream.h"
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


//@@RiskNum
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
    return false;
}

char AFLCoverage::ID = 0;


bool AFLCoverage::runOnModule(Module &M) {

  LLVMContext &C = M.getContext();

  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);
  IntegerType* Int64Ty = IntegerType::getInt64Ty(C);


  //@@RiskNum
#ifdef WORD_SIZE_64
  IntegerType* LargestType = Int64Ty;
  //ConstantInt* MapCntLoc = ConstantInt::get(LargestType, MAP_SIZE + 8); Based on your 
#else
  IntegerType* LargestType = Int32Ty;
  //ConstantInt* MapCntLoc = ConstantInt::get(LargestType, MAP_SIZE + 4);
#endif
    
  ConstantInt* MapRiskNumLoc = ConstantInt::get(LargestType, MAP_SIZE);
  ConstantInt* One = ConstantInt::get(LargestType, 1);
  
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

  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
      0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  /* Instrument all the things! */

  int inst_blocks = 0;

  for (auto& F : M) {
      for (auto& BB : F) {
          //@@RiskNum
          int syscall_num = 0;


          BasicBlock::iterator IP = BB.getFirstInsertionPt();
          IRBuilder<> IRB(&(*IP));

          if (AFL_R(100) >= inst_ratio) continue;

          //@@RiskNum
          /*To traverse Instructions in each block*/
          for (auto Inst = BB.begin(); Inst != BB.end(); Inst++) {
              Instruction& inst = *Inst;

              // only if inst is CallInst can dyn_cast sucess. otherwise dyn_cast will return nullptr 
              if (CallInst* call_inst = dyn_cast<CallInst>(&inst)) {
                  Function* fn = call_inst->getCalledFunction(); //get the called funciton

                  if (fn == NULL) {
                      Value* v = call_inst->getCalledOperand(); //get the called value
                      fn = dyn_cast<Function>(v->stripPointerCasts());
                      if (fn == NULL) {
                          continue;
                      }
                  }

                  std::string fn_name = fn->getName().str();
                  if (fn_name.compare(0, 5, "llvm.") == 0) { //filter function w.r.t llvm
                      continue;
                  }

                  if (is_syscal(fn_name)) {
                      syscall_num++;
                      //outs() << fn_name << "\n";
                  }
              }
          }
          /* Get RiskNum finished */




          /* Make up cur_loc */

          unsigned int cur_loc = AFL_R(MAP_SIZE); // generate a new cur_loc  

          ConstantInt* CurLoc = ConstantInt::get(Int32Ty, cur_loc);

          /* Load prev_loc */

          LoadInst* PrevLoc = IRB.CreateLoad(AFLPrevLoc);
          PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
          Value* PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty());

          /* Load SHM pointer */

          LoadInst* MapPtr = IRB.CreateLoad(AFLMapPtr);
          MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
          Value* MapPtrIdx =
              IRB.CreateGEP(MapPtr, IRB.CreateXor(PrevLocCasted, CurLoc));

          /* Update bitmap */

          LoadInst* Counter = IRB.CreateLoad(MapPtrIdx);
          Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
          Value* Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));
          IRB.CreateStore(Incr, MapPtrIdx)
              ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

          /* Set prev_loc to cur_loc >> 1 */

          StoreInst* Store =
              IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> 1), AFLPrevLoc);
          Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

          //@@RiskNum
          if (syscall_num >= 0) {
              ConstantInt* Syscall_num =
                  ConstantInt::get(LargestType, (unsigned)syscall_num);

              /* Add risk to shm[MAPSIZE] */

              Value* MapRisk_NumPtr = IRB.CreateBitCast(
                  IRB.CreateGEP(MapPtr, MapRiskNumLoc), LargestType->getPointerTo());

              LoadInst* MapRisk = IRB.CreateLoad(MapRisk_NumPtr);
              MapRisk->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

              // modify + write back
              Value* IncrRN = IRB.CreateAdd(MapRisk, Syscall_num);
              IRB.CreateStore(IncrRN, MapRisk_NumPtr)
                  ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

              
              
              // Actually, you don't need this!

              
              
              /* Increase count at shm[MAPSIZE + (4 or 8)], count the number of block that have been met */   
              //Value* MapCntPtr = IRB.CreateBitCast(
              //    IRB.CreateGEP(MapPtr, MapCntLoc), LargestType->getPointerTo()
              //);  //create a pointer that point to: Base + Offset

              //LoadInst* MapCnt = IRB.CreateLoad(MapCntPtr);
              //MapCnt->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

              //Value* IncrCnt = IRB.CreateAdd(MapCnt, One); // add 1 at a time
              //IRB.CreateStore(IncrCnt, MapCntPtr)
              //    ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

          }


          inst_blocks++;

      }
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
