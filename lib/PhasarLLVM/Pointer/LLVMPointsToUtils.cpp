/******************************************************************************
 * Copyright (c) 2020 Philipp Schubert.
 * All rights reserved. This program and the accompanying materials are made
 * available under the terms of LICENSE.txt.
 *
 * Contributors:
 *     Philipp Schubert and others
 *****************************************************************************/

#include "llvm/IR/Constants.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Value.h"

#include "phasar/PhasarLLVM/Pointer/LLVMPointsToUtils.h"

namespace {

unsigned long parseLine(char* line){
    // This assumes that a digit will be found and the line ends in " Kb".
    size_t i = strlen(line);
    const char* p = line;
    while (*p <'0' || *p > '9') p++;
    line[i-3] = '\0';
    return std::stoul(p);
}

}

namespace psr {

bool isInterestingPointer(const llvm::Value *V) {
  return V->getType()->isPointerTy() &&
         !llvm::isa<llvm::ConstantPointerNull>(V);
}


std::pair<unsigned long, unsigned long> getRssAndVss() {
  FILE* file = fopen("/proc/self/status", "r");
  int result = -1;
  char line[128];

  std::pair<unsigned long, unsigned long> rssAndVss = std::make_pair(0, 0);
  while (fgets(line, 128, file) != NULL){
      if (strncmp(line, "VmSize:", 7) == 0) {
          rssAndVss.second = parseLine(line);
          if (rssAndVss.first) break;
      }
      if (strncmp(line, "VmRSS:", 6) == 0) {
          rssAndVss.first = parseLine(line);
          if (rssAndVss.second) break;
      }
  }
  fclose(file);
  return rssAndVss;
}


const std::set<llvm::StringRef> HeapAllocatingFunctions{
    "malloc", "calloc", "realloc", "_Znwm", "_Znam"};

} // namespace psr
