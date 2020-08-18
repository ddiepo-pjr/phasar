/******************************************************************************
 * Copyright (c) 2020 Philipp Schubert.
 * All rights reserved. This program and the accompanying materials are made
 * available under the terms of LICENSE.txt.
 *
 * Contributors:
 *     Philipp Schubert and others
 *****************************************************************************/

#include <iostream>
#include <type_traits>
#include <unordered_set>

#include "llvm/ADT/SetVector.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_os_ostream.h"


#include "phasar/DB/ProjectIRDB.h"
#include "phasar/PhasarLLVM/Pointer/LLVMBasedPointsToAnalysis.h"
#include "phasar/PhasarLLVM/Pointer/LLVMPointsToSet.h"
#include "phasar/PhasarLLVM/Pointer/LLVMPointsToUtils.h"
#include "phasar/Utils/LLVMShorthands.h"
#include "phasar/Utils/Logger.h"

using namespace std;
using namespace psr;

namespace psr {

LLVMPointsToSet::LLVMPointsToSet(ProjectIRDB &IRDB, bool UseLazyEvaluation,
                                 PointerAnalysisType PATy)
    : PTA(IRDB, UseLazyEvaluation, PATy) {
  // TODO handle case of not UseLazyEvaluation
//  if (!UseLazyEvaluation) {
//    for (llvm::Module *M : IRDB.getAllModules()) {
//      for (auto &F : *M) {
//        if (!F.isDeclaration()) {
//          computePointsToSet(&F);
//        }
//      }
//    }
//  }
}

void LLVMPointsToSet::computePointsToSet(const llvm::Value& V) {
  if (const auto* G = llvm::dyn_cast<llvm::GlobalVariable>(&V)) {
    computePointsToSet(*G);
  } else {
    // TODO check if we've already computed
    auto *VF = retrieveFunction(&V);
    if (VF) {
      computePointsToSet(V, *VF);
    }
  }
}

void LLVMPointsToSet::computePointsToSet(const llvm::GlobalVariable& G) {
  // TODO avoid multiple lookups
  auto Search = PointsToSets.find(&G);
  if (Search == PointsToSets.end()) {
    PointsToSets.insert(
        {&G, std::make_shared<std::unordered_set<const llvm::Value *>>()});
    PointsToSets[&G]->insert(&G);
    for (const auto *User : G.users()) {
      computePointsToSet(*User);
      if (User->getType()->isPointerTy()) {
        PointsToSets[&G]->insert(User);
      }
    }
  }
  std::cout << "Computed points-to set for global variable: "
            << llvmIRToString(&G) << '\n';
  for (const auto *Ptr : *PointsToSets[&G]) {
    std::cout << "Ptr: " << llvmIRToString(Ptr) << '\n';
  }
  std::cout << std::endl;
}

#define ONLY_FUNC_PTRS 1

void LLVMPointsToSet::computePointsToSet(const llvm::Value& V, llvm::Function& F) {

  std::shared_ptr<std::unordered_set<const llvm::Value *>> set =
      std::make_shared<std::unordered_set<const llvm::Value *>>();
  auto insertResult = PointsToSets.insert(std::make_pair(&V, set));
  if (!insertResult.second) {
    return;
  }

  if (!V.getType()->isPointerTy()) {
    llvm::raw_os_ostream err(std::cerr);
    err << "Trying to compute points-to for non pointer type: " << V.getName();
    V.getType()->print(err);
    err << "\n";
    return;
  }

  LOG_IF_ENABLE(BOOST_LOG_SEV(lg::get(), DEBUG)
                << "Analyzing function: " << F.getName().str());

  // taken from llvm/Analysis/AliasAnalysisEvaluator.cpp
  llvm::SetVector<llvm::Value *> Pointers;
  for (auto &I : F.args()) {
    if (I.getType()->isPointerTy()
#ifdef ONLY_FUNC_PTRS
        && I.getType()->getPointerElementType()->isFunctionTy()
#endif
        ) { // Add all pointer arguments.
      Pointers.insert(&I);
    }
  }

  for (llvm::inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
    if (I->getType()->isPointerTy()
#ifdef ONLY_FUNC_PTRS
        && I->getType()->getPointerElementType()->isFunctionTy()
#endif
        ) { // Add all pointer instructions.
      Pointers.insert(&*I);
    }
    llvm::Instruction &Inst = *I;
    if (auto *Call = llvm::dyn_cast<llvm::CallBase>(&Inst)) {
      llvm::Value *Callee = Call->getCalledValue();
      // Skip actual functions for direct function calls.
      if (!llvm::isa<llvm::Function>(Callee) && isInterestingPointer(Callee)) {
        Pointers.insert(Callee);
      }
      // Consider formals.
      for (llvm::Use &DataOp : Call->data_ops()) {
        if (isInterestingPointer(DataOp)
#ifdef ONLY_FUNC_PTRS
// Don't filter out non-functions here, as that breaks the ability to distinguish virtual function invokes.
#endif
            ) {
          Pointers.insert(DataOp);
        }
      }
    } else {
      // Consider all operands.
      for (llvm::Instruction::op_iterator OI = Inst.op_begin(),
                                          OE = Inst.op_end();
           OI != OE; ++OI) {
        if (isInterestingPointer(*OI)
#ifdef ONLY_FUNC_PTRS
        && (*OI)->getType()->getPointerElementType()->isFunctionTy()
#endif
            ) {
          Pointers.insert(*OI);
        }
      }
    }
  }
  std::cout << F.getName().str() << " pointer count: " << Pointers.size() << std::endl;

  const llvm::DataLayout &DL = F.getParent()->getDataLayout();
  llvm::Type *inputType =
      llvm::cast<llvm::PointerType>(V.getType())->getElementType();
  const uint64_t inputSize = inputType->isSized()
                              ? DL.getTypeStoreSize(inputType)
                              : llvm::MemoryLocation::UnknownSize;

  size_t aliasCount = 0;

  llvm::AAResults* AA = PTA.getAAResults(&F);
  const auto PointsToSetsEnd = PointsToSets.end();
  for (llvm::Value* valPtr : Pointers)
  {
    if (valPtr == &V)
      continue;

    auto search = PointsToSets.find(valPtr);
    if (search != PointsToSetsEnd)
    {
      if (search->second.get()->count(&V)) {
        set->insert(valPtr);
      }
      continue;
    }

    llvm::Type *I1ElTy =
        llvm::cast<llvm::PointerType>(valPtr->getType())->getElementType();
    const uint64_t I1Size = I1ElTy->isSized()
                                ? DL.getTypeStoreSize(I1ElTy)
                                : llvm::MemoryLocation::UnknownSize;

    switch (AA->alias(&V, inputSize, valPtr, I1Size)) {
      case llvm::NoAlias:
        break;
      case llvm::MayAlias:
        [[fallthrough]];
      case llvm::PartialAlias:
        [[fallthrough]];
      case llvm::MustAlias: {
        set->insert(valPtr);
      }
    }
    ++aliasCount;
    auto memUsage = psr::getRssAndVss();
    const unsigned long oneHundredGigabytes = 100 * 1024 * 1024;
    const unsigned long fiftyGigabytes = 50 * 1024 * 1024;
    if (memUsage.first > fiftyGigabytes || memUsage.second > oneHundredGigabytes) {
      std::cout << "*** RESETTING.  VSS: " << memUsage.second << "kb, RSS:" << memUsage.first << ", count: " << aliasCount << std::endl;
      PTA.clear();
      AA = PTA.getAAResults(&F);
    }
  }
  PTA.clear();
}

bool LLVMPointsToSet::isInterProcedural() const { return false; }

PointerAnalysisType LLVMPointsToSet::getPointerAnalysistype() const {
  return PTA.getPointerAnalysisType();
}

AliasResult LLVMPointsToSet::alias(const llvm::Value *V1, const llvm::Value *V2,
                                   const llvm::Instruction *I) {
  if (V1) {
    computePointsToSet(*V1);
    return PointsToSets[V1]->count(V2) ? AliasResult::MustAlias
                                       : AliasResult::NoAlias;
  }
  return AliasResult::NoAlias;
}

std::shared_ptr<std::unordered_set<const llvm::Value *>>
LLVMPointsToSet::getPointsToSet(const llvm::Value *V,
                                const llvm::Instruction *I) {
  if (!V) {
    return std::make_shared<std::unordered_set<const llvm::Value *>>();
  }

  // TODO so many lookups...
  computePointsToSet(*V);
  if (PointsToSets.find(V) == PointsToSets.end()) {
    return std::make_shared<std::unordered_set<const llvm::Value *>>();
  }
  return PointsToSets[V];
}

std::unordered_set<const llvm::Value *>
LLVMPointsToSet::getReachableAllocationSites(const llvm::Value *V,
                                             const llvm::Instruction *I) {
  std::unordered_set<const llvm::Value *> AllocSites;
  if (!V)
    return AllocSites;

  // TODO so many lookups...
  computePointsToSet(*V);
  const auto PTS = PointsToSets[V];
  for (const auto *P : *PTS) {
    if (const auto *Alloca = llvm::dyn_cast<llvm::AllocaInst>(P)) {
      AllocSites.insert(Alloca);
    }
    if (llvm::isa<llvm::CallInst>(P) || llvm::isa<llvm::InvokeInst>(P)) {
      llvm::ImmutableCallSite CS(P);
      if (CS.getCalledFunction() != nullptr &&
          CS.getCalledFunction()->hasName() &&
          HeapAllocatingFunctions.count(CS.getCalledFunction()->getName())) {
        AllocSites.insert(P);
      }
    }
  }
  return AllocSites;
}

void LLVMPointsToSet::mergeWith(const PointsToInfo &PTI) {
  const LLVMPointsToSet *OtherPTI = dynamic_cast<const LLVMPointsToSet *>(&PTI);
  if (!OtherPTI) {
    llvm::report_fatal_error(
        "LLVMPointsToSet can only be merged with another LLVMPointsToSet!");
  }
  // merge points-to sets
  for (auto &[KeyPtr, Set] : OtherPTI->PointsToSets) {
    bool FoundElemPtr = false;
    for (auto ElemPtr : *Set) {
      // check if a pointer of other is already present in this
      auto Search = PointsToSets.find(ElemPtr);
      if (Search != PointsToSets.end()) {
        // if so, copy its elements
        FoundElemPtr = true;
        Search->second->insert(Set->begin(), Set->end());
        // and reindex its elements
        for (auto ElemPtr : *Set) {
          PointsToSets.insert({ElemPtr, Search->second});
        }
        break;
      }
    }
    // if none of the pointers of a set of other is known in this, we need to
    // perform a copy
    if (!FoundElemPtr) {
      PointsToSets.insert(
          {KeyPtr,
           std::make_shared<std::unordered_set<const llvm::Value *>>(*Set)});
    }
    FoundElemPtr = false;
  }
}

void LLVMPointsToSet::introduceAlias(const llvm::Value *V1,
                                     const llvm::Value *V2,
                                     const llvm::Instruction *I,
                                     AliasResult Kind) {
  if (!V1 || !V2)
    return;

  // before introducing additional aliases make sure we initially computed
  // the aliases for V1 and V2
  // TODO more lookups we don't need!
  computePointsToSet(*V1);
  computePointsToSet(*V2);
  auto SearchV1 = PointsToSets.find(V1);
  auto SearchV2 = PointsToSets.find(V2);
  // better have a safety check
  if (SearchV1 == PointsToSets.end() || SearchV2 == PointsToSets.end()) {
    return;
  }
  auto V1Ptr = SearchV1->first;
  auto V2Ptr = SearchV2->first;
  auto V1Set = SearchV1->second;
  auto V2Set = SearchV2->second;
  // if V1 and V2 are not already aliases, make them aliases
  if (V1Set->find(V2) == V1Set->end()) {
    std::shared_ptr<std::unordered_set<const llvm::Value *>> SmallerSet;
    std::shared_ptr<std::unordered_set<const llvm::Value *>> LargerSet;
    const llvm::Value *SmallerPtr;
    const llvm::Value *LargerPtr;
    if (V1Set->size() < V2Set->size()) {
      SmallerSet = V1Set;
      LargerSet = V2Set;
      SmallerPtr = V1Ptr;
      LargerPtr = V2Ptr;
    } else {
      SmallerSet = V2Set;
      LargerSet = V1Set;
      SmallerPtr = V2Ptr;
      LargerPtr = V1Ptr;
    }
    LargerSet->insert(SmallerSet->begin(), SmallerSet->end());
    // reindex
    for (const auto *Pointer : *SmallerSet) {
      PointsToSets[Pointer] = LargerSet;
    }
    // no we don't need V2Set anymore
    SmallerSet->clear();
    PointsToSets.erase(SmallerPtr);
  }
}

bool LLVMPointsToSet::empty() const { return PointsToSets.empty(); }

nlohmann::json LLVMPointsToSet::getAsJson() const { return ""_json; }

void LLVMPointsToSet::printAsJson(std::ostream &OS) const {}

void LLVMPointsToSet::print(std::ostream &OS) const {
  size_t NumSets = 0;
  for (const auto &[Ptr, PointsToSetPtr] : PointsToSets) {
    ++NumSets;
    OS << '{';
    size_t NumPointers = 0;
    for (const auto &Pointer : *PointsToSetPtr) {
      ++NumPointers;
      OS << llvmIRToString(Pointer);
      // check for last element
      if (NumPointers != PointsToSetPtr->size()) {
        OS << " <-> ";
      }
    }
    if (NumSets != PointsToSets.size()) {
      OS << "}\n";
    } else {
      OS << '}';
    }
  }
}

} // namespace psr
