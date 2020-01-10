/******************************************************************************
 * Copyright (c) 2017 Philipp Schubert.
 * All rights reserved. This program and the accompanying materials are made
 * available under the terms of LICENSE.txt.
 *
 * Contributors:
 *     Philipp Schubert and others
 *****************************************************************************/

/*
 * PointsToGraph.cpp
 *
 *  Created on: 08.02.2017
 *      Author: pdschbrt
 */
#include <llvm/ADT/SetVector.h>
#include <llvm/Analysis/CFLSteensAliasAnalysis.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Value.h>

#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/copy.hpp>
#include <boost/graph/depth_first_search.hpp>
#include <boost/graph/graph_utility.hpp>
#include <boost/graph/graphviz.hpp>
#include <boost/log/sources/record_ostream.hpp>

#include <phasar/PhasarLLVM/Pointer/PointsToGraph.h>

#include <phasar/Utils/GraphExtensions.h>
#include <phasar/Utils/LLVMShorthands.h>
#include <phasar/Utils/Logger.h>
#include <phasar/Utils/Macros.h>
#include <phasar/Utils/PAMMMacros.h>

using namespace std;
using namespace psr;

namespace psr {

struct PointsToGraph::allocation_site_dfs_visitor : boost::default_dfs_visitor {
  // collect the allocation sites that are found
  std::set<const llvm::Value *> &allocation_sites;
  // keeps track of the current path
  std::vector<vertex_t> visitor_stack;
  // the call stack that can be matched against the visitor stack
  const std::vector<const llvm::Instruction *> &call_stack;

  allocation_site_dfs_visitor(
      std::set<const llvm::Value *> &allocation_sizes,
      const vector<const llvm::Instruction *> &call_stack)
      : allocation_sites(allocation_sizes), call_stack(call_stack) {}

  template <typename Vertex, typename Graph>
  void discover_vertex(Vertex u, const Graph &g) {
    visitor_stack.push_back(u);
  }

  template <typename Vertex, typename Graph>
  void finish_vertex(Vertex u, const Graph &g) {
    auto &lg = lg::get();
    // check for stack allocation
    if (const llvm::AllocaInst *Alloc =
            llvm::dyn_cast<llvm::AllocaInst>(g[u].value)) {
      // If the call stack is empty, we completely ignore the calling context
      if (matches_stack(g) || call_stack.empty()) {
        LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                      << "Found stack allocation: " << llvmIRToString(Alloc));
        allocation_sites.insert(g[u].value);
      }
    }
    // check for heap allocation
    if (llvm::isa<llvm::CallInst>(g[u].value) ||
        llvm::isa<llvm::InvokeInst>(g[u].value)) {
      llvm::ImmutableCallSite CS(g[u].value);
      if (CS.getCalledFunction() != nullptr &&
          HeapAllocationFunctions.count(
              CS.getCalledFunction()->getName().str())) {
        // If the call stack is empty, we completely ignore the calling
        // context
        if (matches_stack(g) || call_stack.empty()) {
          LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                        << "Found heap allocation: "
                        << llvmIRToString(CS.getInstruction()));
          allocation_sites.insert(g[u].value);
        }
      }
    }
    visitor_stack.pop_back();
  }

  template <typename Graph> bool matches_stack(const Graph &g) {
    size_t call_stack_idx = 0;
    for (size_t i = 0, j = 1;
         i < visitor_stack.size() && j < visitor_stack.size(); ++i, ++j) {
      auto e = boost::edge(visitor_stack[i], visitor_stack[j], g);
      if (g[e.first].value == nullptr)
        continue;
      if (g[e.first].value !=
          call_stack[call_stack.size() - call_stack_idx - 1]) {
        return false;
      }
      call_stack_idx++;
    }
    return true;
  }
};

struct PointsToGraph::reachability_dfs_visitor : boost::default_dfs_visitor {
  std::set<vertex_t> &points_to_set;
  reachability_dfs_visitor(set<vertex_t> &result) : points_to_set(result) {}
  template <typename Vertex, typename Graph>
  void finish_vertex(Vertex u, const Graph &g) {
    points_to_set.insert(u);
  }
};

void PrintResults(const char *Msg, bool P, const llvm::Value *V1,
                  const llvm::Value *V2, const llvm::Module *M) {
  if (P) {
    std::string o1, o2;
    {
      llvm::raw_string_ostream os1(o1), os2(o2);
      V1->printAsOperand(os1, true, M);
      V2->printAsOperand(os2, true, M);
    }

    if (o2 < o1)
      std::swap(o1, o2);
    llvm::errs() << "  " << Msg << ":\t" << o1 << ", " << o2 << "\n";
  }
}

void PrintModRefResults(const char *Msg, bool P, llvm::Instruction *I,
                        llvm::Value *Ptr, llvm::Module *M) {
  if (P) {
    llvm::errs() << "  " << Msg << ":  Ptr: ";
    Ptr->printAsOperand(llvm::errs(), true, M);
    llvm::errs() << "\t<->" << *I << '\n';
  }
}

void PrintModRefResults(const char *Msg, bool P, llvm::CallSite CSA,
                        llvm::CallSite CSB, llvm::Module *M) {
  if (P) {
    llvm::errs() << "  " << Msg << ": " << *CSA.getInstruction() << " <-> "
                 << *CSB.getInstruction() << '\n';
  }
}

void PrintLoadStoreResults(const char *Msg, bool P, const llvm::Value *V1,
                           const llvm::Value *V2, const llvm::Module *M) {
  if (P) {
    llvm::errs() << "  " << Msg << ": " << *V1 << " <-> " << *V2 << '\n';
  }
}

// points-to graph internal stuff

PointsToGraph::VertexProperties::VertexProperties(const llvm::Value *v)
    : value(v) {
  // WARNING: equivalent to llvmIRToString
  // WARNING 2 : really really really slow (yes it is)
  // // save the ir code
  // llvm::raw_string_ostream rso(ir_code);
  // value->print(rso);
  // // retrieve the id
  // if (const llvm::Instruction *inst =
  //         llvm::dyn_cast<llvm::Instruction>(value)) {
  //   id = stoull(llvm::cast<llvm::MDString>(
  //                   inst->getMetadata(MetaDataKind)->getOperand(0))
  //                   ->getString()
  //                   .str());
  // }
}

PointsToGraph::EdgeProperties::EdgeProperties(const llvm::Value *v) : value(v) {
  // save the ir code
  // WARNING: equivalent to llvmIRToString
  // WARNING 2 : really really really slow (yes it is)
  // if (v) {
  //   llvm::raw_string_ostream rso(ir_code);
  //   value->print(rso);
  //   // retrieve the id
  //   if (const llvm::Instruction *inst =
  //           llvm::dyn_cast<llvm::Instruction>(value)) {
  //     id = stoull(llvm::cast<llvm::MDString>(
  //                     inst->getMetadata(MetaDataKind)->getOperand(0))
  //                     ->getString()
  //                     .str());
  //   }
  // }
}

// points-to graph stuff

const boost::container::flat_set<string>
    PointsToGraph::HeapAllocationFunctions = {"_Znwm", "_Znam", "malloc",
                                              "calloc", "realloc"};
namespace {
void addEdgeFromAliasResult(const PointsToGraph::vertex_t first,
                            const PointsToGraph::vertex_t second,
                            const llvm::AliasResult aliasResult,
                            bool onlyConsiderMustAlias,
                            PointsToGraph::graph_t &ptg) {
  switch (aliasResult) {
  case llvm::NoAlias:
    break;
  case llvm::MayAlias:
    if (onlyConsiderMustAlias) {
      break;
    }
    // no break
  case llvm::PartialAlias:
    if (onlyConsiderMustAlias) {
      break;
    }
    // no break
  case llvm::MustAlias:
    boost::add_edge(first, second, ptg);
    break;
  }
}
} // namespace

PointsToGraph::PointsToGraph(llvm::AAResults &AA, llvm::Function *F,
                             bool onlyConsiderMustAlias) {
  PAMM_GET_INSTANCE;
  auto &lg = lg::get();
  LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                << "Analyzing function: " << F->getName().str());
  ContainedFunctions.insert(F);
  bool PrintNoAlias, PrintMayAlias, PrintPartialAlias, PrintMustAlias;
  PrintNoAlias = PrintMayAlias = PrintPartialAlias = PrintMustAlias = true;
  // ModRef information
  bool PrintNoModRef, PrintMod, PrintRef, PrintModRef;
  PrintNoModRef = PrintMod = PrintRef = PrintModRef = false;
  const llvm::DataLayout &DL = F->getParent()->getDataLayout();
  llvm::SetVector<const llvm::Value *> Pointers;

  for (auto &I : F->args())
    if (I.getType()->isPointerTy()) // Add all pointer arguments.
      Pointers.insert(&I);

  for (llvm::inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
    if (I->getType()->isPointerTy()) // Add all pointer instructions.
      Pointers.insert(&*I);
    llvm::Instruction &Inst = *I;
    if (auto CS = llvm::CallSite(&Inst)) {
      llvm::Value *Callee = CS.getCalledValue();
      // Skip actual functions for direct function calls.
      if (!llvm::isa<llvm::Function>(Callee) && isInterestingPointer(Callee))
        Pointers.insert(Callee);
      // Consider formals.
      for (llvm::Use &DataOp : CS.data_ops())
        if (isInterestingPointer(DataOp))
          Pointers.insert(DataOp);
    } else {
      // Consider all operands.
      for (llvm::Instruction::op_iterator OI = Inst.op_begin(),
                                          OE = Inst.op_end();
           OI != OE; ++OI)
        if (isInterestingPointer(*OI))
          Pointers.insert(*OI);
    }
  }
  INC_COUNTER("GS Pointer", Pointers.size(), PAMM_SEVERITY_LEVEL::Core);

  //  llvm::errs() << "Function: " << F->getName() << ": " << Pointers.size()
  //               << " pointers, " << CallSites.size() << " call sites\n";

  // make vertices for all pointers
  for (const auto &pointer : Pointers) {
    auto vertex = boost::add_vertex(ptg);
    value_vertex_map.insert(std::make_pair(pointer, vertex));
    ptg[vertex] = VertexProperties(pointer);
  }

  // iterate over the worklist, and run the full (n^2)/2 disambiguations
  for (auto I1 = value_vertex_map.begin(), E = value_vertex_map.end(); I1 != E;
       ++I1) {
    llvm::Type *I1ElTy =
        llvm::cast<llvm::PointerType>(I1->first->getType())->getElementType();
    const uint64_t I1Size = I1ElTy->isSized()
                                ? DL.getTypeStoreSize(I1ElTy)
                                : llvm::MemoryLocation::UnknownSize;
    for (auto I2 = value_vertex_map.begin(); I2 != I1; ++I2) {

      llvm::Type *I2ElTy =
          llvm::cast<llvm::PointerType>(I2->first->getType())->getElementType();
      const uint64_t I2Size = I2ElTy->isSized()
                                  ? DL.getTypeStoreSize(I2ElTy)
                                  : llvm::MemoryLocation::UnknownSize;
      auto aliasResult = AA.alias(llvm::MemoryLocation(I1->first, I1Size),
                                  llvm::MemoryLocation(I2->first, I2Size));
      addEdgeFromAliasResult(I1->second, I2->second, aliasResult,
                             onlyConsiderMustAlias, ptg);
    }
  }
}

bool PointsToGraph::isInterestingPointer(llvm::Value *V) {
  return V->getType()->isPointerTy() &&
         !llvm::isa<llvm::ConstantPointerNull>(V);
}

vector<pair<unsigned, const llvm::Value *>>
PointsToGraph::getPointersEscapingThroughParams() {
  vector<pair<unsigned, const llvm::Value *>> escaping_pointers;
  for (pair<vertex_iterator_t, vertex_iterator_t> vp = boost::vertices(ptg);
       vp.first != vp.second; ++vp.first) {
    if (const llvm::Argument *arg =
            llvm::dyn_cast<llvm::Argument>(ptg[*vp.first].value)) {
      escaping_pointers.push_back(make_pair(arg->getArgNo(), arg));
    }
  }
  return escaping_pointers;
}

vector<const llvm::Value *>
PointsToGraph::getPointersEscapingThroughReturns() const {
  vector<const llvm::Value *> escaping_pointers;
  for (pair<vertex_iterator_t, vertex_iterator_t> vp = boost::vertices(ptg);
       vp.first != vp.second; ++vp.first) {
    for (auto user : ptg[*vp.first].value->users()) {
      if (llvm::isa<llvm::ReturnInst>(user)) {
        escaping_pointers.push_back(ptg[*vp.first].value);
      }
    }
  }
  return escaping_pointers;
}

vector<const llvm::Value *>
PointsToGraph::getPointersEscapingThroughReturnsForFunction(
    const llvm::Function *F) const {
  vector<const llvm::Value *> escaping_pointers;
  for (pair<vertex_iterator_t, vertex_iterator_t> vp = boost::vertices(ptg);
       vp.first != vp.second; ++vp.first) {
    for (auto user : ptg[*vp.first].value->users()) {
      if (auto R = llvm::dyn_cast<llvm::ReturnInst>(user)) {
        if (R->getFunction() == F)
          escaping_pointers.push_back(ptg[*vp.first].value);
      }
    }
  }
  return escaping_pointers;
}

set<const llvm::Value *> PointsToGraph::getReachableAllocationSites(
    const llvm::Value *V, vector<const llvm::Instruction *> CallStack) {
  set<const llvm::Value *> alloc_sites;
  allocation_site_dfs_visitor alloc_vis(alloc_sites, CallStack);
  vector<boost::default_color_type> color_map(boost::num_vertices(ptg));
  boost::depth_first_visit(
      ptg, value_vertex_map[V], alloc_vis,
      boost::make_iterator_property_map(color_map.begin(),
                                        boost::get(boost::vertex_index, ptg),
                                        color_map[0]));
  return alloc_sites;
}

bool PointsToGraph::containsValue(llvm::Value *V) {
  pair<vertex_iterator_t, vertex_iterator_t> vp;
  for (vp = boost::vertices(ptg); vp.first != vp.second; ++vp.first)
    if (ptg[*vp.first].value == V)
      return true;
  return false;
}

set<const llvm::Type *>
PointsToGraph::computeTypesFromAllocationSites(set<const llvm::Value *> AS) {
  set<const llvm::Type *> types;
  // an allocation site can either be an AllocaInst or a call to an allocating
  // function
  for (auto V : AS) {
    if (const llvm::AllocaInst *alloc = llvm::dyn_cast<llvm::AllocaInst>(V)) {
      types.insert(alloc->getAllocatedType());
    } else {
      // usually if an allocating function is called, it is immediately
      // bit-casted
      // to the desired allocated value and hence we can determine it from the
      // destination type of that cast instruction.
      for (auto user : V->users()) {
        if (const llvm::BitCastInst *cast =
                llvm::dyn_cast<llvm::BitCastInst>(user)) {
          types.insert(cast->getDestTy());
        }
      }
    }
  }
  return types;
}

set<const llvm::Value *> PointsToGraph::getPointsToSet(const llvm::Value *V) {
  PAMM_GET_INSTANCE;
  INC_COUNTER("[Calls] getPointsToSet", 1, PAMM_SEVERITY_LEVEL::Full);
  START_TIMER("PointsTo-Set Computation", PAMM_SEVERITY_LEVEL::Full);
  set<vertex_t> reachable_vertices;
  reachability_dfs_visitor vis(reachable_vertices);
  vector<boost::default_color_type> color_map(boost::num_vertices(ptg));
  boost::depth_first_visit(
      ptg, value_vertex_map[V], vis,
      boost::make_iterator_property_map(color_map.begin(),
                                        boost::get(boost::vertex_index, ptg),
                                        color_map[0]));
  set<const llvm::Value *> result;
  for (auto vertex : reachable_vertices) {
    result.insert(ptg[vertex].value);
  }
  PAUSE_TIMER("PointsTo-Set Computation", PAMM_SEVERITY_LEVEL::Full);
  ADD_TO_HISTOGRAM("Points-to", result.size(), 1, PAMM_SEVERITY_LEVEL::Full);
  return result;
}

bool PointsToGraph::representsSingleFunction() {
  return ContainedFunctions.size() == 1;
}

void PointsToGraph::print() {
  cout << "PointsToGraph for ";
  for (const auto &fname : ContainedFunctions) {
    cout << fname->getName().str() << " ";
  }
  cout << "\n";
  boost::print_graph(ptg,
                     boost::get(&PointsToGraph::VertexProperties::id, ptg));
}

void PointsToGraph::print() const {
  cout << "PointsToGraph for ";
  for (const auto &fname : ContainedFunctions) {
    cout << fname->getName().str() << " ";
  }
  cout << "\n";
  boost::print_graph(ptg,
                     boost::get(&PointsToGraph::VertexProperties::id, ptg));
}

void PointsToGraph::printAsDot(const string &filename) {
  ofstream ofs(filename);
  boost::write_graphviz(ofs, ptg,
                        boost::make_label_writer(boost::get(
                            &PointsToGraph::VertexProperties::id, ptg)),
                        boost::make_label_writer(boost::get(
                            &PointsToGraph::EdgeProperties::id, ptg)));
}

json PointsToGraph::getAsJson() {
  json J;
  vertex_iterator vi_v, vi_v_end;
  out_edge_iterator ei, ei_end;
  // iterate all graph vertices
  for (boost::tie(vi_v, vi_v_end) = boost::vertices(ptg); vi_v != vi_v_end;
       ++vi_v) {
    J[PhasarConfig::JsonPointToGraphID()][llvmIRToString(ptg[*vi_v].value)];
    // iterate all out edges of vertex vi_v
    for (boost::tie(ei, ei_end) = boost::out_edges(*vi_v, ptg); ei != ei_end;
         ++ei) {
      J[PhasarConfig::JsonPointToGraphID()][llvmIRToString(ptg[*vi_v].value)] +=
          llvmIRToString(ptg[boost::target(*ei, ptg)].value);
    }
  }
  return J;
}

void PointsToGraph::printValueVertexMap() {
  for (const auto &entry : value_vertex_map) {
    cout << entry.first << " <---> " << entry.second << endl;
  }
}

void PointsToGraph::mergeWith(const PointsToGraph &Other,
                              const llvm::Function *F) {
  if (ContainedFunctions.insert(F).second) {
    mergeGraph(Other);
  }
}

void PointsToGraph::mergeWith(
    const PointsToGraph &Other,
    const vector<pair<llvm::ImmutableCallSite, const llvm::Function *>>
        &Calls) {

  mergeGraph(Other);
  for (const auto &call : Calls) {
    ContainedFunctions.insert(call.second);
    mergeCallSite(call.first, call.second);
  }
}

void PointsToGraph::mergeWith(PointsToGraph &Other,
                              const llvm::ImmutableCallSite &CS,
                              const llvm::Function *F) {
  std::cout << "$$Merging in: " << F->getName().str() << std::endl;
  mergeWith(Other, F);
  mergeCallSite(CS, F);
}

void PointsToGraph::mergeGraph(const PointsToGraph &Other) {
  typedef graph_t::vertex_descriptor vertex_t;
  typedef std::map<vertex_t, vertex_t> vertex_map_t;
  vertex_map_t oldToNewVertexMapping;
  boost::associative_property_map<vertex_map_t> vertexMapWrapper(
      oldToNewVertexMapping);
  boost::copy_graph(Other.ptg, ptg, boost::orig_to_copy(vertexMapWrapper));

  for (const auto &otherValues : Other.value_vertex_map) {
    auto mappingIter = oldToNewVertexMapping.find(otherValues.second);
    if (mappingIter != oldToNewVertexMapping.end()) {
      value_vertex_map.insert(
          make_pair(otherValues.first, mappingIter->second));
    }
  }
}

void PointsToGraph::mergeCallSite(const llvm::ImmutableCallSite &CS,
                                  const llvm::Function *F) {
  auto formalArgRange = F->args();
  auto formalIter = formalArgRange.begin();
  auto mapEnd = value_vertex_map.end();
  for (const auto &arg : CS.args()) {
    const llvm::Argument *Formal = &*formalIter++;
    auto argMapIter = value_vertex_map.find(arg);
    auto formalMapIter = value_vertex_map.find(Formal);
    if (argMapIter != mapEnd && formalMapIter != mapEnd) {
      boost::add_edge(argMapIter->second, formalMapIter->second,
                      CS.getInstruction(), ptg);
    }
    if (formalIter == formalArgRange.end())
      break;
  }

  for (auto Formal : getPointersEscapingThroughReturnsForFunction(F)) {
    auto instrMapIter = value_vertex_map.find(CS.getInstruction());
    auto formalMapIter = value_vertex_map.find(Formal);
    if (instrMapIter != mapEnd && formalMapIter != mapEnd) {
      boost::add_edge(instrMapIter->second, formalMapIter->second,
                      CS.getInstruction(), ptg);
    }
  }
}

unsigned PointsToGraph::getNumOfVertices() { return boost::num_vertices(ptg); }

unsigned PointsToGraph::getNumOfEdges() { return boost::num_edges(ptg); }

} // namespace psr
