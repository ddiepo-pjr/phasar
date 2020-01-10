/******************************************************************************
 * Copyright (c) 2017 Philipp Schubert.
 * All rights reserved. This program and the accompanying materials are made
 * available under the terms of LICENSE.txt.
 *
 * Contributors:
 *     Philipp Schubert and others
 *****************************************************************************/

/*
 * LLVMBasedICFG.h
 *
 *  Created on: 09.09.2016
 *      Author: pdschbrt
 */

#ifndef PHASAR_PHASARLLVM_CONTROLFLOW_LLVMBASEDICFG_H_
#define PHASAR_PHASARLLVM_CONTROLFLOW_LLVMBASEDICFG_H_

#include <functional>
#include <iosfwd>
#include <map>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include <boost/graph/adjacency_list.hpp>

#include <phasar/PhasarLLVM/ControlFlow/ICFG.h>
#include <phasar/PhasarLLVM/ControlFlow/LLVMBasedCFG.h>
#include <phasar/PhasarLLVM/Pointer/PointsToGraph.h>

namespace llvm {
class Instruction;
class Function;
class Module;
class Instruction;
class BitCastInst;
} // namespace llvm

namespace psr {

class Resolver;
class ProjectIRDB;
class LLVMTypeHierarchy;

class LLVMBasedICFG
    : public ICFG<const llvm::Instruction *, const llvm::Function *>,
      public virtual LLVMBasedCFG {
  friend class LLVMBasedBackwardsICFG;

private:
  CallGraphAnalysisType CGType;
  LLVMTypeHierarchy &CH;
  ProjectIRDB &IRDB;
  PointsToGraph WholeModulePTG;
  std::unordered_set<const llvm::Function *> VisitedFunctions;

  // The VertexProperties for our call-graph.
  struct VertexProperties {
    const llvm::Function *function = nullptr;
    std::string functionName;
    bool isDeclaration;
    VertexProperties() = default;
    VertexProperties(const llvm::Function *f, bool isDecl = false);
  };

  // The EdgeProperties for our call-graph.
  struct EdgeProperties {
    const llvm::Instruction *callsite = nullptr;
    // std::string ir_code;
    size_t id = 0;
    EdgeProperties() = default;
    EdgeProperties(const llvm::Instruction *i);
  };

  /// Specify the type of graph to be used.
  typedef boost::adjacency_list<boost::vecS, boost::vecS, boost::bidirectionalS,
                                VertexProperties, EdgeProperties>
      bidigraph_t;

  // Let us have some handy typedefs.
  typedef boost::graph_traits<bidigraph_t>::vertex_descriptor vertex_t;
  typedef boost::graph_traits<bidigraph_t>::vertex_iterator vertex_iterator;
  typedef boost::graph_traits<bidigraph_t>::edge_descriptor edge_t;
  typedef boost::graph_traits<bidigraph_t>::out_edge_iterator out_edge_iterator;
  typedef boost::graph_traits<bidigraph_t>::in_edge_iterator in_edge_iterator;

  /// The call graph.
  bidigraph_t cg;

  /// Maps functions to the corresponding vertex id.
  std::unordered_map<const llvm::Function *, vertex_t> function_vertex_map;

  void constructionWalker(const llvm::Function *F, Resolver *resolver,
                          bool isRecursiveCall);

  struct dependency_visitor;

public:
  LLVMBasedICFG(LLVMTypeHierarchy &STH, ProjectIRDB &IRDB);

  LLVMBasedICFG(LLVMTypeHierarchy &STH, ProjectIRDB &IRDB,
                CallGraphAnalysisType CGType,
                const std::vector<std::string> &EntryPoints = {"main"});

  LLVMBasedICFG(LLVMTypeHierarchy &STH, ProjectIRDB &IRDB,
                const llvm::Module &M, CallGraphAnalysisType CGType,
                std::vector<std::string> EntryPoints = {});

  ~LLVMBasedICFG() override = default;

  std::set<const llvm::Function *> getAllMethods();

  bool isVirtualFunctionCall(llvm::ImmutableCallSite CS);

  const llvm::Function *getMethod(const std::string &fun) override;

  std::set<const llvm::Function *>
  getCalleesOfCallAt(const llvm::Instruction *n) override;

  std::set<const llvm::Instruction *>
  getCallersOf(const llvm::Function *m) override;

  std::set<const llvm::Instruction *>
  getCallsFromWithin(const llvm::Function *m) override;

  std::set<const llvm::Instruction *>
  getStartPointsOf(const llvm::Function *m) override;

  std::set<const llvm::Instruction *>
  getExitPointsOf(const llvm::Function *fun) override;

  std::set<const llvm::Instruction *>
  getReturnSitesOfCallAt(const llvm::Instruction *n) override;

  bool isCallStmt(const llvm::Instruction *stmt) override;

  std::set<const llvm::Instruction *> allNonCallStartNodes() override;

  const llvm::Instruction *getLastInstructionOf(const std::string &name);

  std::vector<const llvm::Instruction *>
  getAllInstructionsOfFunction(const std::string &name);

  void mergeWith(const LLVMBasedICFG &other);

  bool isPrimitiveFunction(const std::string &name);

  void print();

  void printAsDot(const std::string &filename);

  void printInternalPTGAsDot(const std::string &filename);

  json getAsJson() override;

  unsigned getNumOfVertices();

  unsigned getNumOfEdges();

  void exportPATBCJSON();

  PointsToGraph &getWholeModulePTG();

  std::vector<std::string> getDependencyOrderedFunctions();
};

} // namespace psr

#endif
