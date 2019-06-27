//===--- ExtractVariable.cpp ------------------------------------*- C++-*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
#include "ClangdUnit.h"
#include "Logger.h"
#include "Protocol.h"
#include "Selection.h"
#include "SourceCode.h"
#include "refactor/Tweak.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Expr.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Stmt.h"
#include "clang/Basic/LangOptions.h"
#include "clang/Basic/SourceLocation.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Tooling/Core/Replacement.h"
#include "llvm/ADT/None.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/Error.h"

namespace clang {
namespace clangd {
namespace {

//
/// Extracts an expression to the variable dummy
/// Before:
/// int x = 5 + 4 * 3;
///         ^^^^^
/// After:
/// auto dummy = 5 + 4;
/// int x = dummy * 3;
class ExtractVariable : public Tweak {
public:
  const char *id() const override final;
  bool prepare(const Selection &Inputs) override;
  Expected<tooling::Replacements> apply(const Selection &Inputs) override;
  std::string title() const override;

private:
  // the expression to extract
  const clang::Expr *Exp = nullptr;
  // the statement before which variable will be extracted to
  const clang::Stmt *Stm = nullptr;
};
REGISTER_TWEAK(ExtractVariable)

// checks whether any variable in a given expr is declared in the DeclStmt
static bool isDeclaredIn(const DeclStmt *Decl, const Expr *Exp,
                         const SourceManager &M) {

  // RAV subclass to find all DeclRefs in a given Stmt
  class FindDeclRefsVisitor
      : public clang::RecursiveASTVisitor<FindDeclRefsVisitor> {
  public:
    std::vector<DeclRefExpr *> DeclRefExprs;
    bool VisitDeclRefExpr(DeclRefExpr *DeclRef) { // NOLINT
      DeclRefExprs.push_back(DeclRef);
      return true;
    }
  };

  FindDeclRefsVisitor Visitor;
  Visitor.TraverseStmt(const_cast<Stmt *>(dyn_cast<Stmt>(Exp)));
  for (const DeclRefExpr *DeclRef : Visitor.DeclRefExprs) {
    // Beginning location of the ValueDecl of the DeclRef
    auto ValueDeclLoc = DeclRef->getDecl()->getBeginLoc();
    // return true if this ValueDecl location is within the DeclStmt
    if (M.isPointWithin(ValueDeclLoc, Decl->getBeginLoc(), Decl->getEndLoc()))
      return true;
  }
  return false;
}
// check whether the expr denoted by N is a part of the Body Stmt
bool isNodeInside(const Stmt *Body, const SelectionTree::Node *N,
                  const SourceManager &M) {
  if (!Body)
    return false;
  auto BodyRng = Body->getSourceRange();
  SourceRange NodeRng = N->ASTNode.getSourceRange();
  return M.isPointWithin(NodeRng.getBegin(), BodyRng.getBegin(),
                         BodyRng.getEnd());
}
// Returns true if we will need braces after extraction
static bool needBraces(const SelectionTree::Node *N, const Stmt *Stm,
                       const SourceManager &M) {

  if (const ForStmt *Stmt = llvm::dyn_cast_or_null<ForStmt>(Stm))
    return isNodeInside(Stmt->getBody(), N, M);
  if (const WhileStmt *Stmt = llvm::dyn_cast_or_null<WhileStmt>(Stm))
    return isNodeInside(Stmt->getBody(), N, M);
  if (const DoStmt *Stmt = llvm::dyn_cast_or_null<DoStmt>(Stm))
    return isNodeInside(Stmt->getBody(), N, M);
  if (const CaseStmt *Stmt = llvm::dyn_cast_or_null<CaseStmt>(Stm))
    return isNodeInside(Stmt->getSubStmt(), N, M);
  if (const DefaultStmt *Stmt = llvm::dyn_cast_or_null<DefaultStmt>(Stm))
    return isNodeInside(Stmt->getSubStmt(), N, M);
  if (const IfStmt *Stmt = llvm::dyn_cast_or_null<IfStmt>(Stm))
    return isNodeInside(Stmt->getThen(), N, M) ||
           isNodeInside(Stmt->getElse(), N, M);
  return false;
}

// check whether to allow extraction from for(...)
// if we are in the condition/Increment part of a for statement, we must ensure
// that the variables in the expression being extracted are not declared in the
// init of the for statement.
static bool checkForStmt(const ForStmt *F, const Expr *Exp,
                         const SourceManager &M) {
  const Stmt *Init = F->getInit();
  if (!Init || !isa<DeclStmt>(Init))
    return true; // FIXME
  // if any variable in Exp is declared in the DeclStmt, return false
  return !isDeclaredIn(dyn_cast<DeclStmt>(Init), Exp, M);
}

// check whether to allow extraction from a Declaration
static bool checkDeclStmt(const DeclStmt *D, const Expr *Exp,
                          const SourceManager &M) {
  return !isDeclaredIn(D, Exp, M);
}
// checks whether extraction will take a variable out of scope
// TODO: Add more unit tests after SelectionTree ancestor bug is fixed
static bool extractionAllowed(const Stmt *ParStmt, const SelectionTree::Node *N,
                              const SourceManager &M) {
  if (isa<ForStmt>(ParStmt) &&
      !checkForStmt(dyn_cast<ForStmt>(ParStmt), N->ASTNode.get<Expr>(), M))
    return false;
  if (isa<DeclStmt>(ParStmt) &&
      !checkDeclStmt(dyn_cast<DeclStmt>(ParStmt), N->ASTNode.get<Expr>(), M))
    return false;
  return true;
}
// Return the Stmt before which we need to insert the extraction.
// To find the Stmt, we go up the AST Tree and if the Parent of the current Stmt
// is a CompoundStmt, we can extract inside this CompoundStmt just before the
// current Stmt. We ALWAYS insert before a Stmt whose parent is a CompoundStmt
//
// Otherwise if we encounter an if/while/do-while/for/case Stmt, we must check
// whether we are in their "body" or the "condition" part. If we are in the
// "body", that means we need to insert braces i.e. create a CompoundStmt. For
// now, we don't allow extraction if we need to insert braces. Else if we are in
// the "condition" part, we can extract before the if/while/do-while/for/case
// Stmt. Remember that we only insert before a stmt if its Parent Stmt is a
// CompoundStmt, thus we continue looping to find a CompoundStmt.
//
// We have a special case for the Case Stmt constant for which we currently
// don't offer extraction.
//
// If doing the extraction will take a variable out of scope, we give up
//
// If we encounter a LambdaExpr (i.e. we are trying to extract a capture/default
// param argument), we give up. Note that the whole LambdaExpr can still be
// extracted.
//
// If we encounter a CXXMethodDecl (implying that the selected expression is a
// default argument for a method parameter), we give up
static const clang::Stmt *getStmt(const SelectionTree::Node *N,
                                  const SourceManager &M) {
  auto CurN = N;
  while (CurN->Parent) {
    auto ParStmt = CurN->Parent->ASTNode.get<Stmt>();
    if (ParStmt) {
      if (isa<CompoundStmt>(ParStmt)) {
        return CurN->ASTNode.get<Stmt>();
      }
      // We will need more functionality here later on
      if (needBraces(N, ParStmt, M))
        break;
      // give up if it's a Case Statement constant
      if (isa<CaseStmt>(ParStmt) && !isNodeInside(ParStmt, N, M))
        break;
      // give up if extraction will take a variable out of scope
      if (!extractionAllowed(ParStmt, N, M))
        break;
      // Prevent extraction from lambda captures and params
      if (isa<LambdaExpr>(ParStmt))
        break;
    }
    else if (CurN->Parent->ASTNode.get<CXXMethodDecl>())
      break;
    CurN = CurN->Parent;
  }
  return nullptr;
}
// returns the replacement for substituting Exp with VarName
tooling::Replacement replaceExpression(std::string VarName, const Expr *Exp,
                                       const ASTContext &Ctx) {
  auto &M = Ctx.getSourceManager();
  auto ExpRng =
      toHalfOpenFileRange(M, Ctx.getLangOpts(), Exp->getSourceRange());
  auto ExpCode = toSourceCode(M, *ExpRng);
  return tooling::Replacement(M, ExpRng->getBegin(), ExpCode.size(), VarName);
  // insert new variable declaration
  // replace expression with variable name
}
// returns the Replacement for declaring a new variable storing the extracted
// expression
tooling::Replacement insertExtractedVar(std::string VarName, const Stmt *Stm,
                                        const Expr *Exp,
                                        const ASTContext &Ctx) {
  auto &M = Ctx.getSourceManager();
  auto ExpRng =
      toHalfOpenFileRange(M, Ctx.getLangOpts(), Exp->getSourceRange());
  auto ExpCode = toSourceCode(M, *ExpRng);
  auto StmRng =
      toHalfOpenFileRange(M, Ctx.getLangOpts(), Stm->getSourceRange());
  // TODO: Replace auto with explicit type
  std::string ExtractedVarDecl =
      std::string("auto ") + VarName + " = " + ExpCode.str() + "; ";
  return tooling::Replacement(M, StmRng->getBegin(), 0, ExtractedVarDecl);
}

// FIXME(Bug in selection tree): doesn't work for int a = 6, b = 8;
// FIXME: case constant refactoring
// FIXME: if, while, else, for, case, default statements without curly braces
// and their combinations
// FIXME: Ignore assignment (a = 1) Expr since it is extracted as dummy = a = 1
bool ExtractVariable::prepare(const Selection &Inputs) {
  const auto &M = Inputs.AST.getSourceManager();
  const SelectionTree::Node *N = Inputs.ASTSelection.commonAncestor();
  if (!N)
    return false;
  Exp = N->ASTNode.get<Expr>();
  if (!Exp)
    return false;
  return (Stm = getStmt(N, M));
}

Expected<tooling::Replacements>
ExtractVariable::apply(const Selection &Inputs) {
  auto &Ctx = Inputs.AST.getASTContext();
  tooling::Replacements Result;
  if (auto Err = Result.add(insertExtractedVar("dummy", Stm, Exp, Ctx)))
    return std::move(Err);
  if (auto Err = Result.add(replaceExpression("dummy", Exp, Ctx)))
    return std::move(Err);
  return Result;
}

std::string ExtractVariable::title() const {
  return "Extract to dummy variable";
}

} // namespace
} // namespace clangd
} // namespace clang
