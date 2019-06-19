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
#include "clang/AST/OperationKinds.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Stmt.h"
#include "clang/Basic/LangOptions.h"
#include "clang/Basic/SourceLocation.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Tooling/Core/Replacement.h"
#include "llvm/ADT/None.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/Error.h"

namespace clang {
namespace clangd {
namespace {
// class to store information about the Expr that is being extracted
class Extract {
public:
  Extract(const clang::Expr *Expr, const SelectionTree::Node *Node);
  // checks if any variable in our Expr references the declarations in Scope
  const clang::Expr *getExpr() const;
  const SelectionTree::Node *getNode() const;
  bool needBraces(const Stmt *InsertionPoint, const SourceManager &SM) const;
  bool isSubExprOf(const clang::Stmt *Body, const SourceManager &SM) const;
  bool canInsertBefore(const Stmt *InsertionPoint,
                         const SourceManager &SM) const;
  tooling::Replacement replaceWithVar(std::string VarName,
                                      const ASTContext &Ctx) const;
  tooling::Replacement insertDeclaration(std::string VarName,
                                         const Stmt *InsertionPoint,
                                         const ASTContext &Ctx) const;
private:
  const clang::Expr *Expr;
  const SelectionTree::Node *Node;
  std::vector<clang::Decl *> ReferencedDecls;
  std::vector<clang::Decl *> getReferencedDecls();
};
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
  Expected<Effect> apply(const Selection &Inputs) override;
  std::string title() const override;
  Intent intent() const override { return Refactor; }

private:
  // the expression to extract
  const Extract *Target = nullptr;
  // the statement before which variable will be extracted to
  const clang::Stmt *InsertionPoint = nullptr;
};
REGISTER_TWEAK(ExtractVariable)
Extract::Extract(const clang::Expr *Expr, const SelectionTree::Node *Node)
    : Expr(Expr), Node(Node) {
  ReferencedDecls = getReferencedDecls();
}

const clang::Expr *Extract::getExpr() const { return Expr; }
const SelectionTree::Node *Extract::getNode() const { return Node; }
std::vector<clang::Decl *> Extract::getReferencedDecls() {
  // RAV subclass to find all DeclRefs in a given Stmt
  class FindDeclRefsVisitor
      : public clang::RecursiveASTVisitor<FindDeclRefsVisitor> {
  public:
    std::vector<Decl *> ReferencedDecls;
    bool VisitDeclRefExpr(DeclRefExpr *DeclRef) { // NOLINT
      ReferencedDecls.push_back(DeclRef->getDecl());
      return true;
    }
  };
  FindDeclRefsVisitor Visitor;
  Visitor.TraverseStmt(const_cast<Stmt *>(dyn_cast<Stmt>(Expr)));
  return Visitor.ReferencedDecls;
}
// check whether the Expr is a sub expression of the Body Stmt
bool Extract::isSubExprOf(const clang::Stmt *Body,
                          const SourceManager &SM) const {
  SourceRange BodyRng = Body->getSourceRange();
  SourceRange TargetRng = Node->ASTNode.getSourceRange();
  return SM.isPointWithin(TargetRng.getBegin(), BodyRng.getBegin(),
                          BodyRng.getEnd());
}
// Returns true if we will need braces after extraction
bool Extract::needBraces(const Stmt *InsertionPoint,
                         const SourceManager &SM) const {
  llvm::SmallVector<const clang::Stmt *, 2> Bodies;
  if (const ForStmt *Stmt = llvm::dyn_cast_or_null<ForStmt>(InsertionPoint))
    Bodies.push_back(Stmt->getBody());
  else if (const WhileStmt *Stmt =
               llvm::dyn_cast_or_null<WhileStmt>(InsertionPoint))
    Bodies.push_back(Stmt->getBody());
  else if (const DoStmt *Stmt = llvm::dyn_cast_or_null<DoStmt>(InsertionPoint))
    Bodies.push_back(Stmt->getBody());
  else if (const CaseStmt *Stmt =
               llvm::dyn_cast_or_null<CaseStmt>(InsertionPoint))
    Bodies.push_back(Stmt->getSubStmt());
  else if (const DefaultStmt *Stmt =
               llvm::dyn_cast_or_null<DefaultStmt>(InsertionPoint))
    Bodies.push_back(Stmt->getSubStmt());
  else if (const IfStmt *Stmt = llvm::dyn_cast_or_null<IfStmt>(InsertionPoint))
    Bodies.insert(Bodies.end(), {Stmt->getThen(), Stmt->getElse()});
  for (const clang::Stmt *Body : Bodies)
    if (Body && isSubExprOf(Body, SM))
      return true;
  return false;
}

// checks whether extracting before InsertionPoint will take a
// variable out of scope
bool Extract::canInsertBefore(const Stmt *InsertionPoint,
                                const SourceManager &SM) const {
  if (!InsertionPoint)
    return true;
  SourceLocation ScopeBegin = InsertionPoint->getBeginLoc();
  SourceLocation ScopeEnd = InsertionPoint->getEndLoc();
  for (const Decl *ReferencedDecl : ReferencedDecls) {
    if (SM.isPointWithin(ReferencedDecl->getBeginLoc(), ScopeBegin, ScopeEnd) &&
        SM.isPointWithin(ReferencedDecl->getEndLoc(), ScopeBegin, ScopeEnd))
      return false;
  }
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
// we also check if doing the extraction will take a variable out of scope
static const clang::Stmt *getInsertionPoint(const Extract *Target,
                                            const SourceManager &SM) {

  for (const SelectionTree::Node *CurNode = Target->getNode(); CurNode->Parent;
       CurNode = CurNode->Parent) {
    const clang::Stmt *Ancestor = CurNode->Parent->ASTNode.get<Stmt>();
    const clang::Stmt *InsertionPoint = CurNode->ASTNode.get<Stmt>();
    // give up if extraction will take a variable out of scope
    if (!Target->canInsertBefore(InsertionPoint, SM))
      break;
    if (Ancestor) {
      if (isa<CompoundStmt>(Ancestor))
        return InsertionPoint;
      // We will need more functionality here later on
      if (Target->needBraces(Ancestor, SM))
        break;
      // give up if it's a Case Statement constant
      if (isa<CaseStmt>(Ancestor))
        break;
    }
  }
  return nullptr;
}
// returns the replacement for substituting the extraction with VarName
tooling::Replacement Extract::replaceWithVar(std::string VarName,
                                             const ASTContext &Ctx) const {
  const SourceManager &SM = Ctx.getSourceManager();
  const llvm::Optional<SourceRange> ExtractionRng =
      toHalfOpenFileRange(SM, Ctx.getLangOpts(), getExpr()->getSourceRange());
  unsigned ExtractionLength = SM.getFileOffset(ExtractionRng->getEnd()) -
                              SM.getFileOffset(ExtractionRng->getBegin());
  return tooling::Replacement(SM, ExtractionRng->getBegin(), ExtractionLength,
                              VarName);
  // insert new variable declaration
  // replace expression with variable name
}
// returns the Replacement for declaring a new variable storing the extraction
tooling::Replacement Extract::insertDeclaration(std::string VarName,
                                                const Stmt *InsertionPoint,
                                                const ASTContext &Ctx) const {
  const SourceManager &SM = Ctx.getSourceManager();
  const llvm::Optional<SourceRange> ExtractionRng =
      toHalfOpenFileRange(SM, Ctx.getLangOpts(), getExpr()->getSourceRange());
  llvm::StringRef ExtractionCode = toSourceCode(SM, *ExtractionRng);
  const SourceLocation InsertionLoc =
      toHalfOpenFileRange(SM, Ctx.getLangOpts(),
                          InsertionPoint->getSourceRange())
          ->getBegin();
  // FIXME: Replace auto with explicit type and add &/&& as necessary
  std::string ExtractedVarDecl =
      std::string("auto ") + VarName + " = " + ExtractionCode.str() + "; ";
  return tooling::Replacement(SM, InsertionLoc, 0, ExtractedVarDecl);
}

// FIXME: case constant refactoring
// FIXME: if, while, else, for, case, default statements without curly braces
// and their combinations
// FIXME: Ignore assignment (a = 1) Expr since it is extracted as dummy = a = 1
bool ExtractVariable::prepare(const Selection &Inputs) {
  const SourceManager &SM = Inputs.AST.getSourceManager();
  const SelectionTree::Node *N = Inputs.ASTSelection.commonAncestor();
  if (!N)
    return false;
  const clang::Expr *Expr = N->ASTNode.get<clang::Expr>();
  if (!Expr)
    return false;
  Target = new Extract(Expr, N);
  InsertionPoint = getInsertionPoint(Target, SM);
  return InsertionPoint != nullptr;
}

Expected<Tweak::Effect> ExtractVariable::apply(const Selection &Inputs) {
  ASTContext &Ctx = Inputs.AST.getASTContext();
  tooling::Replacements Result;
  if (auto Err =
          Result.add(Target->insertDeclaration("dummy", InsertionPoint, Ctx)))
    return std::move(Err);
  if (auto Err = Result.add(Target->replaceWithVar("dummy", Ctx)))
    return std::move(Err);
  return Effect::applyEdit(Result);
}
std::string ExtractVariable::title() const {
  return "Extract subexpression to variable";
}

} // namespace
} // namespace clangd
} // namespace clang
