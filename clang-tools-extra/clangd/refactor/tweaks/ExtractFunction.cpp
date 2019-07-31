//===--- ExtractFunction.cpp -------------------------------------*- C++-*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Extracts statements to a new function and replaces the statements with a
// call to the new function.
// Before:
//   void f(int a) {
//     [[if(a < 5)
//       a = 5;]]
//   }
// After:
//   void extracted(int &a) {
//     if(a < 5)
//       a = 5;
//   }
//   void f(int a) {
//     extracted(a);
//   }
//
// - Only extract statements
// - Extracts from non-templated free functions only.
// - Parameters are const only if the declaration was const
//   - Always passed by l-value reference
// - No return
// - Cannot move declarations before extracting
// - Doesn't check for broken control flow
//
// 1. ExtractFunction is the tweak subclass
//    - Prepare does basic analysis of the selection and is therefore fast.
//      Successful prepare doesn't always mean we can apply the tweak.
//    - Apply does a more detailed analysis and can be slower. In case of
//      failure, we let the user know that we are unable to perform extraction.
// 2. ExtractionZone store information about the range being extracted and the
//    enclosing function.
// 3. NewFunction stores properties of the extracted function and provides
//    methods for rendering it.
// 4. CapturedZoneInfo uses a RAV to capture information about the extraction
//    like declarations, existing return statements, broken control flow, etc.
// 5. getExtractedFunction is responsible for analyzing the CapturedZoneInfo and
//    creating a NewFunction.
// Design Doc at <TODO: Share design doc>
//===----------------------------------------------------------------------===//

#include "ClangdUnit.h"
#include "Logger.h"
#include "Selection.h"
#include "SourceCode.h"
#include "refactor/Tweak.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Stmt.h"
#include "clang/Basic/LangOptions.h"
#include "clang/Basic/SourceLocation.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Lex/Lexer.h"
#include "clang/Tooling/Core/Replacement.h"
#include "clang/Tooling/Refactoring/Extract/SourceExtraction.h"
#include "llvm/ADT/None.h"
#include "llvm/ADT/Optional.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/iterator_range.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/Error.h"

namespace clang {
namespace clangd {
namespace {

using Node = SelectionTree::Node;

// ExtractionZone is the part of code that is being extracted.
// EnclosingFunction is the function/method inside which the zone lies.
// We split the file into 4 parts relative to extraction zone.
enum class ZoneRelative {
  Before,     // Before Zone and inside EnclosingFunction.
  Inside,     // Inside Zone.
  After,      // After Zone and inside EnclosingFunction.
  OutsideFunc // Outside EnclosingFunction.
};

// The ExtractionZone class forms a view of the code wrt to Zone.
// A RootStmt is a statement that's fully selected including all it's children
// and it's parent is unselected.
// We only support extraction of RootStmts since it allows us to extract without
// having to change the selection range. Also, this means that any scope that
// begins in selection range, ends in selection range and any scope that begins
// outside the selection range, ends outside as well.
struct ExtractionZone {
  // Parent of RootStatements being extracted.
  const Node *Parent = nullptr;
  // The half-open file range of the code being extracted.
  SourceRange ZoneRange;
  // The function inside which our zone resides.
  const Node *EnclosingFunction = nullptr;
  // The half-open file range of the enclosing function.
  SourceRange EnclosingFuncRange;
  const SourceManager &SM;

  ExtractionZone(const SourceManager &SM) : SM(SM){};
  // Classify the location type for a given location.
  ZoneRelative getRelationToZone(SourceLocation Loc) const;
  SourceLocation getInsertionPoint() const {
    return EnclosingFuncRange.getBegin();
  }
  const Node *getLastRootStmt() const {
    return Parent ? Parent->Children.back() : nullptr;
  }
};

// TODO: check if this works properly with macros.
ZoneRelative ExtractionZone::getRelationToZone(SourceLocation Loc) const {
  if (!SM.isPointWithin(Loc, EnclosingFuncRange.getBegin(),
                        EnclosingFuncRange.getEnd()))
    return ZoneRelative::OutsideFunc;
  if (Loc < ZoneRange.getBegin())
    return ZoneRelative::Before;
  if (Loc < ZoneRange.getEnd())
    return ZoneRelative::Inside;
  return ZoneRelative::After;
}

bool isStmtInExtractionZone(const Stmt *S, const ExtractionZone &ExtZone) {
  return ExtZone.getRelationToZone(S->getBeginLoc()) == ZoneRelative::Inside;
}
// Finds the function in which the zone lies.
const Node *computeEnclosingFunction(const Node *CommonAnc) {
  // Walk up the SelectionTree until we find a function Decl
  for (const Node *CurNode = CommonAnc; CurNode; CurNode = CurNode->Parent) {
    // Don't extract from lambdas
    if (CurNode->ASTNode.get<LambdaExpr>())
      return nullptr;
    if (CurNode->ASTNode.get<FunctionDecl>()) {
      // FIXME: Support extraction from methods.
      if (CurNode->ASTNode.get<CXXMethodDecl>())
        return nullptr;
      // FIXME: Support extraction from templated functions.
      if (CurNode->Parent->ASTNode.get<FunctionTemplateDecl>())
        return nullptr;
      return CurNode;
    }
  }
  return nullptr;
}

// Find the union of source ranges of all child nodes of Parent. Returns an
// invalid SourceRange if it fails to do so.
SourceRange rangeUnionOfChildren(const Node *Parent, const SourceManager &SM,
                                 const LangOptions &LangOpts) {
  SourceRange SR;
  for (const Node *Child : Parent->Children) {
    auto ChildFileRange =
        toHalfOpenFileRange(SM, LangOpts, Child->ASTNode.getSourceRange());
    if (!ChildFileRange)
      return SourceRange();
    if (SR.isInvalid())
      SR = *ChildFileRange;
    else
      SR.setEnd(ChildFileRange->getEnd());
  }
  return SR;
}
// Compute the range spanned by the enclosing function.
// FIXME: check if EnclosingFunction has any attributes as the AST doesn't
// always store the source range of the attributes and thus we end up extracting
// between the attributes and the EnclosingFunction.
SourceRange computeEnclosingFuncRange(const Node *EnclosingFunction,
                                      const SourceManager &SM,
                                      const LangOptions &LangOpts) {
  return *toHalfOpenFileRange(SM, LangOpts,
                              EnclosingFunction->ASTNode.getSourceRange());
}

// Check if all child nodes of (unselected) Parent are RootStmts.
bool hasOnlyRootStmtChildren(const Node *Parent) {
  for (const Node *Child : Parent->Children) {
    // Ensure every child is a statement.
    if (!Child->ASTNode.get<Stmt>())
      return false;
    // We don't want to extract a partially selected subtree.
    if (Child->Selected == SelectionTree::Partial)
      return false;
    // Only DeclStmt can be an unselected child since VarDecls claim the entire
    // selection range in selectionTree.
    if (Child->Selected == SelectionTree::Selection::Unselected &&
        !Child->ASTNode.get<DeclStmt>())
      return false;
  }
  return true;
}

// Returns the (unselected) parent of all RootStmts given the commonAncestor.
const Node *getParentOfRootStmts(const Node *CommonAnc) {
  if (!CommonAnc)
    return nullptr;
  switch (CommonAnc->Selected) {
  case SelectionTree::Selection::Unselected:
    return hasOnlyRootStmtChildren(CommonAnc) ? CommonAnc : nullptr;
  case SelectionTree::Selection::Partial:
    // Treat Partially selected VarDecl as completely selected since
    // SelectionTree doesn't always select VarDecls correctly.
    if (!CommonAnc->ASTNode.get<VarDecl>())
      return nullptr;
    LLVM_FALLTHROUGH;
  case SelectionTree::Selection::Complete:
    // If the Common Ancestor is completely selected, then it's a root statement
    // and its parent will be unselected.
    const Node *Parent = CommonAnc->Parent;
    // If parent is a DeclStmt, even though it's unselected, we consider it a
    // root statement and return its parent.
    return Parent->ASTNode.get<DeclStmt>() ? Parent->Parent : Parent;
  }
}

// FIXME: Check we're not extracting from the initializer/condition of a control
// flow structure.
// FIXME: Check that we don't extract the compound statement of the
// enclosingFunction.
std::shared_ptr<ExtractionZone> getExtractionZone(const Node *CommonAnc,
                                                  const SourceManager &SM,
                                                  const LangOptions &LangOpts) {
  std::shared_ptr<ExtractionZone> ExtZone =
      std::make_shared<ExtractionZone>(SM);
  ExtZone->Parent = getParentOfRootStmts(CommonAnc);
  if (!ExtZone->Parent || ExtZone->Parent->Children.empty())
    return nullptr;
  ExtZone->EnclosingFunction = computeEnclosingFunction(ExtZone->Parent);
  if (!ExtZone->EnclosingFunction)
    return nullptr;
  ExtZone->EnclosingFuncRange =
      computeEnclosingFuncRange(ExtZone->EnclosingFunction, SM, LangOpts);
  // Don't extract expressions.
  if (ExtZone->Parent->Children.size() == 1 &&
      ExtZone->getLastRootStmt()->ASTNode.get<Expr>())
    return nullptr;
  // Since all children of Parent are RootStmts, ZoneRange will be union of
  // SourceRange of all it's children.
  ExtZone->ZoneRange = rangeUnionOfChildren(ExtZone->Parent, SM, LangOpts);
  return ExtZone;
}

// Stores information about the extracted function and provides methods for
// rendering it.
struct NewFunction {
  struct Parameter {
    std::string Name;
    QualType TypeInfo;
    bool IsConst;
    bool PassByReference;
    unsigned OrderPriority; // Lower value parameters are preferred first.
    std::string render(bool WithTypeAndQualifiers) const;
    bool operator<(const Parameter &Other) const {
      return OrderPriority < Other.OrderPriority;
    }
  };
  std::string Name = "extracted";
  std::string ReturnType;
  std::vector<Parameter> Parameters;
  SourceRange BodyRange;
  SourceLocation InsertionPoint;
  // Decides whether the extracted function body and the function call need a
  // semicolon after extraction.
  tooling::ExtractionSemicolonPolicy SemicolonPolicy;
  NewFunction(SourceRange BodyRange, SourceLocation InsertionPoint,
              tooling::ExtractionSemicolonPolicy SemicolonPolicy,
              const SourceManager &SM)
      : BodyRange(BodyRange), InsertionPoint(InsertionPoint),
        SemicolonPolicy(SemicolonPolicy), SM(SM){};
  // Render the call for this function.
  std::string renderCall() const;
  // Render the definition for this function.
  std::string renderDefinition() const;
  // Add a new parameter for the function.
  void addParam(llvm::StringRef Name, QualType TypeInfo, bool IsConst,
                bool IsReference, unsigned OrderPriority);

private:
  const SourceManager &SM;
  std::string renderParameters(bool WithTypeAndQualifiers) const;
  // Generate the function body.
  std::string getFuncBody() const;
};

std::string NewFunction::renderParameters(bool WithTypeAndQualifiers) const {
  std::string Result;
  bool NeedCommaBefore = false;
  for (const Parameter &P : Parameters) {
    if (NeedCommaBefore)
      Result += ", ";
    NeedCommaBefore = true;
    Result += P.render(WithTypeAndQualifiers);
  }
  return Result;
}
std::string NewFunction::renderCall() const {
  return Name + "(" + renderParameters(false) + ")" +
         (SemicolonPolicy.isNeededInOriginalFunction() ? ";" : "");
}
std::string NewFunction::renderDefinition() const {
  return ReturnType + " " + Name + "(" + renderParameters(true) + ")" + " {\n" +
         getFuncBody() + "\n}\n";
}

std::string NewFunction::getFuncBody() const {
  // FIXME: Generate tooling::Replacements instead of std::string to
  // - hoist decls
  // - add return statement
  // - Add semicolon
  return toSourceCode(SM, BodyRange).str() +
         (SemicolonPolicy.isNeededInExtractedFunction() ? ";" : "");
}

void NewFunction::addParam(llvm::StringRef Name, QualType TypeInfo,
                           bool IsConst, bool IsReference,
                           unsigned OrderPriority) {
  Parameters.push_back({Name, TypeInfo, IsConst, IsReference, OrderPriority});
}
// FIXME: Generate better types names. e.g. remove class from object types.
std::string spellType(QualType TypeInfo) {
  return TypeInfo.getUnqualifiedType().getNonReferenceType().getAsString();
};

std::string NewFunction::Parameter::render(bool WithTypeAndQualifiers) const {
  std::string Result;
  if (WithTypeAndQualifiers) {
    if (IsConst)
      Result += "const ";
    Result += spellType(TypeInfo) + " ";
    if (PassByReference)
      Result += "&";
  }
  Result += Name;
  return Result;
}

// Stores captured information about Extraction Zone.
struct CapturedZoneInfo {
  struct DeclInformation {
    const Decl *TheDecl = nullptr;
    ZoneRelative DeclaredIn;
    // Stores the numbering of this declaration(i for the i-th Decl)
    unsigned DeclIndex;
    bool IsReferencedInZone = false;
    bool IsReferencedInPostZone = false;
    // FIXME: Capture mutation information
    DeclInformation(){};
    DeclInformation(const Decl *TheDecl, ZoneRelative DeclaredIn,
                    unsigned DeclIndex)
        : TheDecl(TheDecl), DeclaredIn(DeclaredIn), DeclIndex(DeclIndex){};
    // Marks the occurence of a reference for this declaration
    void markOccurence(ZoneRelative ReferenceLoc);
  };
  // Maps Decls to their DeclInfo
  llvm::DenseMap<const Decl *, DeclInformation> DeclInfoMap;
  // True if there is a return statement in zone.
  bool HasReturnStmt = false;
  // For now we just care whether there exists a break/continue in zone.
  bool HasBreakOrContinue = false;
  // FIXME: capture TypeAliasDecl and UsingDirectiveDecl
  // FIXME: Capture type information as well.
  // Return reference for a Decl, adding it if not already present.
  DeclInformation &getDeclInformationFor(const Decl *D,
                                         const ExtractionZone &ExtZone);
};

CapturedZoneInfo::DeclInformation &
CapturedZoneInfo::getDeclInformationFor(const Decl *D,
                                        const ExtractionZone &ExtZone) {
  // Adding a new Decl (The declarationIndex will be the size of the
  // DeclInfoMap).
  if (DeclInfoMap.find(D) == DeclInfoMap.end())
    DeclInfoMap.insert(
        {D, DeclInformation(D, ExtZone.getRelationToZone(D->getLocation()),
                            DeclInfoMap.size())});
  return DeclInfoMap[D];
}

void CapturedZoneInfo::DeclInformation::markOccurence(
    ZoneRelative ReferenceLoc) {
  switch (ReferenceLoc) {
  case ZoneRelative::Inside:
    IsReferencedInZone = true;
    break;
  case ZoneRelative::After:
    IsReferencedInPostZone = true;
    break;
  default:
    break;
  }
}

// Captures information from Extraction Zone
CapturedZoneInfo captureZoneInfo(const ExtractionZone &ExtZone) {
  // We use the ASTVisitor instead of using the selection tree since we need to
  // find references in the PostZone as well.
  // FIXME: Check which statements we don't allow to extract.
  class ExtractionZoneVisitor
      : public clang::RecursiveASTVisitor<ExtractionZoneVisitor> {
  public:
    ExtractionZoneVisitor(const ExtractionZone &ExtZone) : ExtZone(ExtZone) {
      TraverseDecl(const_cast<FunctionDecl *>(
          ExtZone.EnclosingFunction->ASTNode.get<FunctionDecl>()));
    }
    bool VisitDecl(Decl *D) { // NOLINT
      // Create new DeclInfo
      Info.getDeclInformationFor(D, ExtZone);
      return true;
    }
    bool VisitDeclRefExpr(DeclRefExpr *DRE) { // NOLINT
      // Find the corresponding Decl and mark it's occurence.
      auto &DeclInfo = Info.getDeclInformationFor(DRE->getDecl(), ExtZone);
      DeclInfo.markOccurence(ExtZone.getRelationToZone(DRE->getLocation()));
      // FIXME: check if reference mutates the Decl being referred.
      return true;
    }
    bool VisitReturnStmt(ReturnStmt *Return) { // NOLINT
      if (isStmtInExtractionZone(Return, ExtZone))
        Info.HasReturnStmt = true;
      return true;
    }

    // FIXME: check for broken break/continue only.
    bool VisitBreakStmt(BreakStmt *Break) { // NOLINT
      if (isStmtInExtractionZone(Break, ExtZone))
        Info.HasBreakOrContinue = true;
      return true;
    }
    bool VisitContinueStmt(ContinueStmt *Continue) { // NOLINT
      if (isStmtInExtractionZone(Continue, ExtZone))
        Info.HasBreakOrContinue= true;
      return true;
    }
    CapturedZoneInfo Info;
    const ExtractionZone &ExtZone;
  };
  ExtractionZoneVisitor Visitor(ExtZone);
  return std::move(Visitor.Info);
}

// Adds parameters to ExtractedFunc.
// Returns true if able to find the parameters successfully and no hoisting
// needed.
bool createParameters(NewFunction &ExtractedFunc,
                      const CapturedZoneInfo &CapturedInfo) {

  for (const auto &KeyVal : CapturedInfo.DeclInfoMap) {
    const auto &DeclInfo = KeyVal.second;
    const ValueDecl *VD = dyn_cast_or_null<ValueDecl>(DeclInfo.TheDecl);
    bool WillBeParameter = (DeclInfo.DeclaredIn == ZoneRelative::Before &&
                            DeclInfo.IsReferencedInZone) ||
                           (DeclInfo.DeclaredIn == ZoneRelative::Inside &&
                            DeclInfo.IsReferencedInPostZone);
    // Check if the Decl will become a parameter.
    if (!WillBeParameter)
      continue;
    // Parameter specific checks.
    // Can't parameterise if the Decl isn't a ValueDecl or is a FunctionDecl
    // (this includes the case of recursive call to EnclosingFunc in Zone).
    if (!VD || dyn_cast_or_null<FunctionDecl>(DeclInfo.TheDecl))
      return false;
    // FIXME: Need better qualifier checks: check mutated status for
    // DeclInformation
    bool IsConstDecl = VD->getType().isConstQualified();
    // FIXME: check if parameter will be a non l-value reference.
    // FIXME: We don't want to always pass variables of types like int,
    // pointers, etc by reference.
    bool IsReference = true;
    // We use the index of declaration as the ordering priority for parameters.
    ExtractedFunc.addParam(VD->getName(), VD->getType(), IsConstDecl,
                           IsReference, DeclInfo.DeclIndex);
    // If a Decl was Declared in zone and referenced in post zone, it needs
    // to be hoisted (we bail out in that case).
    // FIXME: Support Decl Hoisting.
    if (DeclInfo.DeclaredIn == ZoneRelative::Inside &&
        DeclInfo.IsReferencedInPostZone)
      return false;
  }
  llvm::sort(ExtractedFunc.Parameters);
  return true;
}

// Clangd uses open ranges while ExtractionSemicolonPolicy (in Clang Tooling)
// uses closed ranges. Generates the semicolon policy for the extraction and
// extends the ZoneRange if necessary.
tooling::ExtractionSemicolonPolicy
getSemicolonPolicy(ExtractionZone &ExtZone, const SourceManager &SM,
                   const LangOptions &LangOpts) {
  // Get closed ZoneRange.
  SourceRange FuncBodyRange = {ExtZone.ZoneRange.getBegin(),
                               ExtZone.ZoneRange.getEnd().getLocWithOffset(-1)};
  auto SemicolonPolicy = tooling::ExtractionSemicolonPolicy::compute(
      ExtZone.getLastRootStmt()->ASTNode.get<Stmt>(), FuncBodyRange, SM,
      LangOpts);
  // Update ZoneRange.
  ExtZone.ZoneRange.setEnd(FuncBodyRange.getEnd().getLocWithOffset(1));
  return SemicolonPolicy;
}

// Generate return type for ExtractedFunc. Return false if unable to do so.
bool generateReturnProperties(NewFunction &ExtractedFunc,
                              const CapturedZoneInfo &CapturedInfo) {

  // FIXME: Use Existing Return statements (if present)
  // FIXME: Generate new return statement if needed.
  if (CapturedInfo.HasReturnStmt)
    return false;
  ExtractedFunc.ReturnType = "void";
  return true;
}

// FIXME: add support for adding other function return types besides void.
// FIXME: assign the value returned by non void extracted function.
llvm::Optional<NewFunction> getExtractedFunction(ExtractionZone &ExtZone,
                                                 const SourceManager &SM,
                                                 const LangOptions &LangOpts) {
  CapturedZoneInfo CapturedInfo = captureZoneInfo(ExtZone);
  // Bail out if any break of continue exists
  // FIXME: check for broken control flow only
  if (CapturedInfo.HasBreakOrContinue)
    return llvm::None;
  auto SemicolonPolicy = getSemicolonPolicy(ExtZone, SM, LangOpts);
  NewFunction ExtractedFunc(ExtZone.ZoneRange, ExtZone.getInsertionPoint(),
                            std::move(SemicolonPolicy), SM);
  if (!createParameters(ExtractedFunc, CapturedInfo))
    return llvm::None;
  if (!generateReturnProperties(ExtractedFunc, CapturedInfo))
    return llvm::None;
  return ExtractedFunc;
}

class ExtractFunction : public Tweak {
public:
  const char *id() const override final;

  bool prepare(const Selection &Inputs) override;
  Expected<Effect> apply(const Selection &Inputs) override;
  std::string title() const override { return "Extract to function"; }
  Intent intent() const override { return Refactor; }

private:
  std::shared_ptr<ExtractionZone> ExtZone;
};

REGISTER_TWEAK(ExtractFunction)
tooling::Replacement replaceWithFuncCall(const NewFunction &ExtractedFunc,
                                         const SourceManager &SM,
                                         const LangOptions &LangOpts) {
  std::string FuncCall = ExtractedFunc.renderCall();
  return tooling::Replacement(
      SM, CharSourceRange(ExtractedFunc.BodyRange, false), FuncCall, LangOpts);
}

tooling::Replacement createFunctionDefinition(const NewFunction &ExtractedFunc,
                                              const SourceManager &SM) {
  std::string FunctionDef = ExtractedFunc.renderDefinition();
  return tooling::Replacement(SM, ExtractedFunc.InsertionPoint, 0, FunctionDef);
}

bool ExtractFunction::prepare(const Selection &Inputs) {
  const Node *CommonAnc = Inputs.ASTSelection.commonAncestor();
  const SourceManager &SM = Inputs.AST.getSourceManager();
  const LangOptions &LangOpts = Inputs.AST.getASTContext().getLangOpts();
  ExtZone = getExtractionZone(CommonAnc, SM, LangOpts);
  return (bool)ExtZone;
}

Expected<Tweak::Effect> ExtractFunction::apply(const Selection &Inputs) {
  const SourceManager &SM = Inputs.AST.getSourceManager();
  const LangOptions &LangOpts = Inputs.AST.getASTContext().getLangOpts();
  auto ExtractedFunc = getExtractedFunction(*ExtZone, SM, LangOpts);
  // FIXME: Add more types of errors.
  if (!ExtractedFunc)
    return llvm::createStringError(llvm::inconvertibleErrorCode(),
                                   +"Too complex to extract.");
  tooling::Replacements Result;
  if (auto Err = Result.add(createFunctionDefinition(*ExtractedFunc, SM)))
    return std::move(Err);
  if (auto Err = Result.add(replaceWithFuncCall(*ExtractedFunc, SM, LangOpts)))
    return std::move(Err);
  return Effect::applyEdit(Result);
}

} // namespace
} // namespace clangd
} // namespace clang
