//=======- UncountedLocalVarsChecker.cpp -------------------------*- C++ -*-==//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "ASTUtils.h"
#include "DiagOutputUtils.h"
#include "PtrTypesSemantics.h"
#include "clang/AST/CXXInheritance.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/ParentMapContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Basic/SourceLocation.h"
#include "clang/StaticAnalyzer/Checkers/BuiltinCheckerRegistration.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugReporter.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "llvm/ADT/DenseSet.h"
#include <optional>

using namespace clang;
using namespace ento;

namespace {

class RawPtrRefLocalVarsChecker
    : public Checker<check::ASTDecl<TranslationUnitDecl>> {
  BugType Bug;
  mutable BugReporter *BR;

public:
  RawPtrRefLocalVarsChecker(const char* description)
      : Bug(this, description, "WebKit coding guidelines") {}

  virtual std::optional<bool> isUnsafePtr(const clang::Type* T) const = 0;
  virtual const char *ptrKind() const = 0;

  void checkASTDecl(const TranslationUnitDecl *TUD, AnalysisManager &MGR,
                    BugReporter &BRArg) const {
    BR = &BRArg;

    // The calls to checkAST* from AnalysisConsumer don't
    // visit template instantiations or lambda classes. We
    // want to visit those, so we make our own RecursiveASTVisitor.
    struct LocalVisitor : public RecursiveASTVisitor<LocalVisitor> {
      const RawPtrRefLocalVarsChecker *Checker;

      TrivialFunctionAnalysis TFA;

      using Base = RecursiveASTVisitor<LocalVisitor>;

      explicit LocalVisitor(const RawPtrRefLocalVarsChecker *Checker)
          : Checker(Checker) {
        assert(Checker);
      }

      bool shouldVisitTemplateInstantiations() const { return true; }
      bool shouldVisitImplicitCode() const { return false; }

      bool VisitVarDecl(VarDecl *V) {
        auto *Init = V->getInit();
        if (Init && V->isLocalVarDecl())
          Checker->visitVarDecl(V, Init);
        return true;
      }

      bool VisitBinaryOperator(const BinaryOperator *BO) {
        if (BO->isAssignmentOp()) {
          if (auto *VarRef = dyn_cast<DeclRefExpr>(BO->getLHS())) {
            if (auto *V = dyn_cast<VarDecl>(VarRef->getDecl()))
              Checker->visitVarDecl(V, BO->getRHS());
          }
        }
        return true;
      }

      bool TraverseIfStmt(IfStmt *IS) {
        if (!TFA.isTrivial(IS))
          return Base::TraverseIfStmt(IS);
        return true;
      }

      bool TraverseForStmt(ForStmt *FS) {
        if (!TFA.isTrivial(FS))
          return Base::TraverseForStmt(FS);
        return true;
      }

      bool TraverseCXXForRangeStmt(CXXForRangeStmt *FRS) {
        if (!TFA.isTrivial(FRS))
          return Base::TraverseCXXForRangeStmt(FRS);
        return true;
      }

      bool TraverseWhileStmt(WhileStmt *WS) {
        if (!TFA.isTrivial(WS))
          return Base::TraverseWhileStmt(WS);
        return true;
      }

      bool TraverseCompoundStmt(CompoundStmt *CS) {
        if (!TFA.isTrivial(CS))
          return Base::TraverseCompoundStmt(CS);
        return true;
      }
    };

    LocalVisitor visitor(this);
    visitor.TraverseDecl(const_cast<TranslationUnitDecl *>(TUD));
  }

  void visitVarDecl(const VarDecl *V, const Expr *Value) const {
    if (shouldSkipVarDecl(V))
      return;

    const auto *ArgType = V->getType().getTypePtr();
    if (!ArgType)
      return;

    std::optional<bool> IsUncountedPtr = isUnsafePtr(ArgType);
    if (IsUncountedPtr && *IsUncountedPtr) {
      if (hasGuardianVariable(V, Value))
        return;
      reportBug(V, Value);
    }
  }

  bool shouldSkipVarDecl(const VarDecl *V) const {
    assert(V);
    return BR->getSourceManager().isInSystemHeader(V->getLocation());
  }

  void reportBug(const VarDecl *V, const Expr *Value) const {
    assert(V);
    SmallString<100> Buf;
    llvm::raw_svector_ostream Os(Buf);

    if (dyn_cast<ParmVarDecl>(V)) {
      Os << "Assignment to an " << ptrKind() << " parameter ";
      printQuotedQualifiedName(Os, V);
      Os << " is unsafe.";

      PathDiagnosticLocation BSLoc(Value->getExprLoc(), BR->getSourceManager());
      auto Report = std::make_unique<BasicBugReport>(Bug, Os.str(), BSLoc);
      Report->addRange(Value->getSourceRange());
      BR->emitReport(std::move(Report));
    } else {
      if (V->hasLocalStorage())
        Os << "Local variable ";
      else if (V->isStaticLocal())
        Os << "Static local variable ";
      else if (V->hasGlobalStorage())
        Os << "Global variable ";
      else
        Os << "Variable ";
      printQuotedQualifiedName(Os, V);
      Os << " is " << ptrKind() << " and unsafe.";

      PathDiagnosticLocation BSLoc(V->getLocation(), BR->getSourceManager());
      auto Report = std::make_unique<BasicBugReport>(Bug, Os.str(), BSLoc);
      Report->addRange(V->getSourceRange());
      BR->emitReport(std::move(Report));
    }
  }
};

class UncountedLocalVarsChecker final : public RawPtrRefLocalVarsChecker {
public:
  UncountedLocalVarsChecker()
      : RawPtrRefLocalVarsChecker("Uncounted raw pointer or reference not "
                                  "provably backed by ref-counted variable") {}
  std::optional<bool> isUnsafePtr(const clang::Type* T) const final {
    return isUncountedPtr(T);
  }
  const char *ptrKind() const final { return "uncounted"; }
};

class UncheckedLocalVarsChecker final : public RawPtrRefLocalVarsChecker {
public:
  UncheckedLocalVarsChecker()
      : RawPtrRefLocalVarsChecker("Unchecked raw pointer or reference not "
                                  "provably backed by checked variable") {}
  std::optional<bool> isUnsafePtr(const clang::Type* T) const final {
    return isUncheckedPtr(T);
  }
  const char *ptrKind() const final { return "unchecked"; }
};

} // namespace

void ento::registerUncountedLocalVarsChecker(CheckerManager &Mgr) {
  Mgr.registerChecker<UncountedLocalVarsChecker>();
}

bool ento::shouldRegisterUncountedLocalVarsChecker(const CheckerManager &) {
  return true;
}

void ento::registerUncheckedLocalVarsChecker(CheckerManager &Mgr) {
  Mgr.registerChecker<UncheckedLocalVarsChecker>();
}

bool ento::shouldRegisterUncheckedLocalVarsChecker(const CheckerManager &) {
  return true;
}
