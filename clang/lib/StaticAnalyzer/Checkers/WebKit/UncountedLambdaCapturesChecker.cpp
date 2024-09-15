//=======- UncountedLambdaCapturesChecker.cpp --------------------*- C++ -*-==//
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
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/StaticAnalyzer/Checkers/BuiltinCheckerRegistration.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugReporter.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "llvm/ADT/DenseSet.h"
#include <optional>

using namespace clang;
using namespace ento;

namespace {
class UncountedLambdaCapturesChecker
    : public Checker<check::ASTDecl<TranslationUnitDecl>> {
private:
  BugType Bug{this, "Lambda capture of uncounted variable",
              "WebKit coding guidelines"};
  mutable BugReporter *BR = nullptr;

public:
  void checkASTDecl(const TranslationUnitDecl *TUD, AnalysisManager &MGR,
                    BugReporter &BRArg) const {
    BR = &BRArg;

    // The calls to checkAST* from AnalysisConsumer don't
    // visit template instantiations or lambda classes. We
    // want to visit those, so we make our own RecursiveASTVisitor.
    struct LocalVisitor : public RecursiveASTVisitor<LocalVisitor> {
      using Base = RecursiveASTVisitor<LocalVisitor>;

      const UncountedLambdaCapturesChecker *Checker;
      llvm::DenseSet<const LambdaExpr *> SafeLambdas;
      llvm::DenseSet<const DeclRefExpr *> SafeDeclRefs;
      llvm::DenseSet<const LambdaExpr *> LambdasWithoutGuardians;
      TrivialFunctionAnalysis TFA;
      bool InFunctionCall = false;

      explicit LocalVisitor(const UncountedLambdaCapturesChecker *Checker)
          : Checker(Checker) {
        assert(Checker);
      }

      bool shouldVisitTemplateInstantiations() const { return true; }
      bool shouldVisitImplicitCode() const { return false; }

      bool TraverseVarDecl(VarDecl *V) {
        if (auto *Init = V->getInit()) {
          if (auto *Lambda = dyn_cast<LambdaExpr>(Init)) {
            bool CapturedVariablesHaveGuardians = true;
            for (const LambdaCapture &C : Lambda->captures()) {
              if (C.capturesVariable()) {
                if (ValueDecl *CapturedVar = C.getCapturedVar()) {
                  if (auto *VD = dyn_cast<VarDecl>(CapturedVar)) {
                    if (auto *CapturedVarInit = VD->getInit()) {
                      if (hasGuardianVariable(V, CapturedVarInit)) {
                        continue;
                      }
                    }
                  }
                }
              }
              CapturedVariablesHaveGuardians = false;
            }
            if (!CapturedVariablesHaveGuardians)
              LambdasWithoutGuardians.insert(Lambda);
            return true;
          }
        }
        return Base::TraverseVarDecl(V);
      }

      // FIXME: Handle assignment operator.

      bool VisitCallExpr(const CallExpr *CE) {
        for (auto C : CE->children()) {
          auto *E = dyn_cast<Expr>(C);
          if (!E)
            continue;
          E = E->IgnoreParenCasts();
          auto *Lambda = dyn_cast<LambdaExpr>(E);
          if (!Lambda)
            continue;
          auto *LambdaClass = Lambda->getLambdaClass();
          for (auto Method : LambdaClass->methods()) {
            // Calls a temporary lambda created within.
            if (Method == CE->getCalleeDecl()) {
              SafeLambdas.insert(Lambda);
              return true;
            }
          }
        }
        CheckEscapeLambdaArguments(CE);
        return true;
      }

      void CheckEscapeLambdaArguments(const CallExpr *CE)
      {
        const FunctionType::ExtParameterInfo *ExtParams = nullptr;
        unsigned ExtParamsCount = 0;
        if (auto *CalleeDecl = CE->getDirectCallee()) {
          if (auto *ProtoType = GetFunctionProtoType(CalleeDecl)) {
            ExtParams = ProtoType->getExtParameterInfosOrNull();
            ExtParamsCount = ExtParams ? ProtoType->getNumParams() : 0;
          }
        }
        for (unsigned i = 0, NumArgs = CE->getNumArgs(); i < NumArgs; ++i) {
          auto *Arg = CE->getArg(i);
          Arg = Arg->IgnoreParenCasts();
          if (auto *ConstructExpr = dyn_cast<CXXConstructExpr>(Arg)) {
            if (IsWTFFunction(ConstructExpr->getConstructor()) &&
                ConstructExpr->getNumArgs() > 0) {
              if (auto *ConstructArg = ConstructExpr->getArg(0)) {
                ConstructArg = ConstructArg->IgnoreParenCasts();
                if (auto *Ref = dyn_cast<DeclRefExpr>(ConstructArg)) {
                  if (auto *Lambda = GetLambdaExprFromInit(Ref)) {
                    if (i < ExtParamsCount && ExtParams[i].isNoEscape()) {
                      if (!LambdasWithoutGuardians.contains(Lambda))
                        continue;
                    }
                    Checker->visitLambdaExpr(Lambda);
                  }
                }
              }
            }
          } else if (auto *Ref = dyn_cast<DeclRefExpr>(Arg)) {
            if (auto *Lambda = GetLambdaExprFromInit(Ref)) {
              if (auto *CalleeDecl = CE->getDirectCallee()) {
                if (!LambdasWithoutGuardians.contains(Lambda) &&
                    TFA.isTrivial(CalleeDecl))
                  continue;
              }
              Checker->visitLambdaExpr(Lambda);
            }
          } else if (auto *Lambda = dyn_cast<LambdaExpr>(Arg)) {
            if (auto *CalleeDecl = CE->getDirectCallee()) {
              if (!LambdasWithoutGuardians.contains(Lambda) &&
                   TFA.isTrivial(CalleeDecl)) {
                continue;
              }
            }
            Checker->visitLambdaExpr(Lambda);
          }
        }
      }

      const LambdaExpr *GetLambdaExprFromInit(const DeclRefExpr *Ref) {
        auto *Decl = Ref->getDecl();
        if (!Decl)
          return nullptr;
        auto *Var = dyn_cast<VarDecl>(Decl);
        if (!Var)
          return nullptr;
        auto *Init = Var->getInit();
        if (!Init)
          return nullptr;
        return dyn_cast<LambdaExpr>(Init);
      }

      const FunctionProtoType *GetFunctionProtoType(const FunctionDecl *FD) {
        auto *Type = FD->getFunctionType();
        if (!Type)
          return nullptr;
        return dyn_cast<FunctionProtoType>(Type);
      }

      bool IsWTFFunction(const CXXMethodDecl *Decl) {
        if (!Decl)
          return false;
        auto *Cls = Decl->getParent();
        if (!Cls || safeGetName(Cls) != "Function")
          return false;
        auto *Ns = Cls->getParent();
        return Ns && safeGetName(Ns) == "WTF";
      }
    };

    LocalVisitor visitor(this);
    visitor.TraverseDecl(const_cast<TranslationUnitDecl *>(TUD));
  }

  void visitLambdaExpr(const LambdaExpr *L) const {
    for (const LambdaCapture &C : L->captures()) {
      if (C.capturesVariable()) {
        ValueDecl *CapturedVar = C.getCapturedVar();
        if (auto *CapturedVarType = CapturedVar->getType().getTypePtrOrNull()) {
            std::optional<bool> IsUncountedPtr = isUncountedPtr(CapturedVarType);
            if (IsUncountedPtr && *IsUncountedPtr) {
                reportBug(C, CapturedVar, CapturedVarType);
            }
        }
      }
    }
  }

  void reportBug(const LambdaCapture &Capture, ValueDecl *CapturedVar,
                 const Type *T) const {
    assert(CapturedVar);

    SmallString<100> Buf;
    llvm::raw_svector_ostream Os(Buf);

    if (Capture.isExplicit()) {
      Os << "Captured ";
    } else {
      Os << "Implicitly captured ";
    }
    if (T->isPointerType()) {
      Os << "raw-pointer ";
    } else {
      assert(T->isReferenceType());
      Os << "reference ";
    }

    printQuotedQualifiedName(Os, Capture.getCapturedVar());
    Os << " to uncounted type is unsafe.";

    PathDiagnosticLocation BSLoc(Capture.getLocation(), BR->getSourceManager());
    auto Report = std::make_unique<BasicBugReport>(Bug, Os.str(), BSLoc);
    BR->emitReport(std::move(Report));
  }
};
} // namespace

void ento::registerUncountedLambdaCapturesChecker(CheckerManager &Mgr) {
  Mgr.registerChecker<UncountedLambdaCapturesChecker>();
}

bool ento::shouldRegisterUncountedLambdaCapturesChecker(
    const CheckerManager &mgr) {
  return true;
}
