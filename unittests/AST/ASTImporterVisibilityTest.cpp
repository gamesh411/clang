//===- unittest/AST/ASTImporterTest.cpp - AST node import test ------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Type-parameterized tests for the correct import of Decls with different
// visibility.
//
//===----------------------------------------------------------------------===//

// Define this to have ::testing::Combine available.
// FIXME: Better solution for this?
#define GTEST_HAS_COMBINE 1

#include "ASTImporterFixtures.h"

namespace clang {
namespace ast_matchers {

using internal::BindableMatcher;

// Type parameters for type-parameterized test fixtures.
struct GetFunPattern {
  using DeclTy = FunctionDecl;
  BindableMatcher<Decl> operator()() { return functionDecl(hasName("f")); }
};
struct GetFunTemplPattern {
  using DeclTy = FunctionTemplateDecl;
  BindableMatcher<Decl> operator()() {
    return functionTemplateDecl(hasName("f"));
  }
};
struct GetVarPattern {
  using DeclTy = VarDecl;
  BindableMatcher<Decl> operator()() { return varDecl(hasName("v")); }
};
struct GetVarTemplPattern {
  using DeclTy = VarTemplateDecl;
  BindableMatcher<Decl> operator()() {
    return namedDecl(hasName("v"), has(templateTypeParmDecl()));
  }
};
struct GetClassPattern {
  using DeclTy = CXXRecordDecl;
  BindableMatcher<Decl> operator()() { return cxxRecordDecl(hasName("X")); }
};
struct GetClassTemplPattern {
  using DeclTy = ClassTemplateDecl;
  BindableMatcher<Decl> operator()() { return classTemplateDecl(hasName("X")); }
};
struct GetEnumPattern {
  using DeclTy = EnumDecl;
  BindableMatcher<Decl> operator()() { return enumDecl(hasName("E")); }
};
struct GetTypedefPattern {
  using DeclTy = TypedefDecl;
  BindableMatcher<Decl> operator()() { return typedefDecl(hasName("T")); }
};
struct GetTypeAliasPattern {
  using DeclTy = TypeAliasDecl;
  BindableMatcher<Decl> operator()() { return typeAliasDecl(hasName("T")); }
};

// Values for the value-parameterized test fixtures.
// FunctionDecl:
const auto *ExternF = "void f();";
const auto *StaticF = "static void f();";
const auto *AnonF = "namespace { void f(); }";
// FunctionTemplateDecl:
const auto *ExternFT = "template <class> void f();";
const auto *StaticFT = "template <class> static void f();";
const auto *AnonFT = "namespace { template <class> void f(); }";
// VarDecl:
const auto *ExternV = "extern int v;";
const auto *StaticV = "static int v;";
const auto *AnonV = "namespace { extern int v; }";
// VarTemplateDecl:
const auto *ExternVT = "template <class> extern int v;";
const auto *StaticVT = "template <class> static int v;";
const auto *AnonVT = "namespace { template <class> extern int v; }";
// CXXRecordDecl:
const auto *ExternC = "class X;";
const auto *AnonC = "namespace { class X; }";
// ClassTemplateDecl:
const auto *ExternCT = "template <class> class X;";
const auto *AnonCT = "namespace { template <class> class X; }";
// EnumDecl:
const auto *ExternE = "enum E {};";
const auto *AnonE = "namespace { enum E {}; }";
const auto *ExternEC = "enum class E;";
const auto *AnonEC = "namespace { enum class E; }";
// TypedefNameDecl:
const auto *ExternTypedef = "typedef int T;";
const auto *AnonTypedef = "namespace { typedef int T; }";
const auto *ExternUsing = "using T = int;";
const auto *AnonUsing = "namespace { using T = int; }";

// First value in tuple: Compile options.
// Second value in tuple: Source code to be used in the test.
using ImportVisibilityChainParams =
    ::testing::WithParamInterface<std::tuple<ArgVector, const char *>>;
// Fixture to test the redecl chain of Decls with the same visibility. Gtest
// makes it possible to have either value-parameterized or type-parameterized
// fixtures. However, we cannot have both value- and type-parameterized test
// fixtures. This is a value-parameterized test fixture in the gtest sense. We
// intend to mimic gtest's type-parameters via the PatternFactory template
// parameter. We manually instantiate the different tests with the each types.
template <typename PatternFactory>
class ImportVisibilityChain
    : public ASTImporterTestBase, public ImportVisibilityChainParams {
protected:
  using DeclTy = typename PatternFactory::DeclTy;
  ArgVector getExtraArgs() const override { return std::get<0>(GetParam()); }
  std::string getCode() const { return std::get<1>(GetParam()); }
  BindableMatcher<Decl> getPattern() const { return PatternFactory()(); }

  // Type-parameterized test.
  void TypedTest_ImportChain() {
    std::string Code = getCode() + getCode();
    auto Pattern = getPattern();

    TranslationUnitDecl *FromTu = getTuDecl(Code, Lang_CXX14, "input0.cc");

    auto *FromD0 = FirstDeclMatcher<DeclTy>().match(FromTu, Pattern);
    auto *FromD1 = LastDeclMatcher<DeclTy>().match(FromTu, Pattern);

    auto *ToD0 = Import(FromD0, Lang_CXX14);
    auto *ToD1 = Import(FromD1, Lang_CXX14);

    EXPECT_TRUE(ToD0);
    ASSERT_TRUE(ToD1);
    EXPECT_NE(ToD0, ToD1);
    EXPECT_EQ(ToD1->getPreviousDecl(), ToD0);
  }
};

// Manual instantiation of the fixture with each type.
using ImportFunctionsVisibilityChain = ImportVisibilityChain<GetFunPattern>;
using ImportFunctionTemplatesVisibilityChain =
    ImportVisibilityChain<GetFunTemplPattern>;
using ImportVariablesVisibilityChain = ImportVisibilityChain<GetVarPattern>;
using ImportVariableTemplatesVisibilityChain =
    ImportVisibilityChain<GetVarTemplPattern>;
using ImportClassesVisibilityChain = ImportVisibilityChain<GetClassPattern>;
using ImportClassTemplatesVisibilityChain =
    ImportVisibilityChain<GetClassTemplPattern>;
using ImportScopedEnumsVisibilityChain = ImportVisibilityChain<GetEnumPattern>;

// Value-parameterized test for functions.
TEST_P(ImportFunctionsVisibilityChain, ImportChain) {
  TypedTest_ImportChain();
}
// Value-parameterized test for function templates.
TEST_P(ImportFunctionTemplatesVisibilityChain, ImportChain) {
  TypedTest_ImportChain();
}
// Value-parameterized test for variables.
TEST_P(ImportVariablesVisibilityChain, ImportChain) {
  TypedTest_ImportChain();
}
// Value-parameterized test for variable templates.
TEST_P(ImportVariableTemplatesVisibilityChain, ImportChain) {
  TypedTest_ImportChain();
}
// Value-parameterized test for classes.
TEST_P(ImportClassesVisibilityChain, ImportChain) {
  TypedTest_ImportChain();
}
// Value-parameterized test for classes.
TEST_P(ImportClassTemplatesVisibilityChain, ImportChain) {
  TypedTest_ImportChain();
}
// Value-parameterized test for scoped enums.
TEST_P(ImportScopedEnumsVisibilityChain, ImportChain) {
  TypedTest_ImportChain();
}

// Automatic instantiation of the value-parameterized tests.
INSTANTIATE_TEST_CASE_P(ParameterizedTests, ImportFunctionsVisibilityChain,
                        ::testing::Combine(
                           DefaultTestValuesForRunOptions,
                           ::testing::Values(ExternF, StaticF, AnonF)), );
INSTANTIATE_TEST_CASE_P(ParameterizedTests,
                        ImportFunctionTemplatesVisibilityChain,
                        ::testing::Combine(DefaultTestValuesForRunOptions,
                                           ::testing::Values(ExternFT, StaticFT,
                                                             AnonFT)), );
INSTANTIATE_TEST_CASE_P(
    ParameterizedTests, ImportVariablesVisibilityChain,
    ::testing::Combine(
        DefaultTestValuesForRunOptions,
        // There is no point to instantiate with StaticV, because in C++ we can
        // forward declare a variable only with the 'extern' keyword.
        // Consequently, each fwd declared variable has external linkage.  This
        // is different in the C language where any declaration without an
        // initializer is a tentative definition, subsequent definitions may be
        // provided but they must have the same linkage.  See also the test
        // ImportVariableChainInC which test for this special C Lang case.
        ::testing::Values(ExternV, AnonV)), );
INSTANTIATE_TEST_CASE_P(ParameterizedTests,
                        ImportVariableTemplatesVisibilityChain,
                        ::testing::Combine(DefaultTestValuesForRunOptions,
                                           ::testing::Values(ExternVT,
                                                             AnonVT)), );
INSTANTIATE_TEST_CASE_P(ParameterizedTests, ImportClassesVisibilityChain,
                        ::testing::Combine(DefaultTestValuesForRunOptions,
                                           ::testing::Values(ExternC,
                                                             AnonC)), );
INSTANTIATE_TEST_CASE_P(ParameterizedTests, ImportClassTemplatesVisibilityChain,
                        ::testing::Combine(DefaultTestValuesForRunOptions,
                                           ::testing::Values(ExternCT,
                                                             AnonCT)), );
INSTANTIATE_TEST_CASE_P(ParameterizedTests, ImportScopedEnumsVisibilityChain,
                        ::testing::Combine(DefaultTestValuesForRunOptions,
                                           ::testing::Values(ExternEC,
                                                             AnonEC)), );

// First value in tuple: Compile options.
// Second value in tuple: Tuple with informations for the test.
// Code for first import (or initial code), code to import, whether the `f`
// functions are expected to be linked in a declaration chain.
// One value of this tuple is combined with every value of compile options.
// The test can have a single tuple as parameter only.
using ImportVisibilityParams = ::testing::WithParamInterface<
    std::tuple<ArgVector, std::tuple<const char *, const char *, bool>>>;

template <typename PatternFactory>
class ImportVisibility
    : public ASTImporterTestBase,
      public ImportVisibilityParams {
protected:
  using DeclTy = typename PatternFactory::DeclTy;
  ArgVector getExtraArgs() const override { return std::get<0>(GetParam()); }
  std::string getCode0() const { return std::get<0>(std::get<1>(GetParam())); }
  std::string getCode1() const { return std::get<1>(std::get<1>(GetParam())); }
  bool shouldBeLinked() const { return std::get<2>(std::get<1>(GetParam())); }
  BindableMatcher<Decl> getPattern() const { return PatternFactory()(); }

  void TypedTest_ImportAfter() {
    TranslationUnitDecl *ToTu = getToTuDecl(getCode0(), Lang_CXX14);
    TranslationUnitDecl *FromTu =
        getTuDecl(getCode1(), Lang_CXX14, "input1.cc");

    auto *ToD0 = FirstDeclMatcher<DeclTy>().match(ToTu, getPattern());
    auto *FromD1 = FirstDeclMatcher<DeclTy>().match(FromTu, getPattern());

    auto *ToD1 = Import(FromD1, Lang_CXX14);

    ASSERT_TRUE(ToD0);
    ASSERT_TRUE(ToD1);
    EXPECT_NE(ToD0, ToD1);

    if (shouldBeLinked())
      EXPECT_EQ(ToD1->getPreviousDecl(), ToD0);
    else
      EXPECT_FALSE(ToD1->getPreviousDecl());
  }

  void TypedTest_ImportAfterImport() {
    TranslationUnitDecl *FromTu0 =
        getTuDecl(getCode0(), Lang_CXX14, "input0.cc");
    TranslationUnitDecl *FromTu1 =
        getTuDecl(getCode1(), Lang_CXX14, "input1.cc");
    auto *FromD0 =
        FirstDeclMatcher<DeclTy>().match(FromTu0, getPattern());
    auto *FromD1 =
        FirstDeclMatcher<DeclTy>().match(FromTu1, getPattern());
    auto *ToD0 = Import(FromD0, Lang_CXX14);
    auto *ToD1 = Import(FromD1, Lang_CXX14);
    ASSERT_TRUE(ToD0);
    ASSERT_TRUE(ToD1);
    EXPECT_NE(ToD0, ToD1);
    if (shouldBeLinked())
      EXPECT_EQ(ToD1->getPreviousDecl(), ToD0);
    else
      EXPECT_FALSE(ToD1->getPreviousDecl());
  }

  void TypedTest_ImportAfterWithMerge() {
    TranslationUnitDecl *ToTu = getToTuDecl(getCode0(), Lang_CXX14);
    TranslationUnitDecl *FromTu =
        getTuDecl(getCode1(), Lang_CXX14, "input1.cc");

    auto *ToF0 = FirstDeclMatcher<DeclTy>().match(ToTu, getPattern());
    auto *FromF1 = FirstDeclMatcher<DeclTy>().match(FromTu, getPattern());

    auto *ToF1 = Import(FromF1, Lang_CXX14);

    ASSERT_TRUE(ToF0);
    ASSERT_TRUE(ToF1);

    if (shouldBeLinked())
      EXPECT_EQ(ToF0, ToF1);
    else
      EXPECT_NE(ToF0, ToF1);

    // We expect no (ODR) warning during the import.
    EXPECT_EQ(0u, ToTu->getASTContext().getDiagnostics().getNumWarnings());
  }

  void TypedTest_ImportAfterImportWithMerge() {
    TranslationUnitDecl *FromTu0 =
        getTuDecl(getCode0(), Lang_CXX14, "input0.cc");
    TranslationUnitDecl *FromTu1 =
        getTuDecl(getCode1(), Lang_CXX14, "input1.cc");
    auto *FromF0 = FirstDeclMatcher<DeclTy>().match(FromTu0, getPattern());
    auto *FromF1 = FirstDeclMatcher<DeclTy>().match(FromTu1, getPattern());
    auto *ToF0 = Import(FromF0, Lang_CXX14);
    auto *ToF1 = Import(FromF1, Lang_CXX14);
    ASSERT_TRUE(ToF0);
    ASSERT_TRUE(ToF1);
    if (shouldBeLinked())
      EXPECT_EQ(ToF0, ToF1);
    else
      EXPECT_NE(ToF0, ToF1);

    // We expect no (ODR) warning during the import.
    EXPECT_EQ(0u, ToF0->getTranslationUnitDecl()
                      ->getASTContext()
                      .getDiagnostics()
                      .getNumWarnings());
  }
};

using ImportFunctionsVisibility = ImportVisibility<GetFunPattern>;
using ImportFunctionTemplatesVisibility = ImportVisibility<GetFunTemplPattern>;
using ImportVariablesVisibility = ImportVisibility<GetVarPattern>;
using ImportVariableTemplatesVisibility = ImportVisibility<GetVarTemplPattern>;
using ImportClassesVisibility = ImportVisibility<GetClassPattern>;
using ImportClassTemplatesVisibility = ImportVisibility<GetClassTemplPattern>;
using ImportEnumsVisibility = ImportVisibility<GetEnumPattern>;
using ImportScopedEnumsVisibility = ImportVisibility<GetEnumPattern>;
using ImportTypedefVisibility = ImportVisibility<GetTypedefPattern>;
using ImportTypeAliasVisibility = ImportVisibility<GetTypeAliasPattern>;

// FunctionDecl.
TEST_P(ImportFunctionsVisibility, ImportAfter) {
  TypedTest_ImportAfter();
}
TEST_P(ImportFunctionsVisibility, ImportAfterImport) {
  TypedTest_ImportAfterImport();
}
// FunctionTemplateDecl.
TEST_P(ImportFunctionTemplatesVisibility, ImportAfter) {
  TypedTest_ImportAfter();
}
TEST_P(ImportFunctionTemplatesVisibility, ImportAfterImport) {
  TypedTest_ImportAfterImport();
}
// VarDecl.
TEST_P(ImportVariablesVisibility, ImportAfter) {
  TypedTest_ImportAfter();
}
TEST_P(ImportVariablesVisibility, ImportAfterImport) {
  TypedTest_ImportAfterImport();
}
// VarTemplateDecl.
TEST_P(ImportVariableTemplatesVisibility, ImportAfter) {
  TypedTest_ImportAfter();
}
TEST_P(ImportVariableTemplatesVisibility, ImportAfterImport) {
  TypedTest_ImportAfterImport();
}
// CXXRecordDecl.
TEST_P(ImportClassesVisibility, ImportAfter) {
  TypedTest_ImportAfter();
}
TEST_P(ImportClassesVisibility, ImportAfterImport) {
  TypedTest_ImportAfterImport();
}
// ClassTemplateDecl.
TEST_P(ImportClassTemplatesVisibility, ImportAfter) { TypedTest_ImportAfter(); }
TEST_P(ImportClassTemplatesVisibility, ImportAfterImport) {
  TypedTest_ImportAfterImport();
}
// EnumDecl.
TEST_P(ImportEnumsVisibility, ImportAfter) {
  TypedTest_ImportAfterWithMerge();
}
TEST_P(ImportEnumsVisibility, ImportAfterImport) {
  TypedTest_ImportAfterImportWithMerge();
}
TEST_P(ImportScopedEnumsVisibility, ImportAfter) {
  TypedTest_ImportAfter();
}
TEST_P(ImportScopedEnumsVisibility, ImportAfterImport) {
  TypedTest_ImportAfterImport();
}
// TypedefNameDecl.
TEST_P(ImportTypedefVisibility, ImportAfter) {
  TypedTest_ImportAfterWithMerge();
}
TEST_P(ImportTypedefVisibility, ImportAfterImport) {
  TypedTest_ImportAfterImportWithMerge();
}
TEST_P(ImportTypeAliasVisibility, ImportAfter) {
  TypedTest_ImportAfterWithMerge();
}
TEST_P(ImportTypeAliasVisibility, ImportAfterImport) {
  TypedTest_ImportAfterImportWithMerge();
}

const bool ExpectLink = true;
const bool ExpectNotLink = false;

INSTANTIATE_TEST_CASE_P(
    ParameterizedTests, ImportFunctionsVisibility,
    ::testing::Combine(
        DefaultTestValuesForRunOptions,
        ::testing::Values(std::make_tuple(ExternF, ExternF, ExpectLink),
                          std::make_tuple(ExternF, StaticF, ExpectNotLink),
                          std::make_tuple(ExternF, AnonF, ExpectNotLink),
                          std::make_tuple(StaticF, ExternF, ExpectNotLink),
                          std::make_tuple(StaticF, StaticF, ExpectNotLink),
                          std::make_tuple(StaticF, AnonF, ExpectNotLink),
                          std::make_tuple(AnonF, ExternF, ExpectNotLink),
                          std::make_tuple(AnonF, StaticF, ExpectNotLink),
                          std::make_tuple(AnonF, AnonF, ExpectNotLink))), );
INSTANTIATE_TEST_CASE_P(
    ParameterizedTests, ImportFunctionTemplatesVisibility,
    ::testing::Combine(
        DefaultTestValuesForRunOptions,
        ::testing::Values(std::make_tuple(ExternFT, ExternFT, ExpectLink),
                          std::make_tuple(ExternFT, StaticFT, ExpectNotLink),
                          std::make_tuple(ExternFT, AnonFT, ExpectNotLink),
                          std::make_tuple(StaticFT, ExternFT, ExpectNotLink),
                          std::make_tuple(StaticFT, StaticFT, ExpectNotLink),
                          std::make_tuple(StaticFT, AnonFT, ExpectNotLink),
                          std::make_tuple(AnonFT, ExternFT, ExpectNotLink),
                          std::make_tuple(AnonFT, StaticFT, ExpectNotLink),
                          std::make_tuple(AnonFT, AnonFT, ExpectNotLink))), );
INSTANTIATE_TEST_CASE_P(
    ParameterizedTests, ImportVariablesVisibility,
    ::testing::Combine(
        DefaultTestValuesForRunOptions,
        ::testing::Values(std::make_tuple(ExternV, ExternV, ExpectLink),
                          std::make_tuple(ExternV, StaticV, ExpectNotLink),
                          std::make_tuple(ExternV, AnonV, ExpectNotLink),
                          std::make_tuple(StaticV, ExternV, ExpectNotLink),
                          std::make_tuple(StaticV, StaticV, ExpectNotLink),
                          std::make_tuple(StaticV, AnonV, ExpectNotLink),
                          std::make_tuple(AnonV, ExternV, ExpectNotLink),
                          std::make_tuple(AnonV, StaticV, ExpectNotLink),
                          std::make_tuple(AnonV, AnonV, ExpectNotLink))), );
INSTANTIATE_TEST_CASE_P(
    ParameterizedTests, ImportVariableTemplatesVisibility,
    ::testing::Combine(
        DefaultTestValuesForRunOptions,
        ::testing::Values(std::make_tuple(ExternVT, ExternVT, ExpectLink),
                          std::make_tuple(ExternVT, StaticVT, ExpectNotLink),
                          std::make_tuple(ExternVT, AnonVT, ExpectNotLink),
                          std::make_tuple(StaticVT, ExternVT, ExpectNotLink),
                          std::make_tuple(StaticVT, StaticVT, ExpectNotLink),
                          std::make_tuple(StaticVT, AnonVT, ExpectNotLink),
                          std::make_tuple(AnonVT, ExternVT, ExpectNotLink),
                          std::make_tuple(AnonVT, StaticVT, ExpectNotLink),
                          std::make_tuple(AnonVT, AnonVT, ExpectNotLink))), );
INSTANTIATE_TEST_CASE_P(
    ParameterizedTests, ImportClassesVisibility,
    ::testing::Combine(
        DefaultTestValuesForRunOptions,
        ::testing::Values(std::make_tuple(ExternC, ExternC, ExpectLink),
                          std::make_tuple(ExternC, AnonC, ExpectNotLink),
                          std::make_tuple(AnonC, ExternC, ExpectNotLink),
                          std::make_tuple(AnonC, AnonC, ExpectNotLink))), );
INSTANTIATE_TEST_CASE_P(
    ParameterizedTests, ImportClassTemplatesVisibility,
    ::testing::Combine(
        DefaultTestValuesForRunOptions,
        ::testing::Values(std::make_tuple(ExternCT, ExternCT, ExpectLink),
                          std::make_tuple(ExternCT, AnonCT, ExpectNotLink),
                          std::make_tuple(AnonCT, ExternCT, ExpectNotLink),
                          std::make_tuple(AnonCT, AnonCT, ExpectNotLink))), );
INSTANTIATE_TEST_CASE_P(
    ParameterizedTests, ImportEnumsVisibility,
    ::testing::Combine(
        DefaultTestValuesForRunOptions,
        ::testing::Values(std::make_tuple(ExternE, ExternE, ExpectLink),
                          std::make_tuple(ExternE, AnonE, ExpectNotLink),
                          std::make_tuple(AnonE, ExternE, ExpectNotLink),
                          std::make_tuple(AnonE, AnonE, ExpectNotLink))), );
INSTANTIATE_TEST_CASE_P(
    ParameterizedTests, ImportScopedEnumsVisibility,
    ::testing::Combine(
        DefaultTestValuesForRunOptions,
        ::testing::Values(std::make_tuple(ExternEC, ExternEC, ExpectLink),
                          std::make_tuple(ExternEC, AnonEC, ExpectNotLink),
                          std::make_tuple(AnonEC, ExternEC, ExpectNotLink),
                          std::make_tuple(AnonEC, AnonEC, ExpectNotLink))), );
INSTANTIATE_TEST_CASE_P(
    ParameterizedTests, ImportTypedefVisibility,
    ::testing::Combine(
        DefaultTestValuesForRunOptions,
        ::testing::Values(
            std::make_tuple(ExternTypedef, ExternTypedef, ExpectLink),
            std::make_tuple(ExternTypedef, AnonTypedef, ExpectNotLink),
            std::make_tuple(AnonTypedef, ExternTypedef, ExpectNotLink),
            std::make_tuple(AnonTypedef, AnonTypedef, ExpectNotLink))), );
INSTANTIATE_TEST_CASE_P(
    ParameterizedTests, ImportTypeAliasVisibility,
    ::testing::Combine(
        DefaultTestValuesForRunOptions,
        ::testing::Values(
            std::make_tuple(ExternUsing, ExternUsing, ExpectLink),
            std::make_tuple(ExternUsing, AnonUsing, ExpectNotLink),
            std::make_tuple(AnonUsing, ExternUsing, ExpectNotLink),
            std::make_tuple(AnonUsing, AnonUsing, ExpectNotLink))), );

} // end namespace ast_matchers
} // end namespace clang
