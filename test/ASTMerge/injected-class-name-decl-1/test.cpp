// Trigger a case when at import of template record and replacing its type
// with InjectedClassNameType there is a PrevDecl of the record.

// RUN: %clang_cc1 -std=c++1z -emit-pch -o %t.ast %S/Inputs/inject1.cpp
// RUN: %clang_cc1 -std=c++1z -fsyntax-only -ast-merge %t.ast %s
// expected-no-diagnostics
