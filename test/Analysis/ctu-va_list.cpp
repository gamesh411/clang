// RUN: mkdir -p %T/ctudir4
// RUN: %clang_cc1 -triple x86_64-pc-linux-gnu -emit-pch -o %T/ctudir4/ctu-va_list-first.c.ast %S/Inputs/ctu-va_list-first.c
// RUN: %clang_cc1 -triple x86_64-pc-linux-gnu -emit-pch -o %T/ctudir4/ctu-va_list-second.cpp.ast %S/Inputs/ctu-va_list-second.cpp
// RUN: cp %S/Inputs/externalFnMap_va_list.txt %T/ctudir4/externalFnMap.txt
// RUN: %clang_analyze_cc1 -triple x86_64-pc-linux-gnu -analyzer-checker=core -analyzer-config experimental-enable-naive-ctu-analysis=true -analyzer-config ctu-dir=%T/ctudir4 -verify %s

// RUN: %clang_cc1 -triple powerpc-montavista-linux-gnu -emit-pch -o %T/ctudir4/ctu-va_list-first.c.ast %S/Inputs/ctu-va_list-first.c
// RUN: %clang_cc1 -triple powerpc-montavista-pc-linux-gnu -emit-pch -o %T/ctudir4/ctu-va_list-second.cpp.ast %S/Inputs/ctu-va_list-second.cpp
// RUN: cp %S/Inputs/externalFnMap_va_list.txt %T/ctudir4/externalFnMap.txt
// RUN: %clang_analyze_cc1 -triple powerpc-montavista-pc-linux-gnu -analyzer-checker=core -analyzer-config experimental-enable-naive-ctu-analysis=true -analyzer-config ctu-dir=%T/ctudir4 -verify %s

// RUN: %clang_cc1 -triple powerpc64-montavista-linux-gnu -emit-pch -o %T/ctudir4/ctu-va_list-first.c.ast %S/Inputs/ctu-va_list-first.c
// RUN: %clang_cc1 -triple powerpc64-montavista-pc-linux-gnu -emit-pch -o %T/ctudir4/ctu-va_list-second.cpp.ast %S/Inputs/ctu-va_list-second.cpp
// RUN: cp %S/Inputs/externalFnMap_va_list.txt %T/ctudir4/externalFnMap.txt
// RUN: %clang_analyze_cc1 -triple powerpc64-montavista-pc-linux-gnu -analyzer-checker=core -analyzer-config experimental-enable-naive-ctu-analysis=true -analyzer-config ctu-dir=%T/ctudir4 -verify %s

// RUN: %clang_cc1 -triple arm64-linux-android -emit-pch -o %T/ctudir4/ctu-va_list-first.c.ast %S/Inputs/ctu-va_list-first.c
// RUN: %clang_cc1 -triple arm64-linux-android -emit-pch -o %T/ctudir4/ctu-va_list-second.cpp.ast %S/Inputs/ctu-va_list-second.cpp
// RUN: cp %S/Inputs/externalFnMap_va_list.txt %T/ctudir4/externalFnMap.txt
// RUN: %clang_analyze_cc1 -triple arm64-linux-android -analyzer-checker=core -analyzer-config experimental-enable-naive-ctu-analysis=true -analyzer-config ctu-dir=%T/ctudir4 -verify %s

// RUN: %clang_cc1 -triple le32-unknown-nacl -emit-pch -o %T/ctudir4/ctu-va_list-first.c.ast %S/Inputs/ctu-va_list-first.c
// RUN: %clang_cc1 -triple le32-unknown-nacl -emit-pch -o %T/ctudir4/ctu-va_list-second.cpp.ast %S/Inputs/ctu-va_list-second.cpp
// RUN: cp %S/Inputs/externalFnMap_va_list.txt %T/ctudir4/externalFnMap.txt
// RUN: %clang_analyze_cc1 -triple le32-unknown-nacl -analyzer-checker=core -analyzer-config experimental-enable-naive-ctu-analysis=true -analyzer-config ctu-dir=%T/ctudir4 -verify %s

// RUN: %clang_cc1 -triple arm-linux-androideabi -emit-pch -o %T/ctudir4/ctu-va_list-first.c.ast %S/Inputs/ctu-va_list-first.c
// RUN: %clang_cc1 -triple arm-linux-androideabi -emit-pch -o %T/ctudir4/ctu-va_list-second.cpp.ast %S/Inputs/ctu-va_list-second.cpp
// RUN: cp %S/Inputs/externalFnMap_va_list.txt %T/ctudir4/externalFnMap.txt
// RUN: %clang_analyze_cc1 -triple arm-linux-androideabi -analyzer-checker=core -analyzer-config experimental-enable-naive-ctu-analysis=true -analyzer-config ctu-dir=%T/ctudir4 -verify %s

// RUN: mkdir -p %T/ctudir4
// RUN: %clang_cc1 -triple systemz-unknown-linux-gnu -emit-pch -o %T/ctudir4/ctu-va_list-first.c.ast %S/Inputs/ctu-va_list-first.c
// RUN: %clang_cc1 -triple systemz-unknown-linux-gnu -emit-pch -o %T/ctudir4/ctu-va_list-second.cpp.ast %S/Inputs/ctu-va_list-second.cpp
// RUN: cp %S/Inputs/externalFnMap_va_list.txt %T/ctudir4/externalFnMap.txt
// RUN: %clang_analyze_cc1 -triple systemz-unknown-linux-gnu -analyzer-checker=core -analyzer-config experimental-enable-naive-ctu-analysis=true -analyzer-config ctu-dir=%T/ctudir4 -verify %s

// RUN: mkdir -p %T/ctudir4
// RUN: %clang_cc1 -triple lanai-unknown-unknown -emit-pch -o %T/ctudir4/ctu-va_list-first.c.ast %S/Inputs/ctu-va_list-first.c
// RUN: %clang_cc1 -triple lanai-unknown-unknown -emit-pch -o %T/ctudir4/ctu-va_list-second.cpp.ast %S/Inputs/ctu-va_list-second.cpp
// RUN: cp %S/Inputs/externalFnMap_va_list.txt %T/ctudir4/externalFnMap.txt
// RUN: %clang_analyze_cc1 -triple lanai-unknown-unknown -analyzer-checker=core -analyzer-config experimental-enable-naive-ctu-analysis=true -analyzer-config ctu-dir=%T/ctudir4 -verify %s

// expected-no-diagnostics

extern "C" {
void first(int, ...);
}
void second();

void third() {
  first(1, 2);
  second();
}
