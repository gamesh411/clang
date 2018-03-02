// RUN: clang-func-mapping %s -- | FileCheck %s

int f(int) {
  return 0;
}

// CHECK: c:@F@f#I#
