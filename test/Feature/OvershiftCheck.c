// RUN: %llvmgcc %s -emit-llvm -O0 -c -o %t1.bc
// RUN: %klee -check-overshift %t1.bc > %t1.log
// RUN: grep -c "overshift error" %t1.log
#include <stdio.h>

int main()
{
  unsigned int x=15;
  unsigned int y;
  volatile unsigned int result;

  klee_make_symbolic(&y,sizeof(y),"shift_amount");
  result = x << y;

  return 0;
}
