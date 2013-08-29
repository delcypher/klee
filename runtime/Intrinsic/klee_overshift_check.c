//===-- klee_overshift_check.c ---------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include <klee/klee.h>

void klee_overshift_check(unsigned long long bitWidth, unsigned long long shift) {
  /* If we do try to do x << y or x >> y
   * where
   *   bitWidth = sizeof(x)*8
   *   shift = y
   *
   * then we can detect overshifting (which has undefined behaviour) with
   * the following condition
   */
  if (shift >= bitWidth)
    klee_report_error(__FILE__, __LINE__, "overshift error", "overshift.err");
}


