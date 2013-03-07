//===-- Common.h ------------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

/*
 * This file groups declarations that are common to both KLEE and Kleaver.
 */

#ifndef KLEE_COMMON_H
#define KLEE_COMMON_H

namespace klee {
    const char ALL_QUERIES_SMT2_FILE_NAME[]="all-queries.smt2";
    const char SOLVER_QUERIES_SMT2_FILE_NAME[]="solver-queries.smt2";
    const char ALL_QUERIES_PC_FILE_NAME[]="all-queries.pc";
    const char SOLVER_QUERIES_PC_FILE_NAME[]="solver-queries.pc";
}

#endif /* KLEE_COMMON_H */

