/*
 * This header groups command line options declarations and associated data
 * that is common for klee and kleaver.
 */

#ifndef KLEE_COMMANDLINE_H
#define KLEE_COMMANDLINE_H

#include "llvm/Support/CommandLine.h"

// Convenience macro to set llvm::cl::cat on options. User's may/may not have
// KLEE's Command line patches so this macro provides a succinct way of using
// them that won't break compilation for users without the patches.  It must be
// used as cl::opt<int> a("thing" KLEE_CL_CAT(category)) . I.e. without a comma
// between the second to last command line argument and KLEE_CL_CAT
#ifdef KLEE_LLVM_CL3_3_BP
#define KLEE_CL_CAT(X) ,llvm::cl::cat(X) /*Set option category*/
#else
#define KLEE_CL_CAT(X) /*Expand to nothing*/
#endif

namespace klee {

#ifdef KLEE_LLVM_CL3_3_BP
extern llvm::cl::OptionCategory SolverOptionCategory;
#endif

extern llvm::cl::opt<bool> UseFastCexSolver;

extern llvm::cl::opt<bool> UseCexCache;

extern llvm::cl::opt<bool> UseCache;

extern llvm::cl::opt<bool> UseIndependentSolver; 

extern llvm::cl::opt<bool> DebugValidateSolver;
  
extern llvm::cl::opt<int> MinQueryTimeToLog;

extern llvm::cl::opt<double> MaxSTPTime;

///The different query logging solvers that can switched on/off
enum QueryLoggingSolverType
{
    ALL_PC,       ///< Log all queries (un-optimised) in .pc (KQuery) format
    ALL_SMTLIB,   ///< Log all queries (un-optimised)  .smt2 (SMT-LIBv2) format
    SOLVER_PC,    ///< Log queries passed to solver (optimised) in .pc (KQuery) format
    SOLVER_SMTLIB ///< Log queries passed to solver (optimised) in .smt2 (SMT-LIBv2) format
};

/* Using cl::list<> instead of cl::bits<> results in quite a bit of ugliness when it comes to checking
 * if an option is set. Unfortunately with gcc4.7 cl::bits<> is broken with LLVM2.9 and I doubt everyone
 * wants to patch their copy of LLVM just for these options.
 */
extern llvm::cl::list<QueryLoggingSolverType> queryLoggingOptions;


//A bit of ugliness so we can use cl::list<> like cl::bits<>, see queryLoggingOptions
template <typename T>
static bool optionIsSet(llvm::cl::list<T> list, T option)
{
    return std::find(list.begin(), list.end(), option) != list.end();
}

}

#endif	/* KLEE_COMMANDLINE_H */

