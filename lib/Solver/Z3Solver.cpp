#include "klee/Config/config.h"
#ifdef ENABLE_Z3
#include "Z3Builder.h"
#include "klee/Constraints.h"
#include "klee/Solver.h"
#include "klee/SolverImpl.h"
#include "klee/util/Assignment.h"
#include "klee/util/ExprUtil.h"

namespace klee {

class Z3SolverImpl : public SolverImpl {
private:
  Z3Builder *builder;
  double timeout;
  SolverRunStatus runStatusCode;
  ::Z3_params solverParameters;
  // Parameter symbols
  ::Z3_symbol timeoutParamStrSymbol;

public:
  Z3SolverImpl();
  ~Z3SolverImpl();

  char *getConstraintLog(const Query &);
  void setCoreSolverTimeout(double _timeout) {
    assert (_timeout >= 0.0 && "timeout must be >= 0");
    timeout = _timeout;

    unsigned int timeoutInMilliSeconds = (unsigned int) ((timeout * 1000) + 0.5);
    // HACK: The description of this solver parameter is
    // ```
    // timeout (unsigned int) timeout (in milliseconds) (0 means no timeout)
    // (default: 0)
    // ```
    // However Z3 seems to misbehave when the value of 0 is used. See
    // https://github.com/Z3Prover/z3/issues/445
    // Use UINT_MAX instead which gives a huge timeout which in practice we are
    // unlikely
    // to ever hit.
    if (timeoutInMilliSeconds == 0)
      timeoutInMilliSeconds = UINT_MAX;
    Z3_params_set_uint(builder->ctx,
                       solverParameters,
                       timeoutParamStrSymbol,
                       timeoutInMilliSeconds);
  }

  bool computeTruth(const Query &, bool &isValid);
  bool computeValue(const Query &, ref<Expr> &result);
  bool computeInitialValues(const Query &,
                            const std::vector<const Array *> &objects,
                            std::vector<std::vector<unsigned char> > &values,
                            bool &hasSolution);
  SolverRunStatus runAndGetCex(Z3Builder *builder, Z3_solver the_solver,
                               Z3ASTHandle q,
                               const std::vector<const Array *> &objects,
                               std::vector<std::vector<unsigned char> > &values,
                               bool &hasSolution);
  SolverRunStatus getOperationStatusCode();
};

Z3SolverImpl::Z3SolverImpl()
    : builder(new Z3Builder()), timeout(0.0),
      runStatusCode(SOLVER_RUN_STATUS_FAILURE) {
  assert(builder && "unable to create Z3Builder");
  solverParameters = Z3_mk_params(builder->ctx);
  Z3_params_inc_ref(builder->ctx, solverParameters);
  timeoutParamStrSymbol = Z3_mk_string_symbol(builder->ctx, "timeout");
  setCoreSolverTimeout(0.0); // Default to no timeout
}

Z3SolverImpl::~Z3SolverImpl() {
  Z3_params_dec_ref(builder->ctx, solverParameters);
  delete builder; }

/***/

Z3Solver::Z3Solver() : Solver(new Z3SolverImpl()) {}

char *Z3Solver::getConstraintLog(const Query &query) {
  return impl->getConstraintLog(query);
}

void Z3Solver::setCoreSolverTimeout(double timeout) {
  impl->setCoreSolverTimeout(timeout);
}

/***/

char *Z3SolverImpl::getConstraintLog(const Query &query) {
  Z3_solver the_solver = Z3_mk_simple_solver(builder->ctx);
  Z3_solver_inc_ref(builder->ctx, the_solver);
  Z3_solver_set_params(builder->ctx, the_solver, solverParameters);

  for (std::vector<ref<Expr> >::const_iterator it = query.constraints.begin(),
                                               ie = query.constraints.end();
       it != ie; ++it) {
    Z3_solver_assert(builder->ctx, the_solver, builder->construct(*it));
  }

  char* result = strdup(Z3_solver_to_string(builder->ctx, the_solver));
  Z3_solver_dec_ref(builder->ctx, the_solver);
  return result;
}

bool Z3SolverImpl::computeTruth(const Query &query, bool &isValid) {
  std::vector<const Array *> objects;
  std::vector<std::vector<unsigned char> > values;
  bool hasSolution;

  if (!computeInitialValues(query, objects, values, hasSolution))
    return false;

  isValid = !hasSolution;
  return true;
}

bool Z3SolverImpl::computeValue(const Query &query, ref<Expr> &result) {
  std::vector<const Array *> objects;
  std::vector<std::vector<unsigned char> > values;
  bool hasSolution;

  // Find the object used in the expression, and compute an assignment
  // for them.
  findSymbolicObjects(query.expr, objects);
  if (!computeInitialValues(query.withFalse(), objects, values, hasSolution))
    return false;
  assert(hasSolution && "state has invalid constraint set");

  // Evaluate the expression with the computed assignment.
  Assignment a(objects, values);
  result = a.evaluate(query.expr);

  return true;
}

bool Z3SolverImpl::computeInitialValues(
    const Query &query, const std::vector<const Array *> &objects,
    std::vector<std::vector<unsigned char> > &values, bool &hasSolution) {

  // FIXME: Don't make a new solver for every query!
  Z3_solver the_solver = Z3_mk_simple_solver(builder->ctx);
  Z3_solver_inc_ref(builder->ctx, the_solver);
  Z3_solver_set_params(builder->ctx, the_solver, solverParameters);

  runStatusCode = SOLVER_RUN_STATUS_FAILURE;

  TimerStatIncrementer t(stats::queryTime);

  for (ConstraintManager::const_iterator it = query.constraints.begin(),
                                         ie = query.constraints.end();
       it != ie; ++it) {
    Z3_solver_assert(builder->ctx, the_solver, builder->construct(*it));
  }
  ++stats::queries;
  ++stats::queryCounterexamples;

  Z3ASTHandle z3QueryExpr = Z3ASTHandle(builder->construct(query.expr), builder->ctx);

  runStatusCode =
      runAndGetCex(builder, the_solver, z3QueryExpr, objects, values, hasSolution);

  Z3_solver_dec_ref(builder->ctx, the_solver);

  if (runStatusCode == SolverImpl::SOLVER_RUN_STATUS_SUCCESS_SOLVABLE ||
      runStatusCode == SolverImpl::SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE) {
    if (hasSolution) {
      ++stats::queriesInvalid;
    } else {
      ++stats::queriesValid;
    }
    return true; // success
  }
  return false; // failed
}

SolverImpl::SolverRunStatus
Z3SolverImpl::runAndGetCex(Z3Builder *builder, Z3_solver the_solver, Z3ASTHandle q,
                           const std::vector<const Array *> &objects,
                           std::vector<std::vector<unsigned char> > &values,
                           bool &hasSolution) {
  Z3_solver_assert(builder->ctx, the_solver,
                   Z3ASTHandle(Z3_mk_not(builder->ctx, q), builder->ctx));

  Z3_lbool solverResult = Z3_solver_check(builder->ctx, the_solver);
  switch (solverResult) {
    case Z3_L_TRUE: {
      hasSolution = true;
      Z3_model theModel = Z3_solver_get_model(builder->ctx, the_solver);
      assert(theModel && "Failed to retrieve model");
      Z3_model_inc_ref(builder->ctx, theModel);
      values.reserve(objects.size());
      for (std::vector<const Array *>::const_iterator it = objects.begin(),
                                                      ie = objects.end();
           it != ie; ++it) {
        const Array *array = *it;
        std::vector<unsigned char> data;

        data.reserve(array->size);
        for (unsigned offset = 0; offset < array->size; offset++) {
          // FIXME: Can we use Z3ASTHandle here?
          ::Z3_ast counter;
          // WTF: Why are you calling Z3_mk_bv2int()??
          Z3ASTHandle initial_read = Z3ASTHandle(Z3_mk_bv2int(
              builder->ctx, builder->getInitialRead(array, offset), 0), builder->ctx);
          bool successfulEval = Z3_model_eval(builder->ctx,
                                              theModel,
                                              initial_read,
                                              /*model_completion=*/Z3_TRUE,
                                              &counter);
          assert(successfulEval && "Failed to evaluate model");
          Z3_inc_ref(builder->ctx, counter);
          int val = 0;
          bool successGet = Z3_get_numeral_int(builder->ctx, counter, &val);
          assert(successGet && "failed to get value back");
          data.push_back(val);
          Z3_dec_ref(builder->ctx, counter);
        }

        values.push_back(data);
      }

      Z3_model_dec_ref(builder->ctx, theModel);
      return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_SOLVABLE;
    }
    case Z3_L_FALSE:
      hasSolution = false;
      return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE;
    case Z3_L_UNDEF: {
      ::Z3_string reason =
          ::Z3_solver_get_reason_unknown(builder->ctx, the_solver);
      if (strcmp(reason, "timeout") == 0) {
        llvm::errs() << "timeout!\n";
        return SolverImpl::SOLVER_RUN_STATUS_TIMEOUT;
      }
      if (strcmp(reason, "unknown") == 0) {
        llvm::errs() << "unknown!\n";
        return SolverImpl::SOLVER_RUN_STATUS_FAILURE;
      }
      llvm::errs() << "Unexpected solver failure. Reason is \"" << reason
                   << "\"\n";
      abort();
    }
    default:
      llvm_unreachable("unhandled Z3 result");
  }
}

SolverImpl::SolverRunStatus Z3SolverImpl::getOperationStatusCode() {
  return runStatusCode;
}
}
#endif // ENABLE_Z3
