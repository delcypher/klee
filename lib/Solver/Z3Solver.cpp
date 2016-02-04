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

public:
  Z3SolverImpl();
  ~Z3SolverImpl();

  char *getConstraintLog(const Query &);
  void setCoreSolverTimeout(double _timeout) {
    timeout = _timeout;

    unsigned timeout_buffer_size = 100;
    char *timeout_amount = new char[timeout_buffer_size];

    int ret = snprintf(timeout_amount, timeout_buffer_size, "%lu",
                       (timeout > 0 ? ((uint64_t)(timeout * 1000)) : UINT_MAX));
    assert(ret >= 0 && "invalid timeout value specification");

    // llvm::errs() << "DDDD: Setting " << timeout_amount << "\n";
    Z3_global_param_set("timeout", timeout_amount);
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
}

Z3SolverImpl::~Z3SolverImpl() { delete builder; }

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

  Z3_params params = Z3_mk_params(builder->ctx);
  Z3_params_inc_ref(builder->ctx, params);
  Z3_symbol r = Z3_mk_string_symbol(builder->ctx, ":timeout");
  Z3_params_set_uint(builder->ctx, params, r,
                     (timeout > 0 ? (uint64_t)(timeout * 1000) : UINT_MAX));
  Z3_solver_set_params(builder->ctx, the_solver, params);
  Z3_params_dec_ref(builder->ctx, params);

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

  Z3_params params = Z3_mk_params(builder->ctx);
  Z3_params_inc_ref(builder->ctx, params);
  Z3_symbol r = Z3_mk_string_symbol(builder->ctx, ":timeout");
  Z3_params_set_uint(builder->ctx, params, r,
                     (timeout > 0 ? (uint64_t)(timeout * 1000) : UINT_MAX));
  Z3_solver_set_params(builder->ctx, the_solver, params);
  Z3_params_dec_ref(builder->ctx, params);

  runStatusCode = SOLVER_RUN_STATUS_FAILURE;

  TimerStatIncrementer t(stats::queryTime);

  for (ConstraintManager::const_iterator it = query.constraints.begin(),
                                         ie = query.constraints.end();
       it != ie; ++it) {
    Z3_solver_assert(builder->ctx, the_solver, builder->construct(*it));
  }
  ++stats::queries;
  ++stats::queryCounterexamples;

  Z3ASTHandle stp_e = Z3ASTHandle(builder->construct(query.expr), builder->ctx);

  runStatusCode =
      runAndGetCex(builder, the_solver, stp_e, objects, values, hasSolution);

  if (hasSolution)
    ++stats::queriesInvalid;
  else
    ++stats::queriesValid;
  Z3_solver_dec_ref(builder->ctx, the_solver);
  return true; // FIXME: this is wrong!
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
      Z3_model m = Z3_solver_get_model(builder->ctx, the_solver);
      if (m) Z3_model_inc_ref(builder->ctx, m);
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
          bool successfulEval = Z3_model_eval(builder->ctx, m, initial_read, Z3_TRUE, &counter);
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

      if (m) Z3_model_dec_ref(builder->ctx, m);
      return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_SOLVABLE;
    }
    default:
      hasSolution = false;
      return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE;
  }
}

SolverImpl::SolverRunStatus Z3SolverImpl::getOperationStatusCode() {
  return runStatusCode;
}
}
#endif // ENABLE_Z3
