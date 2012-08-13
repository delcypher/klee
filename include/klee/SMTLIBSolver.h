#ifndef SMTLIBSOLVER_H_
#define SMTLIBSOLVER_H_

#include <string>
#include "klee/Solver.h"

namespace klee
{

	class SMTLIBSolver : public SolverWithTimeOut
	{
		public:
		SMTLIBSolver(std::string& pathToSolver, const std::string& pathToOutputTempFile, const std::string& pathToInputTempFile);

		void setTimeout(double timeout);

		SolverType getType() { return Solver::SMTLIBv2; }
	};

}


#endif /* SMTLIBSOLVER_H_ */
