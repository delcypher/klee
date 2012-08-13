#ifndef SMTLIBSOLVER_H_
#define SMTLIBSOLVER_H_

#include <string>
#include "Solver.h"

namespace klee
{

	class SMTLIBSolver : public Solver
	{
		public:
		SMTLIBSolver(std::string& pathToSolver, const std::string& pathToOutputTempFile, const std::string& pathToInputTempFile) :
		Solver(NULL)
		{

		}

		void setTimeout(double timeout)
		{

		}
	};

}


#endif /* SMTLIBSOLVER_H_ */
