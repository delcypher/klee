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

		//If not called no file size logging will be done.
		void setRecordQueryFileSizes(const std::string& logPath );

		SolverType getType() { return Solver::SMTLIBv2; }
	};

}


#endif /* SMTLIBSOLVER_H_ */
