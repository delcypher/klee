#include "klee/SMTLIBSolver.h"
#include "klee/SolverImpl.h"
#include <string>

//for findSymbolicObjects()
#include "klee/util/ExprUtil.h"

#include "klee/util/Assignment.h"

//remove me
#include <iostream>

using namespace std;
namespace klee
{
	class SMTLIBSolverImpl : public SolverImpl
	{
		private:
		  string pathToSolver;
		  string pathToOutputTempFile;
		  string pathToInputTempFile;
		  double timeout;

		public:

		  	SMTLIBSolverImpl(const string& _pathToSolver,
		  			         const string& _pathToOutputTempFile,
		  			         const string& _pathToInputTempFile
		  					);
		  	~SMTLIBSolverImpl() {}


			void setTimeout(double _timeout);

			bool computeTruth(const Query&, bool &isValid);
			bool computeValue(const Query&, ref<Expr> &result);
			bool computeInitialValues(const Query&,
									const std::vector<const Array*> &objects,
									std::vector< std::vector<unsigned char> > &values,
									bool &hasSolution);

	};




	SMTLIBSolver::SMTLIBSolver(std::string& pathToSolver,
			const std::string& pathToOutputTempFile,
			const std::string& pathToInputTempFile) :
	SolverWithTimeOut( new SMTLIBSolverImpl(pathToSolver,pathToOutputTempFile,pathToInputTempFile))
	{
		//check solver exists and is executable.
	}

	void SMTLIBSolver::setTimeout(double timeout)
	{
		static_cast<SMTLIBSolverImpl*>(impl)->setTimeout(timeout);
	}

	/*
	 *  Implementation of SMTLIBSolverImpl methods
	 */

  	SMTLIBSolverImpl::SMTLIBSolverImpl(const string& _pathToSolver,
  			         const string& _pathToOutputTempFile,
  			         const string& _pathToInputTempFile
  					) : pathToSolver(_pathToSolver),
  						pathToOutputTempFile(_pathToOutputTempFile),
  						pathToInputTempFile(_pathToInputTempFile),
  						timeout(0)
  	{
  		cout << "Test solver:" << pathToSolver << endl;
  		cout << "path to temp out:" << pathToOutputTempFile << endl;
  		cout << "path to input temp:" << pathToInputTempFile << endl;
  	}

  	void SMTLIBSolverImpl::setTimeout(double _timeout)
	{
  		if(_timeout < 0.0)
  			timeout=0;
  		else
  			timeout=_timeout;
	}


  	bool SMTLIBSolverImpl::computeTruth(const Query& query,
  	                                 bool &isValid) {
  	  std::vector<const Array*> objects;
  	  std::vector< std::vector<unsigned char> > values;
  	  bool hasSolution;

  	  if (!computeInitialValues(query, objects, values, hasSolution))
  	    return false;

  	  isValid = !hasSolution;
  	  return true;
  	}

  	bool SMTLIBSolverImpl::computeValue(const Query& query,
  	                                 ref<Expr> &result) {
  	  std::vector<const Array*> objects;
  	  std::vector< std::vector<unsigned char> > values;
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

	bool SMTLIBSolverImpl::computeInitialValues(const Query&,
							const std::vector<const Array*> &objects,
							std::vector< std::vector<unsigned char> > &values,
							bool &hasSolution)
	{
		//TODO
		return false;
	}

}
