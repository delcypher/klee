#include "klee/SMTLIBSolver.h"
#include "klee/SolverImpl.h"
#include <string>
#include "klee/util/ExprSMTLIBPrinter.h"

//for findSymbolicObjects()
#include "klee/util/ExprUtil.h"

#include "klee/util/Assignment.h"
#include "../Core/Common.h"

//remove me
#include <iostream>

#include <fstream>

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

		  bool generateSMTLIBv2File(const Query& q, const std::vector<const Array*> arrays);
		  bool invokeSolver();
		  bool parseSolverOutput();


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

  	  // Find the objects used in the expression, and compute an assignment
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

	bool SMTLIBSolverImpl::computeInitialValues(const Query& query,
							const std::vector<const Array*> &objects,
							std::vector< std::vector<unsigned char> > &values,
							bool &hasSolution)
	{
		if(!generateSMTLIBv2File(query,objects))
			return false;

		if(!invokeSolver())
			return false;

		if(!parseSolverOutput())
			return false;

		//Assign values
		//TODO
		return false;
	}


	bool SMTLIBSolverImpl::invokeSolver()
	{
		//TODO
		return false;
	}

	bool SMTLIBSolverImpl::parseSolverOutput()
	{
		//TODO
		return false;
	}

	bool SMTLIBSolverImpl::generateSMTLIBv2File(const Query& q, const std::vector<const Array*> arrays)
	{
		//open output SMTLIBv2 file and truncate it
		ofstream output(pathToOutputTempFile.c_str(),ios_base::trunc);

		//check we can write to it
		if(output.bad())
		{
			klee_warning("Can't write output SMTLIBv2 file");
			return false;
		}

		ExprSMTLIBPrinter printer(output,q);

		//set options
		printer.setLogic(ExprSMTLIBPrinter::QF_AUFBV);
		printer.setHumanReadable(false);
		printer.setArrayValuesToGet(arrays);

		//Generate SMTLIBv2 file containing the query
		printer.generateOutput();

		if(output.bad())
		{
			klee_warning("There was a problem writing the SMTLIBv2 file");
			return false;
		}

		output.close();
		return true;
	}


}

