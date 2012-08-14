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

#include <signal.h>
#include <time.h>
#include <unistd.h>
#include <errno.h>
#include <sys/wait.h>


using namespace std;
namespace klee
{
	class SMTLIBSolverImpl : public SolverImpl
	{
		private:
		  string pathToSolver;
		  string pathToOutputTempFile;
		  string pathToInputTempFile;

		  timespec timeout;

		  bool generateSMTLIBv2File(const Query& q, const std::vector<const Array*> arrays);
		  bool invokeSolver();
		  bool parseSolverOutput();


		public:

		  	SMTLIBSolverImpl(const string& _pathToSolver,
		  			         const string& _pathToOutputTempFile,
		  			         const string& _pathToInputTempFile
		  					);
		  	~SMTLIBSolverImpl() {}


		  	///Set the time in seconds to wait for the solver to complete.
		  	///This time is rounded to the nearest second.
		  	///The default is 0 (i.e. no timeout)
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
  						pathToInputTempFile(_pathToInputTempFile)

  	{
  		timeout.tv_nsec = timeout.tv_sec = 0;

  		cout << "Using Solver:" << pathToSolver << endl;
  		cout << "Path to SMTLIBv2 query file:" << pathToOutputTempFile << endl;
  		cout << "Path to SMTLIBv2 Solver response file:" << pathToInputTempFile << endl;
  	}

  	void SMTLIBSolverImpl::setTimeout(double _timeout)
	{
  		if(_timeout < 0.0)
  		{
  			timeout.tv_nsec=0;
  			timeout.tv_sec=0;
  		}
  		else
  		{
  			timeout.tv_nsec=0;
  			//the +0.5 is to simulate rounding
  			timeout.tv_sec=static_cast<unsigned int>(_timeout + 0.5);
  		}
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
		/* We need to block the SIGCHLD signal so that the parent receives the signal when it is
		 * ready for it and not before (e.g. child could finish before parent calls waitpid() )
		 */
		sigset_t mask;
		sigemptyset(&mask);
		sigaddset(&mask,SIGCHLD);

		int status=0;

		if(sigprocmask(SIG_BLOCK,&mask,NULL) < 0)
		{
			klee_warning("SMTLIBSolverImpl: Failed to block SIGCHLD");
			return false;
		}


		//Perform fork
		pid_t childPid = fork();
		if(childPid == -1)
		{
			klee_warning("SMTLIBSolverImpl: Failed to fork!");
			return false;
		}

		if(childPid > 0)
		{
			//Parent code
			while(true)
			{
				signed int signalReceived=0;
				//Wait for child
				if(timeout.tv_sec > 0)
				{
					//Suspend with timeout
					signalReceived = sigtimedwait(&mask,NULL,&timeout);
				}
				else
				{
					//There is no timeout, just suspend until we get a signal
					signalReceived = sigwaitinfo(&mask,NULL);
				}


				if( signalReceived < 0)
				{

					if(errno ==EINTR)
					{
						/*We were interrupted by another signal that wasn't SIGCHLD.
						 *  For now we will just restart the timeout.
						 */
						klee_warning("SMTLIBSolverImpl: Interrupted by unexpected signal.");
						continue;//restart the loop
					}
					else if(errno==EAGAIN)
					{
						/* The Solver timed out */
						kill(childPid,SIGKILL); //Kill the child.
						return false; //For now we'll tell KLEE we failed (fixme maybe?)
					}
					else
					{
						klee_warning("SMTLIBSolverImpl: Something went wrong waiting for solver");
						return false;
					}

				}
				else
				{
					//The child "finished" without timing out. We're not handling special cases.
					break;
				}


			}

			//Now we will do a clean up of the child process.
			if(waitpid(childPid,&status,WNOHANG) < 0 )
			{
				klee_warning("SMTLIBSolverImpl: Failed to clean up child process.");
				return false;
			}

			//Check that the child terminated normally (i.e. not via a signal).
			if(WIFEXITED(status))
			{
				if(WEXITSTATUS(status) ==0)
				{
					//We interpret an exit code of 0 as a successful run of the solver
					return true;
				}
				else
				{
					klee_warning("SMTLIBSolverImpl: The solver execution failed.");
					return false; //The solver failed
				}
			}
			else
			{
				klee_warning("SMTLIBSolverImpl: The Solver didn't exit normally.");
				return false;
			}

		}
		else
		{
			//child code

			/* reenable SIGCHLD (the mask is preserved across execv and fork)
			 * so the solver might do its own forking and we don't want to mess with
			 * that!
			 */
			if(sigprocmask(SIG_UNBLOCK,&mask,NULL) < 0)
			{
				klee_warning("SMTLIBSolverImpl: Child failed to re-enable SIGCHLD signal");
				exit(EXIT_FAILURE);
			}

			//open the output file (truncate it) for the child and have stdout go into it
			freopen(pathToInputTempFile.c_str(),"w",stdout);

			/* Invoke the solver. We pass it as the 1st argument the name of SMTLIBv2 file we generated
			 * earlier.
			 */
			if(execlp(pathToSolver.c_str(), pathToSolver.c_str(), pathToOutputTempFile.c_str(), (char*) NULL) == -1)
			{
				//We failed to invoke the solver
				switch(errno)
				{
					case ENAMETOOLONG:
						klee_warning("SMTLIBSolverImpl (child): The SMTLIBv2 solver path is too long!");
						exit(EXIT_FAILURE);
					case ENOENT:
						cerr << "SMTLIBSolverImpl (child): The executable " << pathToSolver << " does not exist!" << endl;
						exit(EXIT_FAILURE);
					default:
						cerr << "SMTLIBSolverImpl (child): Failed to invoke solver (" << pathToSolver << ")" << endl;
						exit(EXIT_FAILURE);
				}
			}


		}

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

