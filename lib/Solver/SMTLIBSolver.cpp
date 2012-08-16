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

#include "SMTLIBOutputLexer.h"


using namespace std;
namespace klee
{
	class SMTLIBSolverImpl : public SolverImpl
	{
		private:
		  string pathToSolver;
		  string pathToOutputTempFile; //< The .smt2 file
		  string pathToInputTempFile; //< The result from the solver
		  SMTLIBOutputLexer lexer;

		  timespec timeout;

		  bool generateSMTLIBv2File(const Query& q, const std::vector<const Array*> arrays);
		  bool invokeSolver();
		  bool parseSolverOutput(const std::vector<const Array*> &objects,
					std::vector< std::vector<unsigned char> > &values,
					bool &hasSolution);


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

		if(!parseSolverOutput(objects,values,hasSolution))
			return false;

		return true;
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
			//HACK. KLEE's request of SIGALRM interupts sigtimedwait() and sigwaitinfo()
			//We disable it here just to make the code here work as its supposed to.
			//FIXME
			sigset_t alrm_mask;
			sigemptyset(&alrm_mask);
			sigaddset(&alrm_mask,SIGALRM);
			if(sigprocmask(SIG_BLOCK,&alrm_mask,NULL) < 0)
				klee_warning("failed to block ALRM");


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
						klee_warning("SMTLIBSolverImpl: Solver timed out!");
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

					//hack allow SIGALRM again
					if(sigprocmask(SIG_UNBLOCK,&alrm_mask,NULL) < 0)
						klee_warning("failed to unblock ALRM");

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
				/* We cannot use the solver exit code (WEXITSTATUS(status)) to determine "failure"
				 * because we may ask (check-sat) and go on to ask for array values as well (via (get-value () ).
				 * If the solver returns "unsat" then it is incorrect to ask for array values which will result
				 * in an error. The solver may give a bad exit code in this case but hopefully we still have parsable
				 * output.
				 */

				//We interpret any exit code of as a successful run of the solver
				return true;

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

	bool SMTLIBSolverImpl::parseSolverOutput(const std::vector<const Array*> &objects,
			std::vector< std::vector<unsigned char> > &values,
			bool &hasSolution)
	{
		//open the output from the solver ready to parse
		ifstream file(pathToInputTempFile.c_str());

		if(!file.good())
			return false;

		lexer.setInput(file);

		SMTLIBOutputLexer::Token t=SMTLIBOutputLexer::UNRECOGNISED_TOKEN;


		/* The first thing we want to check is if the solver thought the
		 * set of assertions was satisfiable
		 */
		if(!lexer.getNextToken(t))
		{
			klee_warning("SMTLIBSolverImpl: Lexer failed to get token");
			return false;
		}

		switch(t)
		{
			case SMTLIBOutputLexer::UNKNOWN_TOKEN:
				klee_warning("SMTLIBSolverImpl : Solver responded unknown");
				return false;
			case SMTLIBOutputLexer::UNSAT_TOKEN:
				//not satisfiable
				hasSolution=false;
				return true;
			case SMTLIBOutputLexer::SAT_TOKEN:
				hasSolution=true;
				break;
			default:
				klee_warning("SMTLIBSolverImpl : Unexpected token");
				return false;
		}

		//If we reach here the solver thought the assertions where satisfiable.
		if(objects.empty())
		{
			//we weren't ask to get any values
			return true;
		}

		//Make sure the values vector of vectors has enough slots
		//values.reserve(objects.size());

		/* We expected output like
		 * (((select unnamed_1 (_ bv0 32) ) #x20))
		 */


		unsigned int arrayNumber=0;
		unsigned char byteValue=0;
		//Loop over the arrays to retrieve their values.
		for(std::vector<const Array*>::const_iterator it=objects.begin(); it!=objects.end(); it++, arrayNumber++)
		{
			//make sure the values vector has enough slots
			//values[arrayNumber].reserve((*it)->size);
			std::vector<unsigned char> data;

			//Loop over the bytes in the array
			for(unsigned int byteNumber=0; byteNumber < (*it)->size; byteNumber++)
			{


				// Expect "((("
				for(int c=0; c <3 ; c++)
				{
					if(!lexer.getNextToken(t) || t!=SMTLIBOutputLexer::LBRACKET_TOKEN)
					{
						klee_warning("SMTLIBSolverImpl: Lexer failed to get token for array assignment. Expected `(`");
						return false;
					}
				}

				// Expect "select"
				if(!lexer.getNextToken(t) || t!=SMTLIBOutputLexer::SELECT_TOKEN)
				{
					klee_warning("SMTLIBSolverImpl: Lexer failed to get token for array assignment. Expected `select`");
					return false;
				}

				// Expect the array name
				if(!lexer.getNextToken(t) ||
				   t!=SMTLIBOutputLexer::ARRAY_IDENTIFIER_TOKEN ||
				   (*it)->name != lexer.getLastTokenContents())
				{
					klee_warning("SMTLIBSolverImpl: Lexer failed to get token for array assignment.");
					cerr << "Expected array name `" << (*it)->name << "`. Instead received token `" << lexer.getLastTokenContents() <<
							"`" << endl;
					return false;
				}

				// Expect the array index
				unsigned long foundByteNumber=0;
				if(!lexer.getNextToken(t) ||
				   t!=SMTLIBOutputLexer::NUMERAL_BASE10_TOKEN ||
				   !lexer.getLastNumericValue(foundByteNumber) ||
				   foundByteNumber != byteNumber
				)
				{
					klee_warning("SMTLIBSolverImpl : Lexer failed to get token for array assignment.");
					cerr << "Expected (_ bv" << foundByteNumber << " " << (*it)->getDomain() << " ). Instead received"
							"token " << lexer.getLastTokenContents() << endl;
					return false;
				}

				//Expect ")"
				if(!lexer.getNextToken(t) || t!=SMTLIBOutputLexer::RBRACKET_TOKEN)
				{
					klee_warning("SMTLIBSolverImpl: Lexer failed to get token for array assignment. Expected `)`");
					return false;
				}


				//Expect the array value, we support multiple formats
				unsigned long determinedByteValue=0;
				if(!lexer.getNextToken(t) ||
						(t!=SMTLIBOutputLexer::NUMERAL_BASE10_TOKEN &&
						 t!=SMTLIBOutputLexer::NUMERAL_BASE16_TOKEN &&
						 t!=SMTLIBOutputLexer::NUMERAL_BASE2_TOKEN
						)
				)
				{
					klee_warning("SMTLIBSolverImpl : Lexer failed to get token for array assignment.");
					cerr << "Expected bitvector value." << endl;
					return false;
				}

				if(!lexer.getLastNumericValue(determinedByteValue))
				{
					klee_warning("SMTLIBSolverImpl : Lexer could not get the numeric value of the found bitvector constant");
					return false;
				}

				assert(determinedByteValue <= 255 && "Determined value for bitvector byte was out of range!"); //check in range

				byteValue = determinedByteValue;

				/* Perform the assignment. We assume for now the the "byteNumber"
				 * corresponds with what KLEE expects.
				 */
				data.push_back(byteValue);


				// Expect "))"
				for(int c=0; c <2 ; c++)
				{
					if(!lexer.getNextToken(t) || t!=SMTLIBOutputLexer::RBRACKET_TOKEN)
					{
						klee_warning("SMTLIBSolverImpl: Lexer failed to get token for array assignment. Expected `)`");
						return false;
					}
				}



			}

			values.push_back(data);


		}

		//We found satisfiability and determined the array values successfully.
		return true;
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

