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

#include "SolverStats.h"


using namespace std;
namespace klee
{
	class SMTLIBSolverImpl : public SolverImpl
	{
		private:
		  string pathToSolver;
		  string pathToSolverInputFile; //< The .smt2 file
		  string pathToSolverOutputFile; //< The result from the solver
		  SMTLIBOutputLexer lexer;

		  timespec timeout;
		  timespec startTime;

		  // This is the exit code we use for a failed execution of the child process
		  // Hopefully it doesn't conflict with the exit code from any solver.
		  static const int specialExitCode=57;

		  void giveUp();

		  bool haveRunOutOfTime();

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
  						pathToSolverInputFile(_pathToOutputTempFile),
  						pathToSolverOutputFile(_pathToInputTempFile)

  	{
  		timeout.tv_nsec = timeout.tv_sec = 0;

  		cerr << "Using external SMTLIBv2 Solver:" << pathToSolver << endl;
  		cerr << "Path to SMTLIBv2 query file:" << pathToSolverInputFile << endl;
  		cerr << "Path to SMTLIBv2 Solver response file:" << pathToSolverOutputFile << endl;
  	}

  	void SMTLIBSolverImpl::giveUp()
  	{
  		klee_error("SMTLIBSolverImpl: Giving up!");
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
		//update statistics
		++stats::queries;
		//we only query for a "counter example" is objects is not empty!
		if(!objects.empty()) ++stats::queryCounterexamples;


		if(!generateSMTLIBv2File(query,objects))
			return false;

		if(!invokeSolver())
			return false;

		if(!parseSolverOutput(objects,values,hasSolution))
			return false;

		/* Odd but this is how the reset of klee works
		 * sat == INVALID
		 * unsat == VALID
		 */
	    if (hasSolution)
	      ++stats::queriesInvalid;
	    else
	      ++stats::queriesValid;


		return true;
	}


	bool SMTLIBSolverImpl::invokeSolver()
	{
		//Record the start time
		if(clock_gettime(CLOCK_MONOTONIC,&startTime)==-1)
		{
			cerr << "SMTLIBSolverImpl: Failed to record start time." << endl;
		}

		/* before we fork we need to flush stdout.
		 * If we don't the parent and child have the unflushed stdout
		 * which can get outputted twice because both the parent and child flush stdout
		 * see http://stackoverflow.com/questions/3513242/working-of-fork-in-linux-gcc
		 */
		fflush(stdout);
		fflush(stderr);

		//Perform fork
		pid_t childPid = fork();
		if(childPid == -1)
		{
			klee_error("SMTLIBSolverImpl: Failed to fork!");
			return false;
		}

		if(childPid > 0)
		{
			//parent code
			int status=0;
			int result=0;

			/* This is a disgusting waste of CPU time. We've effectively got a polling wait
			 * because KLEE has an interval timer set (see ExecutorTimers.cpp) to emit SIGALRM
			 * periodically which interrupts waitpid()
			 *
			 * A more elegant solution than using waitpid() is to use sigtimedwait() (in conjunction
			 * with waitpid() so we reap the child) for the timedwait but this requires that we block
			 * SIGALRM which disrupts KLEE keeping track of time. For now this will do
			 */
			do
			{
				result=waitpid(childPid,&status,0);
			} while(result == -1 && errno == EINTR && !haveRunOutOfTime());

			if(haveRunOutOfTime())
			{
				klee_warning("SMTLIBSolverImpl: The Solver timed out!");
				return false;
			}

			//Now we will do a clean up of the child process.
			if(result < 0 )
			{
				klee_warning("SMTLIBSolverImpl: Failed to clean up child process.");
				return false;
			}

			//Check that the child terminated normally (i.e. not via a signal).
			if(WIFEXITED(status))
			{
				/* We cannot assume the solver exit code (WEXITSTATUS(status)) will be 0
				 * because we may ask (check-sat) and go on to ask for array values as well (via (get-value () ).
				 * If the solver returns "unsat" then it is incorrect to ask for array values which will result
				 * in an error. The solver may give a bad exit code in this case but hopefully we still have parsable
				 * output.
				 */

				//check for our specialExitCode that indicates the child process failed in some way.
				if(WEXITSTATUS(status) == specialExitCode)
				{
					klee_error("SMTLIBSolverImpl: The solver could not be executed.");
					return false;
				}


				//We interpret any exit code (except the specialExitCode) of as a successful run of the solver
				return true;

			}
			else
			{
				klee_error("SMTLIBSolverImpl: The Solver didn't exit normally.");
				return false;
			}

		}
		else
		{
			//child code


			//open the output file (truncate it) for the child and have stdout go into it
			if(freopen(pathToSolverOutputFile.c_str(),"w",stdout)==NULL)
			{
				klee_error("SMTLIBSolverImpl (Child): Child failed to redirect stdout.");
				exit(specialExitCode);
			}

			/* Invoke the solver. We pass it as the 1st argument the name of SMTLIBv2 file we generated
			 * earlier.
			 */
			if(execlp(pathToSolver.c_str(), pathToSolver.c_str(), pathToSolverInputFile.c_str(), (char*) NULL) == -1)
			{
				//We failed to invoke the solver
				switch(errno)
				{
					case ENAMETOOLONG:
						klee_warning("SMTLIBSolverImpl (child): The SMTLIBv2 solver path is too long!");
						exit(specialExitCode);
					case ENOENT:
						cerr << "SMTLIBSolverImpl (child): The executable " << pathToSolver << " does not exist!" << endl;
						exit(specialExitCode);
					default:
						cerr << "SMTLIBSolverImpl (child): Failed to invoke solver (" << pathToSolver << ")" << endl;
						exit(specialExitCode);
				}
			}


		}

	}

	bool SMTLIBSolverImpl::parseSolverOutput(const std::vector<const Array*> &objects,
			std::vector< std::vector<unsigned char> > &values,
			bool &hasSolution)
	{
		//open the output from the solver ready to parse
		ifstream file(pathToSolverOutputFile.c_str());

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
				cerr << "SMTLIBSolverImpl : Unexpected token `" << lexer.getLastTokenContents() << "`" << endl;
				giveUp();
				return false;
		}

		//If we reach here the solver thought the assertions where satisfiable.
		if(objects.empty())
		{
			//we weren't ask to get any values
			return true;
		}

		//Preemptively make space seeing as we known how many arrays there are.
		values.reserve(objects.size());

		/* We expected output like
		 * (((select unnamed_1 (_ bv0 32) ) #x20))
		 */


		unsigned int arrayNumber=0;
		unsigned char byteValue=0;
		//Loop over the arrays to retrieve their values.
		for(std::vector<const Array*>::const_iterator it=objects.begin(); it!=objects.end(); it++, arrayNumber++)
		{
			//The raw bits for this array will go in here
			std::vector<unsigned char> data;
			data.reserve((*it)->size);

			//Loop over the bytes in the array
			for(unsigned int byteNumber=0; byteNumber < (*it)->size; byteNumber++)
			{


				// Expect "((("
				for(int c=0; c <3 ; c++)
				{
					if(!lexer.getNextToken(t) || t!=SMTLIBOutputLexer::LBRACKET_TOKEN)
					{
						klee_error("SMTLIBSolverImpl: Lexer failed to get token for array assignment. Expected `(`");
						return false;
					}
				}

				// Expect "select"
				if(!lexer.getNextToken(t) || t!=SMTLIBOutputLexer::SELECT_TOKEN)
				{
					klee_error("SMTLIBSolverImpl: Lexer failed to get token for array assignment. Expected `select`");
					return false;
				}

				// Expect the array name
				if(!lexer.getNextToken(t) ||
				   t!=SMTLIBOutputLexer::ARRAY_IDENTIFIER_TOKEN ||
				   (*it)->name != lexer.getLastTokenContents())
				{
					cerr << "SMTLIBSolverImpl: Lexer failed to get array identifier token." << endl <<
							"Expected array name `" << (*it)->name << "`. Instead received token `" << lexer.getLastTokenContents() <<
							"`" << endl;
					giveUp();
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
					giveUp();
					return false;
				}

				//Expect ")"
				if(!lexer.getNextToken(t) || t!=SMTLIBOutputLexer::RBRACKET_TOKEN)
				{
					klee_error("SMTLIBSolverImpl: Lexer failed to get token for array assignment. Expected `)`");
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
					klee_error("SMTLIBSolverImpl : Lexer failed to get token for array assignment."
							     " Expected bitvector value.");
					return false;
				}

				if(!lexer.getLastNumericValue(determinedByteValue))
				{
					klee_error("SMTLIBSolverImpl : Lexer could not get the numeric value of the "
							     "found bitvector constant");
					return false;
				}

				if(determinedByteValue > 255)
				{
					klee_error("SMTLIBSolverImpl: Determined value for bitvector byte was out of range!");
				}

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
						klee_error("SMTLIBSolverImpl: Lexer failed to get token for array assignment. Expected `)`");
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
		ofstream output(pathToSolverInputFile.c_str(),ios_base::trunc);

		//check we can write to it
		if(output.bad())
		{
			cerr << "Can't write output SMTLIBv2 (input to solver) " << pathToSolverInputFile << endl;
			giveUp();
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
			klee_error("There was a problem writing the SMTLIBv2 file");
			return false;
		}

		output.close();
		return true;
	}

	bool SMTLIBSolverImpl::haveRunOutOfTime()
	{
		timespec currentTime;
		timespec elapsedTime;
		if(clock_gettime(CLOCK_MONOTONIC,&currentTime)==-1)
		{
			cerr << "SMTLIBSolverImpl: Couldn't determine current time!" << endl;
			return true;
		}

		if(timeout.tv_sec == 0)
			return false; //The timeout is disabled, we can never run out of time!

		elapsedTime.tv_sec = (currentTime.tv_sec - startTime.tv_sec) +1;
		//ignore nanoseconds.
		if(elapsedTime.tv_sec > timeout.tv_sec)
			return true; //we've run out of time.
		else
			return false;//we've got some time left.
	}

}


