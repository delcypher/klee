#ifndef KLEE_EXPRSMTLIBPRINTER_H
#define KLEE_EXPRSMTLIBPRINTER_H

#include <ostream>
#include <string>
#include <set>
#include <stack>
#include <map>
#include <klee/Constraints.h>
#include <klee/Expr.h>
#include <klee/util/PrintContext.h>
#include <klee/Solver.h>

namespace klee {

	///Base Class for SMTLIBv2 printer for Expr trees
	///This printer does not abbreviate expressions.
	class ExprSMTLIBPrinter
	{
		public:
			///Output stream to write to
			std::ostream& o;

			///The query to print
			const Query& query;

			///Contains the arrays found during scans
			std::set<const Array*> usedArrays;

			///Different SMTLIBv2 logics supported by this class
			/// \sa setLogic()
			enum SMTLIBv2Logic
			{
				QF_ABV,  ///< Logic using Theory of Arrays and Theory of Bitvectors
				QF_AUFBV ///< Logic using Theory of Arrays and Theory of Bitvectors and has uninterpreted functions
			};

			///Different SMTLIBv2 options that have a boolean value that can be set
			/// \sa setSMTLIBboolOption
			enum SMTLIBboolOptions
			{
				PRINT_SUCCESS, ///< print-success SMTLIBv2 option
				PRODUCE_MODELS,///< produce-models SMTLIBv2 option
				INTERACTIVE_MODE ///< interactive-mode SMTLIBv2 option
			};

			enum ConstantDisplayMode
			{
				BINARY,///< Display bit vector constants in binary e.g. #b00101101
				HEX, ///< Display bit vector constants in Hexidecimal e.g.#x2D
				DECIMAL ///< Display bit vector constants in Decimal e.g. (_ bv45 8)
			};



			///Allows the way Constant bitvectors are printed to be changed.
			/// \return true if setting the mode was successful
			bool setConstantDisplayMode(ConstantDisplayMode cdm);

			ConstantDisplayMode getConstantDisplayMode() { return cdm;}

			///Create a new printer that will print a query in the SMTLIBv2 language to a std::ostream
			/// \param output is the output stream that will be written to.
			/// \param q is the query that will be printed.
			ExprSMTLIBPrinter(std::ostream& output, const Query& q);

			virtual ~ExprSMTLIBPrinter() { }

			/// Print the query to the std::ostream
			/// All options should be set before calling this.
			/// \sa setConstantDisplayMode
			/// \sa setLogic()
			/// \sa setHumanReadable
			/// \sa setSMTLIBboolOption
			/// \sa setArrayValuesToGet
			///
			/// It does not matter what order the options are set in.
			void generateOutput();

			///Set which SMTLIBv2 logic to use.
			///This only affects what logics is used in the (set-logic <logic>) command.
			///The rest of the printed SMTLIBv2 commands are the same regardless of the logic used.
			///
			/// \return true if setting logic was successful.
			bool setLogic(SMTLIBv2Logic l);

			///Sets how readable the printed SMTLIBv2 commands are.
			/// \param hr If set to true the printed commands are made more human readable.
			///
			/// The printed commands are made human readable by indenting and line breaking
			/// appropriately.
			void setHumanReadable(bool hr);

			///Set SMTLIB options.
			/// These options will be printed when generateOutput() is called via
			/// the SMTLIBv2 command (set-option :option-name <value>)
			///
			/// By default no options will be printed so the SMTLIBv2 solver will use
			/// its default values for all options.
			///
			/// \return true if option was successfully set.
			bool setSMTLIBboolOption(SMTLIBboolOptions option, bool value);

			/// Set the array names that the SMTLIBv2 solver will be asked to determine.
			/// Calling this method implies the PRODUCE_MODELS option is true.
			///
			/// If no call is made to this function before ExprSMTLIBPrinter::generateOutput() then
			/// the solver will only be asked to check satisfiability.
			void setArrayValuesToGet(const std::vector<const Array*>& a);


		protected:

			//Print an initial SMTLIBv2 comment before anything else is printed
			virtual void printNotice();

			//Print SMTLIBv2 options e.g. (set-option :option-name <value>) command
			virtual void printOptions();

			//Print SMTLIBv2 logic to use e.g. (set-logic QF_ABV)
			virtual void printSetLogic();

			//Print SMTLIBv2 assertions for constant arrays
			virtual void printArrayDeclarations();

			//Print SMTLIBv2 for all constraints in the query
			virtual void printConstraints();

			//Print SMTLIBv2 assert statement for the "mangled" query
			virtual void printQuery();

			///Print the SMTLIBv2 command to check satisfiability and also optionally request for values
			/// \sa setArrayValuesToGet()
			virtual void printAction();

			///Print the SMTLIBv2 command to exit
			virtual void printExit();

			///Print a Constant in the format specified by the current "Constant Display Mode"
			void printConstant(const ref<ConstantExpr>& e);

			///Recursively print expression
			virtual void printExpression(const ref<Expr>& e);

			///Scan Expression recursively for Arrays in expressions. Found arrays are added to
			/// the usedArrays vector.
			void scan(const ref<Expr>& e);


			//Special Expression handlers
			virtual void printReadExpr(const ref<ReadExpr>& e);
			virtual void printExtractExpr(const ref<ExtractExpr>& e);
			virtual void printCastExpr(const ref<CastExpr>& e);
			virtual void printNotEqualExpr(const ref<NeExpr>& e);

			//All Expressions not handled by the "special expression handlers" are handled by this method
			virtual void printOtherExpr(const ref<Expr>& e);

			///Recursively prints updatesNodes
			virtual void printUpdatesAndArray(const UpdateNode* un, const Array* root);

			///This method does the translation between Expr classes and SMTLIBv2 keywords
			/// \return A C-string of the SMTLIBv2 keyword
			virtual const char* getSMTLIBKeyword(Expr::Kind k);

			virtual void printSeperator();

			///Helper printer class
			PrintContext p;



		private:
			SMTLIBv2Logic logicToUse;

			///Helper function for scan() that scans the expressions of an update node
			void scanUpdates(const UpdateNode* un);


			///Indicates if there were any constant arrays founds during a scan()
			bool haveConstantArray;

			bool humanReadable;

			//Map of enabled SMT	assert(queryAssert != NULL && "Failed to create assert expression!");LIB Options
			std::map<const char*,bool> smtlibBoolOptions;

			///This contains the query from the solver but negated for our purposes.
			/// \sa mangleQuery()
			ref<Expr> queryAssert;

			///This sets queryAssert to be the boolean negation of the original Query
			void mangleQuery();

			//Pointer to a vector of Arrays. These will be used for the (get-value () ) call.
			const std::vector<const Array*> * arraysToCallGetValueOn;

			ConstantDisplayMode cdm;

	};

}

#endif
