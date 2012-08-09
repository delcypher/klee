#ifndef KLEE_EXPRSMTLIBPRINTER_H
#define KLEE_EXPRSMTLIBPRINTER_H

#include <ostream>
#include <string>
#include <set>
#include <stack>
#include <klee/Constraints.h>
#include <klee/Expr.h>
#include <klee/util/PrintContext.h>

namespace klee {

	///Base Class for SMTLIBv2 printer for Expr trees
	class ExprSMTLIBPrinter
	{
		public:
			///Output stream to write to
			std::ostream& o;
			const ConstraintManager& cm;

			///Contains the arrays found during scans
			std::set<const Array*> usedArrays;

			enum Logics
			{
				QF_ABV,
				QF_AUFBV
			} logicToUse;

		protected:

			virtual void printNotice();

			virtual void printOptions() { };

			virtual void printSetLogic();

			virtual void printArrayDeclarations();

			virtual void printConstraints();

			///Print the S-expression(s) to ask for satisfiability, get-value etc...
			virtual void printAction();

			virtual void printExit();

			///Print a Constant in the format specified by the current "Constant Display Mode"
			void printConstant(const ref<ConstantExpr>& e);

			///Recursively print expression
			virtual void printExpression(const ref<Expr>& e);

			///Scan Expression recursively for
			/// * Arrays
			void scan(const ref<Expr>& e);

			virtual void printReadExpr(const ref<ReadExpr>& e);
			virtual void printExtractExpr(const ref<ExtractExpr>& e);
			virtual void printCastExpr(const ref<CastExpr>& e);
			virtual void printNotEqualExpr(const ref<NeExpr>& e);
			virtual void printOtherExpr(const ref<Expr>& e);

			///Recursively prints updatesNodes
			virtual void printUpdatesAndArray(const UpdateNode* un, const Array* root);

			virtual const char* getSMTLIBKeyword(Expr::Kind k);

			virtual void printSeperator();

			///Helper printer class
			PrintContext p;



		private:

			///Helper function for scan() that scans the expressions of an update node
			void scanUpdates(const UpdateNode* un);


			///Indicates if there were any constant arrays founds during a scan()
			bool haveConstantArray;

			bool humanReadable;


		public:

			enum ConstantDisplayMode
			{
				BINARY,
				HEX,
				DECIMAL
			};

			ConstantDisplayMode cdm;

			///Allows the way Constant bitvectors are printed.
			/// \return true if setting the mode was successful
			bool setConstantDisplayMode(ConstantDisplayMode cdm);

			ConstantDisplayMode getConstantDisplayMode() { return cdm;}

			ExprSMTLIBPrinter(std::ostream& output, const ConstraintManager& constraintM);

			void generateOutput();

			bool setLogic(Logics l);

			void setHumanReadable(bool hr);

	};

}

#endif
