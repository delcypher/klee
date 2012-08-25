#include "ExprSMTLIBPrinter.h"
#ifndef EXPRSMTLETPRINTER_H_
#define EXPRSMTLETPRINTER_H_

namespace klee
{
	class ExprSMTLIBLetPrinter : public ExprSMTLIBPrinter
	{
		public:
			ExprSMTLIBLetPrinter(std::ostream& o, const Query& q);
			virtual void generateOutput();
		protected:
			virtual void scan(const ref<Expr>& e);
			virtual void generateBindings();
			void printExpression(const ref<Expr>& e);
			void printLetExpression();

		private:
			//Let expression binding number
			std::map<const ref<Expr>,unsigned int> bindings;

			/* These are effectively expression counters.
			 * firstEO - first Occurrence of expression contains
			 *           all expressions that occur once. It is
			 *           only used to help us fill twoOrMoreOE
			 *
			 * twoOrMoreEO - Contains occur all expressions that
			 *               that occur two or more times. These
			 *               are the expressions that will be
			 *               abbreviated by using (let () ()) expressions.
			 *
			 *
			 *
			 */
			std::set<ref<Expr> > firstEO, twoOrMoreEO;

			static const char BINDING_PREFIX[];

			/* This is needed during un-abbreviated printing.
			 * Because we have overloaded printExpression()
			 * the parent will call it and will abbreviate
			 * when we don't want it to. This bool allows us
			 * to switch it on/off easily.
			 */
			bool disablePrintedAbbreviations;



	};
}



#endif /* EXPRSMTLETPRINTER_H_ */
