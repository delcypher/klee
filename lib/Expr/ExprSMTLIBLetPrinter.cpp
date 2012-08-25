#include "klee/util/ExprSMTLIBLetPrinter.h"

using namespace std;
namespace klee
{
	const char ExprSMTLIBLetPrinter::BINDING_PREFIX[] = "?B";


	ExprSMTLIBLetPrinter::ExprSMTLIBLetPrinter(std::ostream& o, const Query& q) :
	ExprSMTLIBPrinter(o,q), bindings(), firstEO(), twoOrMoreEO(),
	disablePrintedAbbreviations(false)
	{
	}

	void ExprSMTLIBLetPrinter::generateOutput()
	{
		//Scan all the expressions to fill usedArrays
		scanAll();

		generateBindings();

		if(isHumanReadable()) printNotice();
		printOptions();
		printSetLogic();
		printArrayDeclarations();
		printLetExpression();
		printAction();
		printExit();
	}

	void ExprSMTLIBLetPrinter::scan(const ref<Expr>& e)
	{
		if(isa<ConstantExpr>(e))
			return; //we don't need to scan simple constants

		if(firstEO.insert(e).second)
		{
			//We've not seen this expression before

			if(const ReadExpr* re = dyn_cast<ReadExpr>(e))
			{

				//Attempt to insert array and if array wasn't present before do more things
				if(usedArrays.insert(re->updates.root).second)
				{

					//check if the array is constant
					if( re->updates.root->isConstantArray())
						haveConstantArray=true;

					//scan the update list
					scanUpdates(re->updates.head);

				}

			}

			//recurse into the children
			Expr* ep = e.get();
			for(unsigned int i=0; i < ep->getNumKids(); i++)
				scan(ep->getKid(i));
		}
		else
		{
			/* We must of seen the expression before. Add it to
			 * the set of twoOrMoreOccurances. We don't need to
			 * check if the insertion fails.
			 */
			twoOrMoreEO.insert(e);
		}
	}

	void ExprSMTLIBLetPrinter::generateBindings()
	{
		//Assign a number to each binding that will be used
		unsigned int counter=0;
		for(set<ref<Expr> >::const_iterator i=twoOrMoreEO.begin();
				i!= twoOrMoreEO.end(); ++i)
		{
			bindings.insert(std::make_pair(*i,counter));
			++counter;
		}
	}

	void ExprSMTLIBLetPrinter::printExpression(const ref<Expr>& e)
	{
		map<const ref<Expr>,unsigned int>::const_iterator i= bindings.find(e);

		if(disablePrintedAbbreviations || i == bindings.end())
		{
			/*There is no abbreviation for this expression so print it normally.
			 * Do this by using the parent method.
			 */
			ExprSMTLIBPrinter::printExpression(e);
		}
		else
		{
			//Use binding name e.g. "?B1"
			p << BINDING_PREFIX << i->second;
		}
	}

	void ExprSMTLIBLetPrinter::printLetExpression()
	{
		p << "(assert"; p.pushIndent(); printSeperator();

		if(bindings.size() !=0 )
		{
			//Only print let expression if we have bindings to use.
			p << "(let"; p.pushIndent(); printSeperator();
			p << "( "; p.pushIndent();

			//Print each binding
			for(map<const ref<Expr>, unsigned int>::const_iterator i= bindings.begin();
					i!=bindings.end(); ++i)
			{
				printSeperator();
				p << "(" << BINDING_PREFIX << i->second << " ";
				p.pushIndent();

				//Disable abbreviations so none are used here.
				disablePrintedAbbreviations=true;
				printExpression(i->first);

				p.popIndent();
				printSeperator();
				p << ")";
			}


			p.popIndent(); printSeperator();
			p << ")";
			printSeperator();

			//Re-enable printing abbreviations.
			disablePrintedAbbreviations=false;

		}

		//print out Expressions with abbreviations.
		unsigned int numberOfItems= query.constraints.size() +1; //+1 for query
		unsigned int itemsLeft=numberOfItems;
		vector<ref<Expr> >::const_iterator constraint=query.constraints.begin();

		/* Produce nested (and () () statements. If the constraint set
		 * is empty then we will only print the "queryAssert".
		 */
		for(; itemsLeft !=0; --itemsLeft)
		{
			if(itemsLeft >=2)
			{
				p << "(and"; p.pushIndent(); printSeperator();
				printExpression(*constraint);
				printSeperator();
				++constraint;
				continue;
			}
			else
			{
				// must have 1 item left (i.e. the "queryAssert")
				if(isHumanReadable()) { p << "; query"; p.breakLineI();}
				printExpression(queryAssert);

			}
		}

		/* Produce closing brackets for nested "and statements".
		 * Number of "nested ands" = numberOfItems -1
		 */
		itemsLeft= numberOfItems -1;
		for(; itemsLeft!=0; --itemsLeft)
		{
			p.popIndent(); printSeperator();
			p << ")";
		}



		if(bindings.size() !=0)
		{
			//end let expression
			p.popIndent(); printSeperator();
			p << ")";  printSeperator();
		}

		//end assert
		p.popIndent(); printSeperator();
		p << ")";
		p.breakLineI();
	}


}
