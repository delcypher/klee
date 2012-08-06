
//for klee_warning
#include "../Core/Common.h"

#include "llvm/Support/Casting.h"
#include "klee/ExprSMTLIBPrinter.h"

using namespace std;

namespace klee
{
	void ExprSMTLIBPrinter::generateOutput()
	{
		//perform scan of all expressions
		for(ConstraintManager::const_iterator i= cm.begin(); i != cm.end(); i++)
			scan(*i);

		printNotice();
		printOptions();
		printSetLogic(ExprSMTLIBPrinter::QF_AUFBV);
		printArrayDeclarations();
		printConstraints();
		printAction();
	}

	void ExprSMTLIBPrinter::printSetLogic(ExprSMTLIBPrinter::Logics logic)
	{
		o << "(set-logic ";
		switch(logic)
		{
		case QF_ABV: o << "QF_ABV"; break;
		case QF_AUFBV: o << "QF_AUFBV" ; break;
		}
		o << " )" << std::endl;
	}


	void ExprSMTLIBPrinter::printArrayDeclarations()
	{
		//Assume scan() has been called
		o << "; Array declarations" << endl;

		//declare arrays
		for(set<const Array*>::iterator it = usedArrays.begin(); it != usedArrays.end(); it++)
		{
			o << "(declare-fun " << (*it)->name << " () "
				 "(Array (_ BitVec " << (*it)->getDomain() << ") "
				 "(_ BitVec " << (*it)->getRange() << ") ) )" << endl;
		}

		//Set array values for constant values
		if(haveConstantArray)
		{
			o << "; Constant Array Definitions" << endl;

			//TODO
		}
	}

	void ExprSMTLIBPrinter::printConstraints()
	{

	}

	void ExprSMTLIBPrinter::printAction()
	{
		o << "(check-sat)" << std::endl;
	}

	void ExprSMTLIBPrinter::scan(const ref<Expr>& e)
	{
		if(e.isNull())
			klee_error("ExprSMTLIBPrinter::scan() : Found NULL expression!");

		if(isa<ConstantExpr>(e))
			return; //we don't need to scan simple constants

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

	void ExprSMTLIBPrinter::scanUpdates(const UpdateNode* un)
	{
		while(un != NULL)
		{
			scan(un->index);
			scan(un->value);
			un= un->next;
		}
	}

}

