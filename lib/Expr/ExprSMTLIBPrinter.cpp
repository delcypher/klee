
//for klee_warning
#include "../Core/Common.h"

#include "llvm/Support/Casting.h"
#include "llvm/Support/CommandLine.h"
#include "klee/util/ExprSMTLIBPrinter.h"

using namespace std;

namespace
{
	//Command line options
	llvm::cl::opt<klee::ExprSMTLIBPrinter::ConstantDisplayMode> argConstantDisplayMode
	("smtlib-display-constants", llvm::cl::desc("Sets how bitvector constants are written in generated SMTLIBv2 files (default=dec)"),
	llvm::cl::values( clEnumValN(klee::ExprSMTLIBPrinter::BINARY, "bin","Use binary form (e.g. #b00101101)"),
					  clEnumValN(klee::ExprSMTLIBPrinter::HEX, "hex","Use Hexadecimal form (e.g. #x2D)"),
					  clEnumValN(klee::ExprSMTLIBPrinter::DECIMAL, "dec","Use decimal form (e.g. (_ BitVec45 8) )"),
					  clEnumValEnd
					),
					llvm::cl::init(klee::ExprSMTLIBPrinter::DECIMAL)


	);

}


namespace klee
{

ExprSMTLIBPrinter::ExprSMTLIBPrinter(std::ostream& output, const ConstraintManager& constraintM) :
	o(output), cm(constraintM), usedArrays(), p(output), haveConstantArray(false)
{
	setConstantDisplayMode(argConstantDisplayMode);
}

bool ExprSMTLIBPrinter::setConstantDisplayMode(ConstantDisplayMode cdm)
{
	if(cdm > DECIMAL)
		return false;

	this->cdm = cdm;
	return true;
}

void ExprSMTLIBPrinter::printConstant(const ref<ConstantExpr>& e)
{
	std::string value;

	/* SMTLIBv2 deduces the bit-width (should be 8-bits in our case)
	 * from the length of the string (e.g. zero is #b00000000). LLVM
	 * doesn't know about this so we need to pad the printed output
	 * with the appropriate number of zeros (zeroPad)
	 */
	unsigned int zeroPad=0;

	switch(cdm)
	{
	case BINARY:
		e->toString(value,2);
		o << "#b";

		zeroPad = e->getWidth() - value.length();

		for(unsigned int count=0; count < zeroPad; count++)
			o << "0";

		o << value ;
	break;

	case HEX:
		e->toString(value,16);
		o << "#x";

		zeroPad =  (e->getWidth() / 4) - value.length();
		for(unsigned int count=0; count < zeroPad; count++)
			o << "0";

		o << value ;
	break;

	case DECIMAL:
		e->toString(value,10);
		o << "(_ bv" << value<< " " << e->getWidth() << ")";

	break;

	default:
		klee_warning("ExprSMTLIBPrinter::printConstant() : Unexpected Constant display mode");
	}
}

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
		printExit();
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

			const Array* array;

			//loop over found arrays
			for(set<const Array*>::iterator it = usedArrays.begin(); it != usedArrays.end(); it++)
			{
				array= *it;
				int byteIndex=0;
				if(array->isConstantArray())
				{
					/*loop over elements in the array and generate an assert statement
					  for each one
					 */
					for(vector< ref<ConstantExpr> >::const_iterator ce= array->constantValues.begin();
							ce != array->constantValues.end(); ce++, byteIndex++)
					{
						p << "(assert (";
						p.pushIndent();
						p <<           "= ";
						p.pushIndent().breakLineI();

						p << "(select " << array->name << " (_ bv" << byteIndex << " " << array->getDomain() << ") )";
						p.breakLineI();
						printConstant((*ce));

						p.popIndent().breakLineI();
						p << ")";
						p.popIndent().breakLineI();
						p << ")";

						p.breakLineI();

					}
				}
			}
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


	void ExprSMTLIBPrinter::printExit()
	{
		o << "(exit)" << endl;
	}


}



