#include "klee/ExprSMTLIBPrinter.h"


namespace klee
{
	void ExprSMTLIBPrinter::generateOutput()
	{
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

	}

	void ExprSMTLIBPrinter::printConstraints()
	{

	}

	void ExprSMTLIBPrinter::printAction()
	{
		o << "(check-sat)" << std::endl;
	}
}

