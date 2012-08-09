
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

	ExprSMTLIBPrinter::ExprSMTLIBPrinter(std::ostream& output, const Query& q) :
		o(output), query(q), usedArrays(), logicToUse(QF_AUFBV), p(output), haveConstantArray(false),
		humanReadable(true), smtlibBoolOptions()
	{
		setConstantDisplayMode(argConstantDisplayMode);
		mangleQuery();
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
		/* Handle simple boolean constants */

		if(e->isTrue())
		{
			p << "true";
			return;
		}

		if(e->isFalse())
		{
			p << "false";
			return;
		}

		/* Handle bitvector constants */

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
				p << "#b";

				zeroPad = e->getWidth() - value.length();

				for(unsigned int count=0; count < zeroPad; count++)
					p << "0";

				p << value ;
				break;

			case HEX:
				e->toString(value,16);
				p << "#x";

				zeroPad =  (e->getWidth() / 4) - value.length();
				for(unsigned int count=0; count < zeroPad; count++)
					p << "0";

				p << value ;
				break;

			case DECIMAL:
				e->toString(value,10);
				p << "(_ bv" << value<< " " << e->getWidth() << ")";
				break;

			default:
				klee_warning("ExprSMTLIBPrinter::printConstant() : Unexpected Constant display mode");
		}
	}

	void ExprSMTLIBPrinter::printExpression(const ref<Expr>& e)
	{
		switch(e->getKind())
		{
			case Expr::Constant:
				printConstant(cast<ConstantExpr>(e));
				return; //base case

			case Expr::NotOptimized:
				//skip to child
				printExpression(e->getKid(0));
				return;

			case Expr::Read:
				printReadExpr(cast<ReadExpr>(e));
				return;

			case Expr::Extract:
				printExtractExpr(cast<ExtractExpr>(e));
				return;

			case Expr::SExt:
			case Expr::ZExt:
				printCastExpr(cast<CastExpr>(e));
				return;

			case Expr::Ne:
				printNotEqualExpr(cast<NeExpr>(e));
				return;

			default:
				/* All other expression types can be handled in a generic way */
				printOtherExpr(e);
				return;
		}
	}

	void ExprSMTLIBPrinter::printReadExpr(const ref<ReadExpr>& e)
	{
		p.pushIndent();
		p << "(" << getSMTLIBKeyword(e->getKind()) << " ";
		p.pushIndent();

		printSeperator();

		//print array with updates recursively
		printUpdatesAndArray(e->updates.head,e->updates.root);

		//print index
		printSeperator();
		printExpression(e->index);

		p.popIndent();
		printSeperator();
		p << ")";
		p.popIndent();
	}

	void ExprSMTLIBPrinter::printExtractExpr(const ref<ExtractExpr>& e)
	{
		p.pushIndent();

		unsigned int lowIndex= e->offset;
		unsigned int highIndex= lowIndex + e->width -1;

		p << "((_ " << getSMTLIBKeyword(e->getKind()) << " " << highIndex << "  " << lowIndex << ") ";
		p.pushIndent();

		//recurse
		printExpression(e->getKid(0));

		p.popIndent();
		printSeperator();
		p << ")";
		p.popIndent();

	}

	void ExprSMTLIBPrinter::printCastExpr(const ref<CastExpr>& e)
	{
		/* sign_extend and zero_extend behave slightly unusually in SMTLIBv2
		 * instead of specifying of what bit-width we would like to extend to
		 * we specify how many bits to add to the child expression
		 *
		 * e.g
		 * ((_ sign_extend 64) (_ bv5 32))
		 *
		 * gives a (_ BitVec 96) instead of (_ BitVec 64)
		 *
		 * So we must work out how many bits we need to add.
		 *
		 * (e->width) is the desired number of bits
		 * (e->src->getWidth()) is the number of bits in the child
		 */
		unsigned int numExtraBits= (e->width) - (e->src->getWidth());

		p.pushIndent();
		p << "((_ " << getSMTLIBKeyword(e->getKind()) << " " <<
				numExtraBits << ") ";

		p.pushIndent();
		printSeperator();

		//recurse
		printExpression(e->src);

		p.popIndent();
		printSeperator();

		p << ")";
		p.popIndent();
	}

	void ExprSMTLIBPrinter::printNotEqualExpr(const ref<NeExpr>& e)
	{
		p.pushIndent();
		p << "(not (" << getSMTLIBKeyword(Expr::Eq) << " ";

		p.pushIndent();
		printExpression(e->getKid(0));
		printSeperator();
		printExpression(e->getKid(1));
		p.popIndent();

		p << ")";
		p.popIndent();
	}

	void ExprSMTLIBPrinter::printOtherExpr(const ref<Expr>& e)
	{
		p.pushIndent();
		p << "(" << getSMTLIBKeyword(e->getKind()) << " ";
		p.pushIndent();

		//loop over children and recurse into each
		for(unsigned int i=0; i < e->getNumKids(); i++)
		{
			printSeperator();
			printExpression(e->getKid(i));
		}

		p.popIndent();
		printSeperator();
		p << ")";
		p.popIndent();
	}

	const char* ExprSMTLIBPrinter::getSMTLIBKeyword(Expr::Kind k)
	{
		switch(k)
		{
			case Expr::Read: return "select";
			case Expr::Select: return "ite";
			case Expr::Concat: return "concat";
			case Expr::Extract: return "extract";
			case Expr::ZExt: return "zero_extend";
			case Expr::SExt: return "sign_extend";

			case Expr::Add: return "bvadd";
			case Expr::Sub: return "bvneg";
			case Expr::Mul: return "bvmul";
			case Expr::UDiv: return "budiv";
			case Expr::SDiv: return "bsdiv";
			case Expr::URem: return "burem";
			case Expr::SRem: return "bsrem";

			case Expr::Not: return "bvnot";
			case Expr::And: return "bvand";
			case Expr::Or:  return "bvor";
			case Expr::Xor: return "bvxor";
			case Expr::Shl: return "bvshl";
			case Expr::LShr: return "bvlshr";
			case Expr::AShr: return "bvashr";

			case Expr::Eq: return "=";

			//Not Equal does not exist directly in SMTLIBv2

			case Expr::Ult: return "bvult";
			case Expr::Ule: return "bvule";
			case Expr::Ugt: return "bvugt";
			case Expr::Uge: return "bvuge";

			case Expr::Slt: return "bvslt";
			case Expr::Sle: return "bvsle";
			case Expr::Sgt: return "bvsgt";
			case Expr::Sge: return "bvsge";

			default:
				return "<error>";

		}
	}

	void ExprSMTLIBPrinter::printUpdatesAndArray(const UpdateNode* un, const Array* root)
	{
		if(un!=NULL)
		{
			p << "(store ";
			p.pushIndent();

			//recurse to get the array or update that this store operations applies to
			printUpdatesAndArray(un->next,root);

			printSeperator();

			//print index
			printExpression(un->index);
			printSeperator();

			//print value that is assigned to this index of the array
			printExpression(un->value);

			p.popIndent();
			printSeperator();
		}
		else
		{
			//The base case of the recursion
			p << root->name;
		}

	}

	void ExprSMTLIBPrinter::generateOutput()
	{
		//perform scan of all expressions
		for(ConstraintManager::const_iterator i= query.constraints.begin(); i != query.constraints.end(); i++)
			scan(*i);

		//Scan the query too
		scan(query.expr);

		printNotice();
		printOptions();
		printSetLogic();
		printArrayDeclarations();
		printConstraints();
		printQuery();
		printAction();
		printExit();
	}

	void ExprSMTLIBPrinter::printSetLogic()
	{
		o << "(set-logic ";
		switch(logicToUse)
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
						p.pushIndent();
						printSeperator();

						p << "(select " << array->name << " (_ bv" << byteIndex << " " << array->getDomain() << ") )";
						printSeperator();
						printConstant((*ce));

						p.popIndent();
						printSeperator();
						p << ")";
						p.popIndent();
						printSeperator();
						p << ")";

						p.breakLineI();

					}
				}
			}
		}
	}

	void ExprSMTLIBPrinter::printConstraints()
	{
		o << "; Constraints" << endl;
		//Generate assert statements for each constraint
		for(ConstraintManager::const_iterator i= query.constraints.begin(); i != query.constraints.end(); i++)
		{
			p << "(assert ";
			p.pushIndent();
			printSeperator();

			//recurse into Expression
			printExpression(*i);

			p.popIndent();
			printSeperator();
			p << ")"; p.breakLineI();
		}

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

	bool ExprSMTLIBPrinter::setLogic(Logics l)
	{
		if(l > QF_AUFBV)
			return false;

		logicToUse=l;
		return true;
	}

	void ExprSMTLIBPrinter::printSeperator()
	{
		if(humanReadable)
			p.breakLineI();
		else
			p.write(" ");
	}

	void ExprSMTLIBPrinter::printNotice()
	{
		o << "; This file conforms to SMTLIBv2 and was generated by KLEE with " <<
				(humanReadable?"":"no ") << "indentation" << endl;
	}

	void ExprSMTLIBPrinter::setHumanReadable(bool hr)
	{
		humanReadable=hr;
	}

	void ExprSMTLIBPrinter::printOptions()
	{
		//Print out SMTLIBv2 boolean options
		for(std::map<const char*,bool>::const_iterator i= smtlibBoolOptions.begin(); i!= smtlibBoolOptions.end(); i++)
		{
			o << "(set-option :" << i->first << " " << ((i->second)?"true":"false") << ")" << endl;
		}
	}

	void ExprSMTLIBPrinter::printQuery()
	{
		p << "; Query from solver turned into an assert"; p.breakLineI();
		p.pushIndent();
		p << "(assert";
		p.pushIndent();
		printSeperator();

		printExpression(queryAssert);

		p.popIndent();
		printSeperator();
		p << ")";
		p.popIndent();
		p.breakLineI();
	}

	void ExprSMTLIBPrinter::mangleQuery()
	{
		//Negating the query
		queryAssert = Expr::createIsZero(query.expr);
	}

	bool ExprSMTLIBPrinter::setSMTLIBboolOption(SMTLIBboolOptions option, bool value)
	{
		switch(option)
		{
			case PRINT_SUCCESS:
				smtlibBoolOptions.insert(pair<const char*,bool>("print-success",value));
				return true;
			case PRODUCE_MODELS:
				smtlibBoolOptions.insert(pair<const char*,bool>("produce-models",value));
				return true;
			case INTERACTIVE_MODE:
				smtlibBoolOptions.insert(pair<const char*,bool>("interactive-mode",value));
				return true;
			default:
				return false;

		}
	}

}



