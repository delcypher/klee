#include "SMTLIBOutputLexer.h"
#include <ctype.h>

namespace klee
{

	SMTLIBOutputLexer::SMTLIBOutputLexer() :
			input(NULL),lastTokenContents(""),
			lastChar(' '), lastNumericTokenValue(""),
			lastNumericToken(UNKNOWN_TOKEN),
			tokenToReturn(NULL)
	{
	}

	bool SMTLIBOutputLexer::getNextToken(Token& t)
	{
		if(input==NULL)
			return false;

		if(! input->good())
			return false;


		//clear the last token string
		lastTokenContents="";

		tokenToReturn=&t;

		/* We set lastChar like this so that the call to walkPastWhiteSpace()
		 * will walk past the whitespace and have lastChar set to the next
		 * non-whitespace character.
		 */
		lastChar=' ';

		//skip whitespace and newlines
		if(!walkPastWhiteSpace())
			return true;

		//now lastChar contains a useful character

		//Check for #b or #x
		if(lastChar =='#')
		{

			lastTokenContents=lastChar;
			lastTokenContents+= input->get();

			if(lastTokenContents=="#b")
			{
				//we should have a binary numeral

				//check there are digits that follow
				lastChar=input->peek();
				if(lastChar != '0' || lastChar != '1')
				{
					*tokenToReturn = UNKNOWN_TOKEN;
					return false;
				}

				//clear the lastNumeric number
				lastNumericTokenValue="";

				//gather digits (lastChar peeks ahead)
				while(lastChar == '0' || lastChar == '1')
				{
					lastNumericTokenValue+=input->get(); //move input forward
					lastChar=input->peek();
				}

				//append the digits to what we've already found.
				lastTokenContents+=lastNumericTokenValue;

				//we should gathered all the bits now
				*tokenToReturn = lastNumericToken= NUMERAL_BASE2;
				return true;
			}
			else if(lastTokenContents=="#x")
			{
				//we should have a hex numeral

				//check there hex digits to follow
				lastChar=input->peek();
				if(!isxdigit(lastChar))
				{
					*tokenToReturn = UNKNOWN_TOKEN;
					return false;
				}

				//clear the lastNumeric number
				lastNumericTokenValue="";

				//gather hex digits (lastChar peeks ahead)
				while(isxdigit(lastChar))
				{
					lastNumericTokenValue+=input->get(); //move input forward
					lastChar=input->peek();
				}

				//append the digits to what we've already found.
				lastTokenContents+=lastNumericTokenValue;

				//we should have gathered all the hex digits now
				*tokenToReturn = lastNumericToken = NUMERAL_BASE16;
				return true;
			}
			else
			{
				*tokenToReturn = UNKNOWN_TOKEN;
				return false;
			}
		}

		if(lastChar ==')')
		{
			*tokenToReturn = RBRACKET;
			lastTokenContents=lastChar;
			return true;
		}

		//could be "(" or "(_ bvN  N)"
		if(lastChar == '(')
		{
			if(input->peek() != '_')
			{
				//It's just a left bracket
				*tokenToReturn = LBRACKET;
				lastTokenContents=lastChar;
				return true;
			}

			lastTokenContents="";
			lastTokenContents+=lastChar;
			lastChar=input->get();
			lastTokenContents+=lastChar;

			//now have "(_" so far

			//walkpast any whitespace
			if(!walkPastWhiteSpace())
			{
				//we didn't expect to hit EOF here
				return false;
			}

			lastTokenContents+=" "; //add a space because none have been added so far.

			//at this point lastChar is a non-whitespace and the stream points to the character afterwards

			//expecting "bv"
			lastTokenContents+=lastChar;
			lastChar=input->get();
			lastTokenContents+=lastChar;

			if(lastTokenContents != "(_ bv")
			{
				*tokenToReturn = UNKNOWN_TOKEN;
				return false;
			}

			//have "(_ bv" so far.

			//the next character should be the start of the digits ( the actual numeric value in base10)
			if(!isdigit(lastChar))
			{
				*tokenToReturn = UNKNOWN_TOKEN;
				return false;
			}

			//clear the lastNumericToken value
			lastNumericTokenValue="";
			lastNumericTokenValue+=lastChar; //grab the first digit

			//gather other digits (there might not be any) (lastChar peeks ahead)
			lastChar=input->peek();
			while(isdigit(lastChar))
			{
				lastNumericTokenValue+=input->get(); //move input forward
				lastChar=input->peek();
			}

			lastTokenContents+=lastNumericTokenValue;

			//walkpast any whitespace
			if(!walkPastWhiteSpace())
			{
				//we didn't expect to hit EOF here
				return false;
			}
			lastTokenContents+=" ";//append a single space

			//have "(_ bvN " so far where N is a decimal number.

			//now comes the digit stating the bit width we don't care what this number actually is
			//lastChar should be pointing at a numeral
			if(!isdigit(lastChar))
			{
				*tokenToReturn = UNKNOWN_TOKEN;
				return false;
			}

			lastTokenContents+=lastChar;//grab the digit

			//grab the other digits (if they exist)
			lastChar=input->peek();
			while(isdigit(lastChar))
			{
				lastTokenContents+=input->get(); //move input forward
				lastChar=input->peek();
			}

			//walkpast any whitespace
			if(!walkPastWhiteSpace())
			{
				//we didn't expect to hit EOF here
				return false;
			}

			//now the last character should be ')'
			if(lastChar != ')')
			{
				*tokenToReturn = UNKNOWN_TOKEN;
				return false;
			}
			lastTokenContents+=lastChar;

			//Finally processed the bitvector
			*tokenToReturn = NUMERAL_BASE10;
			return true;
		}

		/* Could be SAT, UNSAT, UNKNOWN, SELECT or ARRAY_IDENTIFIER
		 *
		 */
		if(isalpha(lastChar))
		{
			lastTokenContents+=lastChar;

			//grab additional characters (there may be none)
			lastChar=input->peek();
			while(isIdentifier(lastChar))
			{
				lastChar=input->get();
				lastTokenContents+=lastChar;

				/* Check for keywords. We look ahead one character to check that we're not accidently
				 * identifying an ARRAY_IDENTIFIER that uses another keyword as a prefix.
				 * e.g. an array called sat_1 could be identified as SAT if we didn't look ahead.
				 */
				if(lastTokenContents == "sat" && !isIdentifier(input->peek()))
				{
					*tokenToReturn = SAT;
					return true;
				}

				if(lastTokenContents == "unsat" && !isIdentifier(input->peek()))
				{
					*tokenToReturn = UNSAT;
					return true;
				}

				if(lastTokenContents == "unknown" && !isIdentifier(input->peek()))
				{
					*tokenToReturn = UNKNOWN;
					return true;
				}

				if(lastTokenContents == "select" && !isIdentifier(input->peek()))
				{
					*tokenToReturn = SELECT;
					return true;
				}


			}

			//We must have an array identifier.
			*tokenToReturn = ARRAY_IDENTIFIER;
			return true;


		}

		*tokenToReturn = UNKNOWN_TOKEN;
		return false;
	}


	void SMTLIBOutputLexer::setInput(std::istream& i)
	{
		input = &i;
		lastTokenContents="";


	}

	std::istream& SMTLIBOutputLexer::getInput()
	{
		return *input;
	}


	const std::string& SMTLIBOutputLexer::getLastTokenContents()
	{
		return lastTokenContents;
	}

	bool SMTLIBOutputLexer::walkPastWhiteSpace()
	{
		//skip whitespace and newlines
		while(isspace(lastChar))
		{
			lastChar = input->get();

			if(input->eof())
			{
				//hit end of file
				*tokenToReturn = END_OF_FILE;
				return false;//User's expect this return value if hit end of file.
			}
		}


		return true;//didn't hit end of file
	}

bool SMTLIBOutputLexer::getLastNumericValue(unsigned int& value)
{
	//TODO
	return false;
}

	bool SMTLIBOutputLexer::isIdentifier(char c)
	{
		return (isalnum(c) || c == '_');
	}

}




