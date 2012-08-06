#ifndef PRINTCONTEXT_H_
#define PRINTCONTEXT_H_

#include <ostream>
#include <sstream>
#include <string>
#include <iomanip>

/// PrintContext - Helper class for storing extra information for
/// the pretty printer.
class PrintContext {
private:
  std::ostream &os;
  std::stringstream ss;
  std::string newline;

public:
  /// Number of characters on the current line.
  unsigned pos;

public:
  PrintContext(std::ostream &_os) : os(_os), newline("\n"), pos(0) {}

  void setNewline(const std::string &_newline) {
    newline = _newline;
  }

  void breakLine(unsigned indent=0) {
    os << newline;
    if (indent)
      os << std::setw(indent) << ' ';
    pos = indent;
  }

  /// write - Output a string to the stream and update the
  /// position. The stream should not have any newlines.
  void write(const std::string &s) {
    os << s;
    pos += s.length();
  }

  template <typename T>
  PrintContext &operator<<(T elt) {
    ss.str("");
    ss << elt;
    write(ss.str());
    return *this;
  }
};


#endif /* PRINTCONTEXT_H_ */
