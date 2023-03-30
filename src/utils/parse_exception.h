#include <exception>
#include <string>

class parse_exception : public std::exception {

public:

    parse_exception(std::string msg) : std::exception(msg.c_str()) {}

};
