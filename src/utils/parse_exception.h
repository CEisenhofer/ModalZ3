#include <stdexcept>
#include <string>

class parse_exception : public std::runtime_error {
public:
    parse_exception(const std::string &msg) : std::runtime_error(msg) {}
};
