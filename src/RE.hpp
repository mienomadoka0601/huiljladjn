#ifndef RUNTIMEERROR
#define RUNTIMEERROR

#include <exception>
#include <string>

class RuntimeError : public std::exception {
private:
    std::string s;
public:
    RuntimeError(std::string msg) : s(msg) {}
    const char* what() const noexcept override {
        return s.c_str();
    }
};

#endif