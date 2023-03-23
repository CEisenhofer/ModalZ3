#pragma once
// From Z3's source

#include <iostream>

// Clemens this is cursed, why?
#ifdef NDEBUG
#define INVOKE_DEBUGGER() exit(-1)
#else
#ifdef _WINDOWS
#define INVOKE_DEBUGGER() __debugbreak()
#else
#include <csignal>
#define INVOKE_DEBUGGER() raise(SIGTRAP)
#endif
#endif

inline void notify_assertion_violation(const char* fileName, int line, const char* condition) {
    std::cerr << "ASSERTION VIOLATION\n"
                 "File: " << fileName << "\n"
                 "Line: " << line << '\n'
              << condition << '\n';
    INVOKE_DEBUGGER();
}

#define VERIFY(x) do {                                                                  \
    if (!(x)) {                                                                       \
        notify_assertion_violation(__FILE__, __LINE__, "Failed to verify: " #x "\n");   \
    }                                                                                   \
} while (false)

#ifdef NDEBUG
#define DEBUG_CODE(x) do { } while (false)
#else
#define DEBUG_CODE(x) do { x } while (false)
#endif

#define SASSERT(x) DEBUG_CODE(VERIFY(x);)
