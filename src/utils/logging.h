#pragma once
// #define SILENT

#include <iostream>
#include <string>

#ifdef NDEBUG

inline void set_logging() {}
inline bool get_logging() { return false; }

#define LOG(x) do { } while (false)
#define LOG2(x) do { } while (false)

#define IF_LOG(x) do { } while (false)

#else

void set_logging(bool enabled);
bool get_logging();

#define LOG_CORE(x) do { if (get_logging()) {   \
  auto fn = std::string(__func__);              \
  size_t width = 20;                            \
  size_t padding = 0;                           \
  if (width >= fn.size())                       \
    padding = width - fn.size();                \
  else                                          \
    fn = fn.substr(0, width - 3) + "...";       \
  std::cout << x << std::endl;                  \
} } while (false)

#ifdef SILENT
#define LOG(x) do { } while (false)
#else
#define LOG(x) LOG_CORE(x)
#endif
#define LOG2(x) LOG_CORE(x)

#define IF_LOG(x) do { if (get_logging()) { x } } while (false)

#endif

