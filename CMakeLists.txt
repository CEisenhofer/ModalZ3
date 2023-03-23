cmake_minimum_required(VERSION 3.18.4)
project (Z3Modal)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

list(APPEND CMAKE_MODULE_PATH "${PROJECT_SOURCE_DIR}/cmake")

find_package(Z3 4.12.0 REQUIRED)

if ((NOT Z3_INCLUDE_DIR) OR (NOT Z3_LIBRARIES))
    message(FATAL_ERROR "Did not find Z3. Pass path diretly to CMake via -D")
    fail()
else()
    include_directories(${Z3_INCLUDE_DIR})
endif()
  
add_subdirectory(src)
