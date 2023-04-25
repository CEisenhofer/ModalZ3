cmake_minimum_required(VERSION 3.18.4)

add_executable(test
  test.cpp
  random_formula.cpp
)

target_link_libraries(test PRIVATE strategies)
#target_link_libraries(test PRIVATE utils)

if ((CMAKE_CXX_COMPILER_ID STREQUAL "Clang") OR (CMAKE_CXX_COMPILER_ID STREQUAL "GNU"))
    SET(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -pthread")
endif()

include_directories("../strategies")
include_directories("../utils")
target_link_libraries(test PRIVATE ${Z3_LIBRARIES})
