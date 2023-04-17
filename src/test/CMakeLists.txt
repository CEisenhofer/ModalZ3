cmake_minimum_required(VERSION 3.18.4)

add_executable(test
  test.cpp
  random_formula.cpp
)

target_link_libraries(test PRIVATE strategies)
#target_link_libraries(test PRIVATE utils)

include_directories("../strategies")
include_directories("../utils")
target_link_libraries(test PRIVATE ${Z3_LIBRARIES})
