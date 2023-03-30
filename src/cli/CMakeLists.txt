cmake_minimum_required(VERSION 3.18.4)

add_executable(cli
  main.cpp
)

target_link_libraries(cli PRIVATE ast)
#target_link_libraries(cli PRIVATE utils)

include_directories("../strategies")
include_directories("../utils")
target_link_libraries(cli PRIVATE ${Z3_LIBRARIES})
