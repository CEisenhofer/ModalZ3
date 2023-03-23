cmake_minimum_required(VERSION 3.19.2)

add_library(ast
    modal_to_qeuf.cpp
    modal_to_euf.cpp
    lazy_up.cpp
    strategy.cpp
)

target_link_libraries(ast utils)
include_directories("../utils")
