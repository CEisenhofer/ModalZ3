cmake_minimum_required(VERSION 3.18.4)

add_library(ast
    standard_translation.cpp
    modal_to_euf.cpp
    lazy_up.cpp
    strategy.cpp
    syntax_tree.cpp
iterative_deepening.cpp iterative_deepening.h)

target_link_libraries(ast utils)
include_directories("../utils")
