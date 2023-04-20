cmake_minimum_required(VERSION 3.18.4)

add_library(strategies
    standard_translation.cpp
    lazy_up.cpp
    strategy.cpp
    syntax_tree.cpp
    modal_tree.cpp
    iterative_deepening_quant.cpp
    iterative_deepening_quant.h
    iterative_deepening_unrolled.cpp
    iterative_deepening_unrolled.h
)

target_link_libraries(strategies utils)
include_directories("../utils")
