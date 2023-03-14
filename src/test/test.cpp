#pragma once

#include <iostream>

#include "modal_to_qeuf.h"
#include "random_formula.h"

constexpr unsigned RANDOM_FORMULAS = 1000;

void test_preprocess() {
    context ctx;
    random_formula rf(ctx, 1678632895);
    rf.set_max_depth(6);
    
#if 0
    for (unsigned i = 0; i < RANDOM_FORMULAS; i++) {
        if (i % 100 == 0) 
                std::cout << "Iteration " << i << std::endl; 
        expr e = rf.get();
        
        preprocess_only preprocess(ctx);
        expr preprocessed = preprocess.rewrite_formula(e);
        
        modal_to_qeuf std_translation1(ctx, false);
        check_result result = std_translation1.check(!implies(e, preprocessed));
        if (result != z3::unsat) {
            std::cerr << "Seed: " << rf.get_last_seed() << ":\n";
            std::cerr << "Preprocessed " << preprocessed << " is weaker than " << e << std::endl;
            exit(-1);
        }
        
        modal_to_qeuf std_translation2(ctx, false);
        result = std_translation2.check(!implies(preprocessed, e));
        if (result != z3::unsat) {
            std::cerr << "Seed: " << rf.get_last_seed() << ":\n";
            std::cerr << "Original " << preprocessed << " is weaker than " << e << std::endl;
            exit(1);
        }
    }
    
    std::cout << "Preprocessing succeeded!\n\n";
#endif
    
    for (unsigned i = 0; i < RANDOM_FORMULAS; i++) {
        if (i % 100 == 0) 
            std::cout << "Iteration " << i << std::endl; 
        expr e = rf.get();
        
        modal_to_qeuf std_translation(ctx);
        check_result result_std_translation = std_translation.check(e);
        
        modal_to_qeuf euf_translation(ctx);
        check_result result_euf_translation = euf_translation.check(e);
        
        if (result_std_translation == z3::unknown) {
            std::cerr << "Seed: " << rf.get_last_seed() << ":\n";
            std::cerr << "std-translation unknown " << e << std::endl;
            exit(-1);
        }
        
        if (result_euf_translation == z3::unknown) {
            std::cerr << "Seed: " << rf.get_last_seed() << ":\n";
            std::cerr << "euf-translation unknown " << e << std::endl;
            exit(-1);
        }
        
        if (result_std_translation != result_euf_translation) {
            std::cerr << "Seed: " << rf.get_last_seed() << ":\n";
            std::cerr << "Different results: std vs euf " << e << std::endl;
            exit(-1);
        }
    }
}

int main() {

    test_preprocess();
    
    return 0;
}