#include <iostream>

#include "iterative_deepening.h"
#include "lazy_up.h"
#include "random_formula.h"
#include "standard_translation.h"

constexpr unsigned RANDOM_FORMULAS = 1000;
constexpr unsigned MAX_RELATIONS = 3;

void test() {
    context ctx;

    z3::sort world_sort = ctx.uninterpreted_sort("World");
    z3::sort relation_sort = ctx.uninterpreted_sort("Relation");
    z3::expr placeholder = ctx.constant("world", world_sort);
    z3::sort_vector domain(ctx);
    domain.push_back(relation_sort);
    domain.push_back(ctx.bool_sort());
    z3::func_decl dia = ctx.function("dia", domain, ctx.bool_sort());
    z3::func_decl box = ctx.function("box", domain, ctx.bool_sort());
    
    domain.pop_back();
    domain.push_back(world_sort);
    domain.push_back(world_sort);
    z3::func_decl reachable = ctx.function("reachable", domain, ctx.bool_sort());

    for (unsigned r = 1; r <= MAX_RELATIONS; r++) {
        random_formula rf(ctx, r, world_sort, relation_sort, dia, box, placeholder);
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
            
            standard_translation std_translation(ctx, world_sort, relation_sort, dia, box, reachable, placeholder);
            check_result result_std_translation = std_translation.check(e);
            
            iterative_deepening iterative_deepening(ctx, world_sort, relation_sort, dia, box, reachable, placeholder);
            check_result result_iterative_deepening = iterative_deepening.check(e);
            
            lazy_up lazy_up(ctx, world_sort, relation_sort, dia, box, reachable, placeholder);
            check_result result_lazy_up = lazy_up.check(e);
    
            if (result_std_translation == z3::unknown) {
                std::cerr << "Seed: " << rf.get_last_seed() << ":\n";
                std::cerr << "std-translation unknown: " << e << std::endl;
                exit(-1);
            }
            
            if (result_iterative_deepening == z3::unknown) {
                std::cerr << "Seed: " << rf.get_last_seed() << ":\n";
                std::cerr << "iterative-deepening unknown: " << e << std::endl;
                exit(-1);
            }
            
            if (result_lazy_up == z3::unknown) {
                std::cerr << "Seed: " << rf.get_last_seed() << ":\n";
                std::cerr << "lazy-up unknown: " << e << std::endl;
                exit(-1);
            }
            
            if (result_std_translation != result_lazy_up) {
                std::cerr << "Seed: " << rf.get_last_seed() << ":\n";
                std::cerr << "Different results: std (" << result_std_translation << ") vs lazy-up (" << result_lazy_up << "): " << e << std::endl;
                exit(-1);
            }
            if (result_std_translation != result_iterative_deepening) {
                std::cerr << "Seed: " << rf.get_last_seed() << ":\n";
                std::cerr << "Different results: std (" << result_std_translation << ") vs lazy-up (" << result_iterative_deepening << "): " << e << std::endl;
                exit(-1);
            }
        }
    }
}

int main() {
    test();
    return 0;
}
