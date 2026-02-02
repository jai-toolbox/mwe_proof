#import "Basic";
#import "tbx/proof";

test_and :: () {
    print("=== AND Proof ===\n");

    natural_numbers := make_constant(SYM_NAT);
    
    x := make_variable("x");
    y := make_variable("y");
    two := make_constant("2");
    three := make_constant("3");
    
    x_eq_2 := make_eq(x, two);
    y_eq_3 := make_eq(y, three);
    
    target := make_and(x_eq_2, y_eq_3);
    
    assumptions: [..]*Formula;
    array_add(*assumptions, x_eq_2);
    array_add(*assumptions, y_eq_3);
    
    proof := create_proof(assumptions, target);
    
    add_line_to_proof(*proof, x_eq_2, "ASSUMPTION");
    add_line_to_proof(*proof, y_eq_3, "ASSUMPTION");
    add_line_to_proof(*proof, target, "AND", 0, 1);
    
    print_proof(*proof);
    
    if is_valid(*proof) {
        print("Proof is valid for target: %\n", formula_to_string(target));
    } else {
        print("Proof is NOT valid.\n");
    }
    print("\n");
}

test_forall :: () {
    print("=== FORALL Proof ===\n");
    natural_numbers := make_constant(SYM_NAT);
    
    y := make_variable("y");
    x := make_variable("x");
    five := make_constant("5");
    X := make_constant("X");
    
    y_in_X := make_rel(SYM_IN, y, X);
    
    x_eq_5 := make_eq(x, five);
    forall_x_eq_5 := make_forall("x", X, x_eq_5);
    
    y_eq_5 := make_eq(y, five);
    
    assumptions: [..]*Formula;
    array_add(*assumptions, y_in_X);
    array_add(*assumptions, forall_x_eq_5);
    
    proof := create_proof(assumptions, y_eq_5);
    
    add_line_to_proof(*proof, y_in_X, "ASSUMPTION");
    add_line_to_proof(*proof, forall_x_eq_5, "ASSUMPTION");
    add_line_to_proof(*proof, y_eq_5, "FORALL", 1, 0);
    
    print_proof(*proof);
    
    if is_valid(*proof) {
        print("Proof is valid for target: %\n", formula_to_string(y_eq_5));
    } else {
        print("Proof is NOT valid.\n");
    }
    print("\n");
}

test_excluded_middle :: () {
    print("=== Excluded Middle Proof ===\n");
    
    x := make_variable("x");
    Px := make_rel("P", x);
    not_Px := make_not(Px);
    target := make_or(Px, not_Px);
    
    assumptions: [..]*Formula;
    proof := create_proof(assumptions, target);
    register_rule(*proof, "LEM", excluded_middle_rule);
    
    add_line_to_proof(*proof, target, "LEM");
    
    print_proof(*proof);
    
    if is_valid(*proof) {
        print("Proof is valid for target: %\n", formula_to_string(target));
    } else {
        print("Proof is NOT valid.\n");
    }
    print("\n");
}



test_cases_proof :: () {
    print("=== CASES Proof ===\n");
    
    // Terms
    x := make_variable("x");
    
    // Formulas
    Px := make_rel("P", x);
    not_Px := make_not(Px);
    Qx := make_rel("Q", x);
    
    // Implications
    imp1 := make_implies(Px, Qx);
    imp2 := make_implies(not_Px, Qx);
    
    // Target
    target := Qx;
    
    assumptions: [..]*Formula;
    array_add(*assumptions, imp1);
    array_add(*assumptions, imp2);
    
    proof := create_proof(assumptions, target);
    register_rule(*proof, "CASES", cases_rule);
    
    // 0. Assume f -> t
    add_line_to_proof(*proof, imp1, "ASSUMPTION");
    
    // 1. Assume ¬f -> t
    add_line_to_proof(*proof, imp2, "ASSUMPTION");
    
    // 2. Apply cases
    add_line_to_proof(*proof, target, "CASES", 0, 1);
    
    print_proof(*proof);
    
    if is_valid(*proof) {
        print("Proof is valid for target: %\n", formula_to_string(target));
    }
}

test_induction_modification_rules :: () {
    print("=== Induction Proof (modification rules): sum(n) = n ===\n");
    
    natural_numbers := make_constant(SYM_NAT);
    
    // Terms
    n := make_variable("n");
    k := make_variable("k");
    zero := make_constant("0");
    one := make_constant("1");
    
    // Helper function for sum
    sum_fn :: (t: *Term) -> *Term {
        return make_function("sum", t);
    }
    
    // base axiom: sum(0) = 0
    sum_axiom_base := make_eq(sum_fn(zero), zero);
    
    // recursive axiom: forall k, sum(k+1) = sum(k) + 1
    k_plus_1 := make_function("+", k, one);
    sum_k_plus_1 := sum_fn(k_plus_1);
    sum_k_plus_1_def := make_function("+", sum_fn(k), one);
    recursive_axiom_inner := make_eq(sum_k_plus_1, sum_k_plus_1_def);
    sum_axiom_recursive := make_forall("k", natural_numbers, recursive_axiom_inner);
    
    // step: forall k, sum(k) = k -> sum(k+1) = k+1
    sum_k_eq_k := make_eq(sum_fn(k), k);
    sum_k1_eq_k1 := make_eq(sum_fn(k_plus_1), k_plus_1);
    step_inner := make_implies(sum_k_eq_k, sum_k1_eq_k1);
    step := make_forall("k", natural_numbers, step_inner);
    
    // target: forall n, sum(n) = n
    target := make_forall("n", natural_numbers, make_eq(sum_fn(n), n));
    
    assumptions: [..]*Formula;
    array_add(*assumptions, sum_axiom_base);
    array_add(*assumptions, sum_axiom_recursive);
    
    proof := create_proof(assumptions, target);
    
    instantiate_induction(*proof);
    add_line_to_proof(*proof, sum_axiom_base, "ASSUMPTION");
    add_line_to_proof(*proof, sum_axiom_recursive, "ASSUMPTION");
    instantiate_forall(*proof);
    add_line_to_proof(*proof, make_rel(SYM_IN, k, natural_numbers), "ASSUMPTION");
    instantiate_implication(*proof);  // assumes sum(k) = k, goal becomes sum(k+1) = k+1
    add_line_to_proof(*proof, recursive_axiom_inner, "FORALL", 1, 2);
    rewrite_target_using_equality(*proof, 3);
    add_line_to_proof(*proof, make_eq(sum_fn(k), k), "ASSUMPTION");
    rewrite_target_using_equality(*proof, 4);
    k_plus_one := make_function("+", k, one);
    add_line_to_proof(*proof, make_eq(k_plus_one, k_plus_one), "EQ");
    if is_valid(*proof) {
        print("Proof is valid for target: %\n", formula_to_string(target));
    } else {
        print("Proof is NOT valid.\n");
    }
    print("\n");
}

test_swap_proof :: () {
    print("=== Variable Reassignment (Swap) Proof ===\n");
    
    natural_numbers := make_constant(SYM_NAT);
    
    // Terms
    x := make_constant("x");
    y := make_constant("y");
    temp := make_constant("temp");
    zero := make_constant("0");
    one := make_constant("1");
    two := make_constant("2");
    three := make_constant("3");
    
    va_x_0 := make_function("va", x, zero);
    va_x_1 := make_function("va", x, one);
    va_x_2 := make_function("va", x, two);
    va_x_3 := make_function("va", x, three);
    
    va_y_0 := make_function("va", y, zero);
    va_y_1 := make_function("va", y, one);
    va_y_2 := make_function("va", y, two);
    va_y_3 := make_function("va", y, three);
    
    va_temp_1 := make_function("va", temp, one);
    va_temp_2 := make_function("va", temp, two);
    va_temp_3 := make_function("va", temp, three);
    
    vas: [..]*Term;
    array_add(*vas, va_x_0);
    array_add(*vas, va_x_1);
    array_add(*vas, va_x_2);
    array_add(*vas, va_x_3);
    array_add(*vas, va_y_0);
    array_add(*vas, va_y_1);
    array_add(*vas, va_y_2);
    array_add(*vas, va_y_3);
    array_add(*vas, va_temp_1);
    array_add(*vas, va_temp_2);
    array_add(*vas, va_temp_3);
    
    // Assumptions
    va_x_0_eq_va_x_1 := make_eq(va_x_0, va_x_1);
    va_x_2_eq_va_x_3 := make_eq(va_x_2, va_x_3);
    
    va_y_0_eq_va_y_1 := make_eq(va_y_0, va_y_1);
    va_y_1_eq_va_y_2 := make_eq(va_y_1, va_y_2);
    
    va_temp_1_eq_va_temp_2 := make_eq(va_temp_1, va_temp_2);
    va_temp_2_eq_va_temp_3 := make_eq(va_temp_2, va_temp_3);
    
    va_temp_1_eq_va_x_1 := make_eq(va_temp_1, va_x_1);
    va_x_2_eq_va_y_2 := make_eq(va_x_2, va_y_2);
    va_y_3_eq_va_temp_3 := make_eq(va_y_3, va_temp_3);
    
    // Helper function for element of natural assumptions
    make_el_of_nat :: (el: *Term, nat: *Term) -> *Formula {
        return make_rel(SYM_IN, el, nat);
    }
    
    element_of_nat_assumptions: [..]*Formula;
    for va: vas {
        array_add(*element_of_nat_assumptions, make_el_of_nat(va, natural_numbers));
    }
    
    // transitivity
    a := make_variable("a");
    b := make_variable("b");
    c := make_variable("c");
    
    a_eq_b := make_eq(a, b);
    b_eq_c := make_eq(b, c);
    a_eq_c := make_eq(a, c);
    a_eq_b_and_b_eq_c := make_and(a_eq_b, b_eq_c);
    a_eq_b_and_b_eq_c_implies_a_eq_c := make_implies(a_eq_b_and_b_eq_c, a_eq_c);
    
    forall_c := make_forall("c", natural_numbers, a_eq_b_and_b_eq_c_implies_a_eq_c);
    forall_b := make_forall("b", natural_numbers, forall_c);
    forall_a := make_forall("a", natural_numbers, forall_b);
    transitivity := forall_a;
    
    innermost_refl := make_implies(make_eq(a, b), make_eq(b, a));
    inner_refl := make_forall("b", natural_numbers, innermost_refl);
    reflexivity := make_forall("a", natural_numbers, inner_refl);
    
    // Target: va_x_3 = va_y_0 and va_y_3 = va_x_0
    va_x_3_eq_va_y_0 := make_eq(va_x_3, va_y_0);
    va_x_0_eq_va_y_3 := make_eq(va_y_3, va_x_0);
    swapped := make_and(va_x_3_eq_va_y_0, va_x_0_eq_va_y_3);
    
    assumptions: [..]*Formula;
    array_add(*assumptions, va_x_0_eq_va_x_1);
    array_add(*assumptions, va_x_2_eq_va_x_3);
    array_add(*assumptions, va_y_0_eq_va_y_1);
    array_add(*assumptions, va_y_1_eq_va_y_2);
    array_add(*assumptions, va_temp_1_eq_va_temp_2);
    array_add(*assumptions, va_temp_2_eq_va_temp_3);
    array_add(*assumptions, va_temp_1_eq_va_x_1);
    array_add(*assumptions, va_x_2_eq_va_y_2);
    array_add(*assumptions, va_y_3_eq_va_temp_3);
    array_add(*assumptions, transitivity);
    array_add(*assumptions, reflexivity);
    
    for child: element_of_nat_assumptions {
        array_add(*assumptions, child);
    }
    
    proof := create_proof(assumptions, swapped);
    
    for assumption: assumptions {
        add_line_to_proof(*proof, assumption, "ASSUMPTION");
    }
    
    // a replaced by va_x_3
    // forall b, forall c, (...)
    fab_fac := substitute_term_in_formula(forall_b, a, va_x_3);
    add_line_to_proof(*proof, fab_fac, "FORALL", 9, 14);
    
    print_proof(*proof);
    
    // b replaced by va_x_2
    // forall c, (...)
    // Access the inner formula from the forall
    assert(fab_fac.kind == .FORALL);
    fac := fab_fac.forall.inner;
    fac_b_replaced := substitute_term_in_formula(fac, b, va_x_2);
    add_line_to_proof(*proof, fac_b_replaced, "FORALL", 22, 13);
    
    assert(fac_b_replaced.kind == .FORALL);
    inner_forall := fac_b_replaced.forall.inner;
    inner_fa_c_replaced := substitute_term_in_formula(inner_forall, c, va_y_2);
    add_line_to_proof(*proof, inner_fa_c_replaced, "FORALL", 23, 17);
    
    print_proof(*proof);
    
    refl_1 := substitute_term_in_formula(inner_refl, a, va_x_2);
    assert(refl_1.kind == .FORALL);
    refl_2 := substitute_term_in_formula(refl_1.forall.inner, b, va_x_3);
    add_line_to_proof(*proof, refl_1, "FORALL", 10, 13);
    add_line_to_proof(*proof, refl_2, "FORALL", 25, 14);
    
    va_x_3_eq_va_x_2 := make_eq(va_x_3, va_x_2);
    add_line_to_proof(*proof, va_x_3_eq_va_x_2, "IMPLIES", 26, 1);
    add_line_to_proof(*proof, make_and(va_x_3_eq_va_x_2, va_x_2_eq_va_y_2), "AND", 27, 7);
    add_line_to_proof(*proof, make_eq(va_x_3, va_y_2), "IMPLIES", 24, 28);
    
    print_proof(*proof);
    
    print("\n");
}

main :: () {
    test_and();
    test_forall();
    test_excluded_middle();
    test_cases_proof();
    test_induction_modification_rules();
    test_swap_proof();
}

