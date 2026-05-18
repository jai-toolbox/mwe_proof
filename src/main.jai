#import "Basic";
#import "tbx/proof";

#import "knowledge";
#import "generation";

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

test_generalized_forall :: () {
    print("=== GENERALIZED FORALL Proof ===\n");
    natural_numbers := make_constant(SYM_NAT);
    
    x := make_variable("x");
    y := make_variable("y");

    j := make_variable("j");
    k := make_variable("k");

    five := make_constant("5");
    six := make_constant("6");

    X := make_constant("X");
    Y := make_constant("Y");

    j_in_X := make_rel(SYM_IN, j, X);
    k_in_Y := make_rel(SYM_IN, k, Y);
    
    x_eq_5 := make_eq(x, five);
    y_eq_6 := make_eq(y, six);

    both := make_and(x_eq_5, y_eq_6);

    forall_x_both := make_forall("x", X, both);
    forall_y_x_both := make_forall("y", Y, forall_x_both);
    
    assumptions: [..]*Formula;
    array_add(*assumptions, j_in_X);
    array_add(*assumptions, k_in_Y);
    array_add(*assumptions, forall_y_x_both);
    
    target := make_and(make_eq(j, five), make_eq(k, six));

    proof := create_proof(assumptions, target);

    // it's kinda dumb that we have to do this.
    add_line_to_proof(*proof, forall_y_x_both, "ASSUMPTION");
    add_line_to_proof(*proof, k_in_Y, "ASSUMPTION");
    add_line_to_proof(*proof, j_in_X, "ASSUMPTION");

    add_line_to_proof(*proof, target, "GENERALIZED_FORALL", 0, 1, 2);
    
    print_proof(*proof);
    
    if is_valid(*proof) {
        print("Proof is valid for target: %\n", formula_to_string(target));
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

sum_fn :: (t: *Term) -> *Term {
    return make_function("sum", t);
}

triangular_rhs :: (t: *Term) -> *Term {
    one := make_constant("1");
    two := make_constant("2");
    t_plus_one := make_function("+", t, one);
    numerator := make_function("*", t, t_plus_one);
    return make_function("/", numerator, two);
}

triangular_formula :: (t: *Term) -> *Formula {
    return make_eq(sum_fn(t), triangular_rhs(t));
}

test_triangular_number_induction :: () {
    print("\n=== Induction Proof: 1 + ... + n = n * (n + 1) / 2 ===\n");
    print("Arithmetic facts are explicit assumptions; the rest is target rewriting.\n\n");

    positive_naturals := make_constant("N1");
    one := make_constant("1");
    k := make_variable("k");
    n := make_variable("n");

    k_plus_one := make_function("+", k, one);
    sum_k_plus_one_def := make_eq(sum_fn(k_plus_one), make_function("+", sum_fn(k), k_plus_one));
    sum_recurrence := make_forall("k", positive_naturals, sum_k_plus_one_def);
    sum_base_fact := make_eq(sum_fn(one), one);

    target := make_forall("n", positive_naturals, triangular_formula(n));

    arithmetic_facts := make_triangular_arithmetic_facts(positive_naturals);

    assumptions: [..]*Formula;
    array_add(*assumptions, sum_base_fact);
    array_add(*assumptions, sum_recurrence);
    add_triangular_arithmetic_facts(*assumptions, arithmetic_facts);

    proof := create_proof(assumptions, target);

    print("Arithmetic assumptions used:\n");
    print("  base: %\n", formula_to_string(arithmetic_facts.base_one));
    print("  expand k*(k+1): %\n", formula_to_string(arithmetic_facts.mul_successor_expansion));
    print("  put k+1 over 2: %\n", formula_to_string(arithmetic_facts.successor_as_half_twice));
    print("  add halves: %\n", formula_to_string(arithmetic_facts.add_halves));
    print("  distribute 2: %\n", formula_to_string(arithmetic_facts.distribute_two_successor));
    print("  collect numerator: %\n", formula_to_string(arithmetic_facts.collect_triangular_numerator));
    print("  k+1+1 = k+2: %\n\n", formula_to_string(arithmetic_facts.successor_successor_as_plus_two));

    instantiate_induction(*proof);

    // Base target: sum(1) = 1 * (1 + 1) / 2
    add_line_to_proof(*proof, sum_base_fact, "ASSUMPTION");
    rewrite_target_using_equality(*proof, 0);
    add_line_to_proof(*proof, arithmetic_facts.base_one, "ASSUMPTION");

    // Step target: forall k, P(k) -> P(k+1)
    instantiate_forall(*proof, k);
    k_in_positive_naturals := make_rel(SYM_IN, k, positive_naturals);
    add_line_to_proof(*proof, k_in_positive_naturals, "ASSUMPTION");

    add_line_to_proof(*proof, sum_recurrence, "ASSUMPTION");
    add_line_to_proof(*proof, sum_k_plus_one_def, "FORALL", 3, 2);

    instantiate_implication(*proof);
    induction_hypothesis := triangular_formula(k);
    add_line_to_proof(*proof, induction_hypothesis, "ASSUMPTION");

    rewrite_target_using_equality(*proof, 4);
    rewrite_target_using_equality(*proof, 5);

    add_line_to_proof(*proof, arithmetic_facts.mul_successor_expansion, "ASSUMPTION");
    mul_successor_inner := arithmetic_facts.mul_successor_expansion.forall.inner;
    add_line_to_proof(*proof, mul_successor_inner, "FORALL", 6, 2);
    rewrite_target_using_equality(*proof, 7);

    add_line_to_proof(*proof, arithmetic_facts.successor_as_half_twice, "ASSUMPTION");
    successor_as_half_inner := arithmetic_facts.successor_as_half_twice.forall.inner;
    add_line_to_proof(*proof, successor_as_half_inner, "FORALL", 8, 2);
    rewrite_target_using_equality_occurrence(*proof, 9, 0);

    add_line_to_proof(*proof, arithmetic_facts.add_halves, "ASSUMPTION");
    add_halves_inner := arithmetic_facts.add_halves.forall.inner;
    add_line_to_proof(*proof, add_halves_inner, "FORALL", 10, 2);
    rewrite_target_using_equality(*proof, 11);

    add_line_to_proof(*proof, arithmetic_facts.distribute_two_successor, "ASSUMPTION");
    distribute_two_inner := arithmetic_facts.distribute_two_successor.forall.inner;
    add_line_to_proof(*proof, distribute_two_inner, "FORALL", 12, 2);
    rewrite_target_using_equality(*proof, 13);

    add_line_to_proof(*proof, arithmetic_facts.collect_triangular_numerator, "ASSUMPTION");
    collect_numerator_inner := arithmetic_facts.collect_triangular_numerator.forall.inner;
    add_line_to_proof(*proof, collect_numerator_inner, "FORALL", 14, 2);
    rewrite_target_using_equality(*proof, 15);

    add_line_to_proof(*proof, arithmetic_facts.successor_successor_as_plus_two, "ASSUMPTION");
    successor_successor_inner := arithmetic_facts.successor_successor_as_plus_two.forall.inner;
    add_line_to_proof(*proof, successor_successor_inner, "FORALL", 16, 2);
    rewrite_target_using_equality(*proof, 17);

    add_line_to_proof(*proof, get_active_target(*proof), "EQ");

    print_proof(*proof);

    if is_valid(*proof) {
        print("Proof is valid for target: %\n", formula_to_string(target));
    } else {
        print("Proof is NOT valid.\n");
    }
    print("\n");
}

test_finite_range_induction :: () {
    print("\n=== Finite Range Induction Proof ===\n");

    natural_numbers := make_constant(SYM_NAT);
    one := make_constant("1");
    four := make_constant("4");

    n := make_variable("n");
    i := make_variable("i");
    i_plus_one := make_function("+", i, one);

    Pn := make_rel("P", n);
    Pi := make_rel("P", i);
    Psucc := make_rel("P", i_plus_one);

    target_range := make_and(
        make_rel(SYM_LEQ, one, n),
        make_rel(SYM_LEQ, n, four)
    );
    target := make_forall("n", natural_numbers, make_implies(target_range, Pn));

    step_range := make_and(
        make_rel(SYM_LEQ, one, i),
        make_rel("<", i, four)
    );
    step := make_forall("i", natural_numbers, make_implies(step_range, make_implies(Pi, Psucc)));

    base := make_rel("P", one);

    assumptions: [..]*Formula;
    array_add(*assumptions, base);
    array_add(*assumptions, step);

    proof := create_proof(assumptions, target);

    add_line_to_proof(*proof, base, "ASSUMPTION");
    add_line_to_proof(*proof, step, "ASSUMPTION");
    add_line_to_proof(*proof, target, "FINITE_INDUCTION", 0, 1);

    print_proof(*proof);

    if is_valid(*proof) {
        print("Proof is valid for target: %\n", formula_to_string(target));
    } else {
        print("Proof is NOT valid.\n");
    }
    print("\n");
}

test_finite_set_forall_with_successors :: () {
    print("\n=== Finite Set Forall Proof: forall x in {1, 2, 3}, x < 4 ===\n");

    x := make_variable("x");
    zero := make_constant("0");
    one := make_constant("1");
    two := make_constant("2");
    three := make_constant("3");
    four := make_constant("4");

    set_1_2_3 := make_finite_set(one, two, three);
    target := make_forall("x", set_1_2_3, make_rel("<", x, four));

    order_facts := make_finite_set_order_facts();

    assumptions: [..]*Formula;
    add_finite_set_order_facts(*assumptions, order_facts);

    proof := create_proof(assumptions, target);

    print("Order assumptions used:\n");
    print("  seed: %\n", formula_to_string(order_facts.zero_lt_one));
    print("  succ step 0->1: %\n", formula_to_string(order_facts.succ_lt_0_to_1));
    print("  succ step 1->2: %\n", formula_to_string(order_facts.succ_lt_1_to_2));
    print("  succ step 2->3: %\n", formula_to_string(order_facts.succ_lt_2_to_3));
    print("  trans 1,2,3: %\n", formula_to_string(order_facts.trans_1_2_3));
    print("  trans 1,3,4: %\n", formula_to_string(order_facts.trans_1_3_4));
    print("  trans 2,3,4: %\n\n", formula_to_string(order_facts.trans_2_3_4));

    add_line_to_proof(*proof, order_facts.zero_lt_one, "ASSUMPTION");            // 0
    add_line_to_proof(*proof, order_facts.succ_lt_0_to_1, "ASSUMPTION");        // 1
    one_lt_two := make_rel("<", one, two);
    add_line_to_proof(*proof, one_lt_two, "IMPLIES", 1, 0);                     // 2

    add_line_to_proof(*proof, order_facts.succ_lt_1_to_2, "ASSUMPTION");        // 3
    two_lt_three := make_rel("<", two, three);
    add_line_to_proof(*proof, two_lt_three, "IMPLIES", 3, 2);                   // 4

    add_line_to_proof(*proof, order_facts.succ_lt_2_to_3, "ASSUMPTION");        // 5
    three_lt_four := make_rel("<", three, four);
    add_line_to_proof(*proof, three_lt_four, "IMPLIES", 5, 4);                  // 6

    add_line_to_proof(*proof, order_facts.trans_2_3_4, "ASSUMPTION");           // 7
    two_three_and_three_four := make_and(two_lt_three, three_lt_four);
    add_line_to_proof(*proof, two_three_and_three_four, "AND", 4, 6);           // 8
    two_lt_four := make_rel("<", two, four);
    add_line_to_proof(*proof, two_lt_four, "IMPLIES", 7, 8);                    // 9

    add_line_to_proof(*proof, order_facts.trans_1_2_3, "ASSUMPTION");           // 10
    one_two_and_two_three := make_and(one_lt_two, two_lt_three);
    add_line_to_proof(*proof, one_two_and_two_three, "AND", 2, 4);              // 11
    one_lt_three := make_rel("<", one, three);
    add_line_to_proof(*proof, one_lt_three, "IMPLIES", 10, 11);                 // 12

    add_line_to_proof(*proof, order_facts.trans_1_3_4, "ASSUMPTION");           // 13
    one_three_and_three_four := make_and(one_lt_three, three_lt_four);
    add_line_to_proof(*proof, one_three_and_three_four, "AND", 12, 6);          // 14
    one_lt_four := make_rel("<", one, four);
    add_line_to_proof(*proof, one_lt_four, "IMPLIES", 13, 14);                  // 15

    add_line_to_proof(*proof, target, "FINITE_FORALL", 15, 9, 6);               // 16

    print_proof(*proof);

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

test_reflexivity_and_transitivity :: () {
    assumptions : [..] *Formula; 

    array_add(*assumptions, make_transitivity_formula(make_constant("Z")));
    array_add(*assumptions, make_symmetry_formula(make_constant("Z")));

    a := make_variable("a");
    b := make_variable("b");
    c := make_variable("c");

    array_add(*assumptions, make_eq(a, b));
    array_add(*assumptions, make_eq(c, b));

    target := make_eq(a, c);

    proof := create_proof(assumptions, target);

    for assumptions {
        add_line_to_proof(*proof, it, "ASSUMPTION");
    }

    // TODO: we use the new function here to create the proof.

    print_proof(*proof);
}

main :: () {
    // test_and();
    // test_forall();
    // test_generalized_forall();
    // test_excluded_middle();
    // test_cases_proof();
    // test_induction_modification_rules();
    // test_swap_proof();
    // test_reflexivity_and_transitivity();
    // test_equality_graph();
    // test_equality_graph_complex();
}

#import "Basic";
#import "Compiler";

Fact :: struct {
    lhs_expr: string;
    lhs_line: int;
    rhs_expr: string;
    rhs_line: int;
}

TypeFact :: struct {
    expr: string;
    type_set: string;
}

fact_to_string :: (fact: Fact) -> string {
    return tprint("va(%, %) = va(%, %)", fact.lhs_expr, fact.lhs_line, fact.rhs_expr, fact.rhs_line);
}

type_fact_to_string :: (fact: TypeFact) -> string {
    return tprint("% in %", fact.expr, fact.type_set);
}

get_type_set :: (type_infox: *Type_Info) -> string {
    if !type_infox return "?";
    
    if type_infox.type == {
        case .INTEGER;  return "Z";
        case .FLOAT;    return "R";
        case .BOOL;     return "B";
        case .STRING;   return "String";
    }
    
    return "?";
}

generate_type_facts :: (body: *Code_Procedure_Body) -> [..] TypeFact {
    type_facts: [..] TypeFact;
    
    if body.header {
        for arg: body.header.arguments {
            arg_type := arg.type;  // Type_Info for the argument

            if arg_type == null {
                continue;
            }
            
            if arg_type.type == .POINTER {
                ptr_info := cast(*Type_Info_Pointer) arg_type;
                pointed_type := ptr_info.pointer_to;
                
                type_set := get_type_set(pointed_type);
                if type_set != "?" {
                    fact: TypeFact;
                    fact.expr = tprint("%.*", arg.name);
                    fact.type_set = type_set;
                    array_add(*type_facts, fact);
                }
            } else { // non-pointer argument
                type_set := get_type_set(arg_type);
                if type_set != "?" {
                    fact: TypeFact;
                    fact.expr = copy_string(arg.name);
                    fact.type_set = type_set;
                    array_add(*type_facts, fact);
                }
            }
        }
    }
    
    return type_facts;
}

node_to_string :: (node: *Code_Node) -> string {
    if !node return "???";
    
    if node.kind == {
        case .IDENT;
            ident := cast(*Code_Ident) node;
            return copy_string(ident.name);
            
        case .UNARY_OPERATOR;
            unary := cast(*Code_Unary_Operator) node;
            op := cast(Operator_Type) unary.operator_type;
            if op == .POINTER_DEREFERENCE || op == .POSTFIX_DEREFERENCE {
                sub := node_to_string(unary.subexpression);
                return tprint("%.*", sub);
            }
            if unary.operator_type == xx #char "*" {
                sub := node_to_string(unary.subexpression);
                return tprint("*%", sub);
            }
    }
    
    return "???";
}

generate_facts :: (body: *Code_Procedure_Body) -> [..] Fact {
    facts: [..] Fact;
    tracked: [..] string;
    
    if body.header {
        for body.header.arguments {
            if it.type_inst && it.type_inst.pointer_to {
                array_add(*tracked, tprint("%.*", it.name));
            } else {
                array_add(*tracked, copy_string(it.name));
            }
        }
    }
    
    if body.block {
        line := 1;
        for stmt: body.block.statements {
            modified_expr: string;
            rhs_expr: string;
            
            if stmt.kind == {
                case .DECLARATION;
                    decl := cast(*Code_Declaration) stmt;
                    modified_expr = copy_string(decl.name);
                    if decl.expression {
                        rhs_expr = node_to_string(decl.expression);
                    }
                    array_add(*tracked, modified_expr);
                    
                case .BINARY_OPERATOR;
                    binop := cast(*Code_Binary_Operator) stmt;
                    if binop.operator_type == xx #char "=" {
                        modified_expr = node_to_string(binop.left);
                        rhs_expr = node_to_string(binop.right);
                    }
            }
            
            for expr: tracked {
                fact: Fact;
                fact.lhs_expr = expr;
                fact.lhs_line = line;
                
                if expr == modified_expr {
                    fact.rhs_expr = rhs_expr;
                    fact.rhs_line = line - 1;
                } else {
                    fact.rhs_expr = expr;
                    fact.rhs_line = line - 1;
                }
                
                array_add(*facts, fact);
            }
            
            line += 1;
        }
    }
    
    return facts;
}

Procedure_Facts :: struct {
    type_facts: [..] TypeFact;
    value_facts: [..] Fact;
    assumptions: [..]*Formula;
}

Extract_Context :: struct {
    function_name: string;
    arguments: [..] string;
}

is_argument_name :: (ctx: *Extract_Context, name: string) -> bool {
    for arg: ctx.arguments {
        if arg == name return true;
    }

    return false;
}

operator_string :: (op: Operator_Type) -> string {
    if op == xx #char "+" return "+";
    if op == xx #char "-" return "-";
    if op == xx #char "*" return "*";
    if op == xx #char "/" return "/";
    if op == xx #char "=" return "=";
    if op == xx #char "<" return "<";
    if op == xx #char ">" return ">";

    result := operator_to_string(op);
    if result.count return result;

    return "?";
}

node_to_source_string :: (node: *Code_Node) -> string {
    if !node return "???";

    if node.kind == {
        case .IDENT;
            ident := cast(*Code_Ident) node;
            return copy_string(ident.name);

        case .LITERAL;
            literal := cast(*Code_Literal) node;
            if literal.value_type == {
                case .NUMBER;
                    if literal.value_flags & .FLOAT return tprint("%", literal._float64);
                    if literal.value_flags & .MINUS_SIGN return tprint("-%", literal._s64);
                    return tprint("%", literal._s64);

                case .BOOLEAN;
                    return ifx literal._s64 != 0 then "true" else "false";

                case .STRING;
                    return tprint("\"%\"", literal._string);
            }

        case .BINARY_OPERATOR;
            binop := cast(*Code_Binary_Operator) node;
            return tprint("% % %", node_to_source_string(binop.left), operator_string(binop.operator_type), node_to_source_string(binop.right));

        case .UNARY_OPERATOR;
            unary := cast(*Code_Unary_Operator) node;
            if unary.operator_type == .POSTFIX_DEREFERENCE {
                return tprint("%.*", node_to_source_string(unary.subexpression));
            }
            return tprint("%%", operator_string(unary.operator_type), node_to_source_string(unary.subexpression));
    }

    return "???";
}

node_to_source_term :: (node: *Code_Node) -> *Term {
    if !node return make_constant("???");

    if node.kind == {
        case .IDENT;
            ident := cast(*Code_Ident) node;
            return make_constant(ident.name);

        case .LITERAL;
            return make_constant(node_to_source_string(node));

        case .BINARY_OPERATOR;
            binop := cast(*Code_Binary_Operator) node;
            return make_function(operator_string(binop.operator_type), node_to_source_term(binop.left), node_to_source_term(binop.right));

        case .UNARY_OPERATOR;
            return make_constant(node_to_source_string(node));
    }

    return make_constant(node_to_source_string(node));
}

node_to_value_term :: (node: *Code_Node, time: *Term, ctx: *Extract_Context) -> *Term {
    if !node return make_constant("???");

    if node.kind == {
        case .IDENT;
            ident := cast(*Code_Ident) node;
            if is_argument_name(ctx, ident.name) return make_variable(ident.name);
            return make_function("va", make_constant(ident.name), time);

        case .LITERAL;
            return node_to_source_term(node);

        case .BINARY_OPERATOR;
            binop := cast(*Code_Binary_Operator) node;
            return make_function(operator_string(binop.operator_type), node_to_value_term(binop.left, time, ctx), node_to_value_term(binop.right, time, ctx));

        case .UNARY_OPERATOR;
            return node_to_source_term(node);
    }

    return node_to_source_term(node);
}

node_to_condition_formula :: (node: *Code_Node, time: *Term, ctx: *Extract_Context) -> *Formula {
    if !node return make_rel("truthy", make_constant("???"));

    if node.kind == .BINARY_OPERATOR {
        binop := cast(*Code_Binary_Operator) node;
        op := operator_string(binop.operator_type);

        if op == "<" || op == ">" || op == "<=" || op == ">=" || op == "==" || op == "!=" {
            return make_rel(op, node_to_value_term(binop.left, time, ctx), node_to_value_term(binop.right, time, ctx));
        }
    }

    return make_rel("truthy", node_to_value_term(node, time, ctx));
}

hits_term :: (line: int) -> *Term {
    return make_function("hits", make_constant(tprint("%", line)));
}

es_term :: (time: *Term) -> *Term {
    return make_function("ES", time);
}

line_term :: (line: int) -> *Term {
    return make_constant(tprint("%", line));
}

next_time_term :: () -> *Term {
    return make_function("+", make_variable("l"), make_constant("1"));
}

previous_time_term :: () -> *Term {
    return make_function("-", make_variable("l"), make_constant("1"));
}

assignment_formula :: (line: int, lhs: *Term, value_time: *Term, rhs: *Term, next_line: int) -> *Formula {
    value_update := make_eq(make_function("va", lhs, value_time), rhs);
    control_update := make_eq(es_term(next_time_term()), line_term(next_line));
    return make_forall("l", hits_term(line), make_and(value_update, control_update));
}

return_formula :: (line: int, returned: *Term, ctx: *Extract_Context) -> *Formula {
    args: [..]*Term;
    for arg: ctx.arguments {
        array_add(*args, make_variable(arg));
    }

    lhs := make_function_from_array(ctx.function_name, args);
    rhs := make_function("va", returned, previous_time_term());
    return_value := make_eq(lhs, rhs);
    finite_execution := make_rel(SYM_IN, cardinality(domain(make_constant("ES"))), make_constant("N0"));
    return make_forall("l", hits_term(line), make_and(return_value, finite_execution));
}

extract_statement_assumptions :: (stmt: *Code_Node, line: int, next_line: int, loop_back_line: int, ctx: *Extract_Context, out: *[..]*Formula) {
    if !stmt return;

    if stmt.kind == {
        case .DECLARATION;
            decl := cast(*Code_Declaration) stmt;
            rhs := ifx decl.expression then node_to_source_term(decl.expression) else make_constant("???");
            value_time := ifx line == 1 then line_term(1) else make_variable("l");
            array_add(out, assignment_formula(line, make_constant(decl.name), value_time, rhs, next_line));

        case .BINARY_OPERATOR;
            binop := cast(*Code_Binary_Operator) stmt;
            lhs := node_to_source_term(binop.left);

            if binop.operator_type == .PLUS_ASSIGN {
                rhs := make_function("+", make_function("va", lhs, previous_time_term()), node_to_value_term(binop.right, previous_time_term(), ctx));
                array_add(out, assignment_formula(line, lhs, make_variable("l"), rhs, next_line));
            } else if binop.operator_type == xx #char "=" {
                rhs := node_to_value_term(binop.right, previous_time_term(), ctx);
                array_add(out, assignment_formula(line, lhs, make_variable("l"), rhs, next_line));
            }

        case .WHILE;
            w := cast(*Code_While) stmt;
            condition := node_to_condition_formula(w.condition, previous_time_term(), ctx);
            enter_loop := make_implies(condition, make_eq(es_term(next_time_term()), line_term(line + 1)));
            exit_loop := make_implies(make_not(condition), make_eq(es_term(next_time_term()), line_term(next_line)));
            array_add(out, make_forall("l", hits_term(line), make_and(enter_loop, exit_loop)));

            if w.block {
                for child, i: w.block.statements {
                    child_line := line + 1 + cast(int) i;
                    child_next := ifx i + 1 < w.block.statements.count then child_line + 1 else loop_back_line;
                    extract_statement_assumptions(child, child_line, child_next, loop_back_line, ctx, out);
                }
            }

        case .RETURN;
            r := cast(*Code_Return) stmt;
            returned := make_constant("???");
            if r.arguments_sorted.count {
                returned = node_to_source_term(r.arguments_sorted[0]);
            }

            array_add(out, return_formula(line, returned, ctx));
    }
}

extract_procedure_assumptions :: (body: *Code_Procedure_Body) -> [..]*Formula {
    assumptions: [..]*Formula;

    ctx: Extract_Context;
    ctx.function_name = copy_string(body.header.name);
    for arg: body.header.arguments {
        array_add(*ctx.arguments, copy_string(arg.name));
    }

    for arg: ctx.arguments {
        array_add(*assumptions, make_eq(make_function("va", make_constant(arg), make_constant("0")), make_variable("x")));
    }

    if !body.block return assumptions;

    line := 1;
    for stmt, i: body.block.statements {
        next_line := line + 1;
        loop_back_line := -1;

        if stmt.kind == .WHILE {
            w := cast(*Code_While) stmt;
            close_line := line + 1 + cast(int) w.block.statements.count;
            next_line = close_line + 1;
            loop_back_line = line;
        } else if i + 1 < body.block.statements.count && body.block.statements[i + 1].kind == .WHILE {
            next_line = line + 1;
        }

        extract_statement_assumptions(stmt, line, next_line, loop_back_line, *ctx, *assumptions);

        if stmt.kind == .WHILE {
            w := cast(*Code_While) stmt;
            line += cast(int) w.block.statements.count + 2;
        } else {
            line += 1;
        }
    }

    return assumptions;
}

generate_procedure_facts :: (body: *Code_Procedure_Body) -> Procedure_Facts {
    facts: Procedure_Facts;
    facts.type_facts = generate_type_facts(body);
    facts.value_facts = generate_facts(body);
    facts.assumptions = extract_procedure_assumptions(body);
    return facts;
}

print_procedure_assumptions :: (body: *Code_Procedure_Body, assumptions: []*Formula) {
    function_name := ifx body.header then body.header.name else "<anonymous>";

    print("=== Extracted assumptions for % ===\n\n", function_name);

    for assumption, i: assumptions {
        print("  [%] %\n", i, formula_to_string(assumption));
    }
}

create_initial_sum_termination_proof :: (facts: Procedure_Facts) {
    print("\n=== Initial Proof: sum_of_1_to_n execution cardinality ===\n\n");

    proof_assumptions: [..]*Formula;
    for assumption: facts.assumptions {
        array_add(*proof_assumptions, assumption);
    }
    return_fact_idx := facts.assumptions.count - 1;

    N0 := make_constant("N0");
    N1 := make_constant("N1");
    ES := make_constant("ES");
    domain_ES := domain(ES);
    image_ES := image(ES);
    card_domain_ES := cardinality(domain_ES);
    x := make_variable("x");

    array_add(*proof_assumptions, make_rel("function_type", ES, N0, N0));
    array_add(*proof_assumptions, make_rel(SYM_IN, x, N1));

    finite_case := make_rel(SYM_IN, card_domain_ES, N0);
    not_finite_case := make_not(finite_case);
    return_line_in_image := make_rel(SYM_IN, make_constant("7"), image_ES);
    return_line_not_in_image := make_not(return_line_in_image);
    k := make_variable("k");
    k_in_hits_7 := make_rel(SYM_IN, k, hits_term(7));
    image_7_gives_hit_7 := make_implies(return_line_in_image, k_in_hits_7);
    contradiction := logic_contradiction();
    image_refute_left := make_refute_left_fact(return_line_in_image, return_line_not_in_image);
    finite_refute_right := make_refute_right_fact(finite_case, not_finite_case);

    image_7_gives_hit_7_idx := proof_assumptions.count;
    array_add(*proof_assumptions, image_7_gives_hit_7);
    array_add(*proof_assumptions, image_refute_left);
    array_add(*proof_assumptions, finite_refute_right);
    image_refute_left_idx := image_7_gives_hit_7_idx + 1;
    finite_refute_right_idx := image_7_gives_hit_7_idx + 2;

    target := finite_case;

    proof := create_proof(proof_assumptions, target);

    for assumption: proof_assumptions {
        add_line_to_proof(*proof, assumption, "ASSUMPTION");
    }

    finite_cases := make_or(finite_case, not_finite_case);
    add_line_to_proof(*proof, finite_cases, "LEM");
    finite_cases_line := proof.lines.count - 1;

    image_cases := make_or(return_line_in_image, return_line_not_in_image);
    add_line_to_proof(*proof, image_cases, "LEM");
    image_cases_line := proof.lines.count - 1;

    finite_contradiction_subgoal := make_implies(not_finite_case, contradiction);
    begin_subproof(*proof, finite_contradiction_subgoal);
    instantiate_implication(*proof);
    add_line_to_proof(*proof, not_finite_case, "IMPLIES_ASSUMPTION");
    not_finite_line := proof.lines.count - 1;

    image_refutation_subgoal := make_and(
        image_cases,
        make_implies(return_line_in_image, contradiction)
    );
    begin_subproof(*proof, image_refutation_subgoal);

    image_contradiction_subgoal := make_implies(return_line_in_image, contradiction);
    begin_subproof(*proof, image_contradiction_subgoal);
    instantiate_implication(*proof);
    add_line_to_proof(*proof, return_line_in_image, "IMPLIES_ASSUMPTION");
    return_line_in_image_line := proof.lines.count - 1;

    add_line_to_proof(*proof, k_in_hits_7, "IMPLIES", image_7_gives_hit_7_idx, return_line_in_image_line);
    k_in_hits_7_line := proof.lines.count - 1;

    return_value := make_eq(make_function("sum_of_1_to_n", make_variable("n")), make_function("va", make_constant("sum"), make_function("-", make_variable("k"), make_constant("1"))));
    return_line_fact := make_and(return_value, finite_case);
    add_line_to_proof(*proof, return_line_fact, "FORALL", return_fact_idx, k_in_hits_7_line);
    return_line_fact_line := proof.lines.count - 1;

    add_line_to_proof(*proof, finite_case, "AND_RIGHT", return_line_fact_line);
    finite_case_line := proof.lines.count - 1;

    add_line_to_proof(*proof, contradiction, "CONTRADICTION", finite_case_line, not_finite_line);
    contradiction_line := proof.lines.count - 1;

    add_line_to_proof(*proof, image_contradiction_subgoal, "IMPLIES_INTRO", return_line_in_image_line, contradiction_line);
    image_contradiction_line := proof.lines.count - 1;

    add_line_to_proof(*proof, image_refutation_subgoal, "AND", image_cases_line, image_contradiction_line);
    image_refutation_line := proof.lines.count - 1;

    add_line_to_proof(*proof, return_line_not_in_image, "IMPLIES", image_refute_left_idx, image_refutation_line);
    return_line_not_in_image_line := proof.lines.count - 1;

    add_line_to_proof(*proof, contradiction, "CONTRADICTION", return_line_in_image_line, return_line_not_in_image_line);
    outer_contradiction_line := proof.lines.count - 1;

    add_line_to_proof(*proof, finite_contradiction_subgoal, "IMPLIES_INTRO", not_finite_line, outer_contradiction_line);
    finite_contradiction_line := proof.lines.count - 1;

    finite_refutation_subgoal := make_and(finite_cases, finite_contradiction_subgoal);
    add_line_to_proof(*proof, finite_refutation_subgoal, "AND", finite_cases_line, finite_contradiction_line);
    finite_refutation_line := proof.lines.count - 1;

    add_line_to_proof(*proof, finite_case, "IMPLIES", finite_refute_right_idx, finite_refutation_line);

    print_proof(*proof);
}

create_proof_from_extracted_facts :: (type_facts: [..] TypeFact, value_facts: [..] Fact) {
    print("=== Proof from Extracted Facts ===\n\n");
    
    get_type_set_term :: (type_set: string) -> *Term {
        if type_set == "Z" return make_constant("Z");
        if type_set == "R" return make_constant("R");
        if type_set == "B" return make_constant("B");
        if type_set == "String" return make_constant("String");
        return make_constant("?");
    }
    
    assumptions: [..]*Formula;
    
    // Create type membership assumptions from type facts
    for tf: type_facts {
        expr_term := make_constant(tf.expr);
        type_set_term := get_type_set_term(tf.type_set);
        membership := make_rel(SYM_IN, expr_term, type_set_term);
        array_add(*assumptions, membership);
    }
    
    // Create value equality assumptions from value facts
    for vf: value_facts {
        lhs_term := make_function("va", make_constant(vf.lhs_expr), make_constant(tprint("%", vf.lhs_line)));
        rhs_term := make_function("va", make_constant(vf.rhs_expr), make_constant(tprint("%", vf.rhs_line)));
        equality := make_eq(lhs_term, rhs_term);
        array_add(*assumptions, equality);
    }

    
    // Target: va_x_3 = va_y_0 and va_y_3 = va_x_0

    x := make_constant("x.*");
    y := make_constant("y.*");
    temp := make_constant("temp");

    zero := make_constant("0");
    three := make_constant("3");
    Z := make_constant("Z");

    for i: 0..3 {
        blah := make_rel(SYM_IN, make_function("va", x, make_constant(sprint("%", i))), Z);
        blahy := make_rel(SYM_IN, make_function("va", y, make_constant(sprint("%", i))), Z);
        blaht := make_rel(SYM_IN, make_function("va", temp, make_constant(sprint("%", i))), Z);
        array_add(*assumptions, blah, blahy, blaht);
    }

    array_add(*assumptions, make_transitivity_formula(make_constant("Z")));
    array_add(*assumptions, make_symmetry_formula(make_constant("Z")));

    va_x_0 := make_function("va", x, zero);
    va_x_3 := make_function("va", x, three);

    va_y_0 := make_function("va", y, zero);
    va_y_3 := make_function("va", y, three);

    va_x_3_eq_va_y_0 := make_eq(va_x_3, va_y_0);
    va_x_0_eq_va_y_3 := make_eq(va_y_3, va_x_0);
    swapped := make_and(va_x_3_eq_va_y_0, va_x_0_eq_va_y_3);
    
    proof := create_proof(assumptions, swapped);
    
    for assumption: assumptions {
        add_line_to_proof(*proof, assumption, "ASSUMPTION");
    }

    success := try_prove_equality(*proof, va_y_3, va_x_0, make_constant("Z"));
    success = try_prove_equality(*proof, va_x_3, va_y_0, make_constant("Z"));

    add_line_to_proof(*proof, swapped, "AND", 36, 30);
    
    print_proof(*proof);
}

/*

----
Terminology

----

Execution Sequence

Supposing that a given program terminates on some input, then ES is the sequence ({0, ..., k} -> N0), for any integer i in {0, ..., k} it maps i to the ith expression number executed in the program (for most programs this equates to the line number).

----
Hits

Once the execution sequence exists, then given a line number n, we can define hits(n) = {j in N : ES(j) = n}

then we can define hit_map(n) to be the function f : {0, ..., |hits(n) - 1|} -> N0 (where the output is an index into ES).

f(i) = j such that j in hits(n) : |{h in hits(n) : h < j}| = i (we can prove this is a function because the choice of j is unique)

Note the strict less that works here because when i = 0, we're selecting the element that has no element in Hn smaller than it.

----
Value After

va(x, n) is the value of x, after executing the expression with number ES(n) (usually just a line number).

---- 
Implicit Equalities 

Given i and i+1 and a collection of existing variables V such that x in V, if ES(i+1) is not an assignment to x, then the line ES(i+1) emits the assumption that va(v, i+1) = va(v, i) for all v otherwise if it is an assignment to x, then we obtain va(v, i+1) = v(v, i) for all v in V if v != x.

---------

0: sum_of_1_to_n :: (n : int) {   |
1:     sum := 0;                  |  fa l in hits(1), va(sum, 1) = 0 and ES(l+1) = 2
2:     i := 1;                    |  fa l in hits(2), va(i, l) = 1   and ES(l+1) = 3
3:     while i <= n {             |  fa l in hits(3), if va(i, l-1) <= n imp ES(l+1) = 4 else ES(l+1) = 7
4:         sum += i;              |  fa l in hits(4), va(sum, l) = va(sum, l-1) + va(i, l-1) and ES(l+1) = 5
5:         i += 1;                |  fa l in hits(5), va(i, l) = va(i, l-1) + 1 and ES(l+1) = 3 (go back)
6:     }                          |  
7:     return sum;                |  fa l in hits(7), sum_of_1_to_n(n) = va(sum, 6), |dom(ES)| in N0
8: }                              |

need to prove: sum_of_1_to_n(n) = sum(1, n)

where

sum(n) = n + sum(n-1), n > 1
sum(1) = 1

----

PROOF OF TERMINATION:

Suppose for the sake of contradiction that the function does not terminate, therefore dom(hm3) = N, we first prove that:

for any t in dom(hm3), va(i, hm3(t)) = t + 1 (we can paste the below proof, changing the finite set to be N).

since dom(hm3) is infinite and contains an element k > n, then we can show that it would terminate on the next iteration cont.

Therefore the function terminates and let ES be the finite execution sequence of the function.

----

First we start with the variable i.

Let hm3 = hit_map(3), and let dom(hm3) = {0, ..., k - 1} for some k in N.

We prove that for any t in {0, ..., k - 1},

    va(i, hm3(t)) = t + 1.

Base case:

We want to prove:

    va(i, hm3(0)) = 1.

We can asses the start of the function, we know that ES(0) = 0, so 0 in hits(0), thus ES(0 + 1) = 1
Now we know ES(1) = 1 so 1 in hits(1), so ES(1 + 1) = 2, ... so ES(3) = 3

Since hm3(0) is defined to be the unique j in hits(3) such that:

    |{h in hits(3) : h < j}| = 0,

and since no earlier execution-sequence index is a hit of line 3 (by the above enumeration), we have:

    hm3(0) = 3.

Therefore:

    va(i, hm3(0)) = va(i, 3).

By implicit equality from 2 to 3, since ES(3) = 3 is not an assignment to i:

    va(i, 3) = va(i, 2).

So:

    va(i, hm3(0)) = va(i, 3) = va(i, 2) = 1 = 0 + 1 , as needed

Inductive step:

Let t in {0, ..., k - 2}. Assume: va(i, hm3(t)) = t + 1.

We want to prove: va(i, hm3(t + 1)) = t + 2.

Since hm3(t) in hits(3), by the assumption for line 3:

    if va(i, hm3(t) - 1) <= n then ES(hm3(t) + 1) = 4 else ES(hm3(t) + 1) = 7.

Since t + 1 in dom(hm3), hm3(t + 1) exists. Therefore hm3(t) is not the final hit of line 3, so the branch to line 7 cannot occur at hm3(t).

Therefore:

    ES(hm3(t))     = 3
    ES(hm3(t) + 1) = 4
    ES(hm3(t) + 2) = 5
    ES(hm3(t) + 3) = 3

So we can say that hm3(t + 1) = hm3(t) + 3

Since hm3(t) + 2 in hits(5), by the assumption for line 5: va(i, hm3(t) + 2) = va(i, hm3(t) + 1) + 1

By implicit equality from hm3(t) to hm3(t) + 1, since ES(hm3(t) + 1) = 4 is not an assignment to i:

    va(i, hm3(t) + 1) = va(i, hm3(t)).

Therefore:

    va(i, hm3(t) + 2)
    = va(i, hm3(t) + 1) + 1
    = va(i, hm3(t)) + 1
    = (t + 1) + 1
    = t + 2.

By implicit equality from hm3(t) + 2 to hm3(t) + 3, since ES(hm3(t) + 3) = 3 is not an assignment to i:

    va(i, hm3(t) + 3) = va(i, hm3(t) + 2).

Therefore:

    va(i, hm3(t) + 3) = va(i, hm3(t+1)) = t + 2. as needed.

Therefore, by finite induction:

    for all t in {0, ..., k - 1},
    va(i, hm3(t)) = t + 1.

----

Now we want to prove that the return value is sum(n).

Let hm4 = hit_map(4), and let dom(hm4) = {0, ..., k - 1}.

We prove that for every t in {0, ..., k - 1},

    va(sum, hm4(t)) = sum(t + 1).

Base case:

We want to prove:

    va(sum, hm4(0)) = sum(1).

Since hm4(0) in hits(4) then we have that:


va(sum, hm(4) ) = va(sum, hm4(0)-1) + va(i, hm4(0) - 1) and ES(hm4(0)+1) = 5

We can see that hm4(0) - 1 = hm3(0) and from the previous proof: va(i, hm3(0)) = 1.

va(sum, 3) = va(sum, 2), = va(sum, 1) = 0, thus and since hm4(0) = 4 we have:

va(sum, hm(4)) = va(sum, hm4(0)-1) + va(i, hm4(0) - 1) 
               = 0 + 1 = sum(1)

Inductive step:

Let t in {0, ..., k - 2}. Assume:

    va(sum, hm4(t)) = sum(t + 1).

We want to prove:

    va(sum, hm4(t + 1)) = sum(t + 2).

Because hm4(t + 1) in hits(4), then we know that

(1) va(sum, hm4(t + 1)) = va(sum, hm4(t + 1) - 1) + va(i, hm4(t + 1) - 1) and ES(hm4(t+1) + 1) = 5

Also since hm4(t + 1) in hits(4), and since every hit of line 4 comes immediately after a hit of line 3, we have:

    hm4(t + 1) - 1 in hits(3), and moreover hm4(t + 1) - 1 = hm3(t + 1)

From the previous proof about i:

    va(i, hm3(t + 1)) = t + 2.

Therefore:

    va(i, hm4(t + 1) - 1) = t + 2.

revisiting (1) we have:

    va(sum, hm4(t + 1)) = va(sum, hm4(t + 1) - 1) + va(i, hm4(t + 1) - 1)
                        = va(sum, hm4(t + 1) - 1) + (t + 2)

Now we prove:

    va(sum, hm4(t + 1) - 1) = va(sum, hm4(t)) and then use the induction hypothesis

Since hm4(t) in hits(4), by the assumption for line 4:

    ES(hm4(t) + 1) = 5.

Therefore:

    hm4(t) + 1 in hits(5).

Since hm4(t) + 1 in hits(5), by the assumption for line 5:

    ES(hm4(t) + 2) = 3.

Therefore:

    hm4(t) + 2 in hits(3).

Since hm4(t) + 2 in hits(3), and hm4(t + 1) exists, by the assumption for line 3 the branch to line 4 occurs, so:

    ES(hm4(t) + 1) = 5
    ES(hm4(t) + 2) = 3
    ES(hm4(t) + 3) = 4.

So hm4(t) + 3 is the next hit of line 4 after hm4(t). Therefore:

    hm4(t + 1) = hm4(t) + 3.

Thus:

    hm4(t + 1) - 1 = hm4(t) + 2.

Since line 5 and line 3 do not assign to sum, by implicit equalities:

    va(sum, hm4(t)) = va(sum, hm4(t) + 1) = va(sum, hm4(t) + 2) = va(sum, hm(t) + 3) = va(sum, hm(t+1))

By the induction hypothesis:

    va(sum, hm4(t)) = sum(t + 1).

Therefore:

    va(sum, hm4(t + 1) - 1) = sum(t + 1).

So:

    va(sum, hm4(t + 1))
    = sum(t + 1) + (t + 2)
    = sum(t + 2).

Therefore, by finite induction:

    for all t in {0, ..., k - 1}, va(sum, hm4(t)) = sum(t + 1).

----

Now we prove that if dom(hm4) = {0, ..., k - 1}, then k = n.

Note that dom(hm3) = {0, ..., k}, because on the last iteration it will branch.

By the first proof we can see that va(i, hm3(k - 1)) = k > n, and recall the assumptions 

if va(i, hm3(k-1)-1) <= n imp ES(hm3(k - 1) + 1) = 4 else ES(hm3(k - 1) + 1) = 7

And because va(i, hm3(k - 1)) > n, then ES(hm3(k - 1) + 1) = 7, and the execution never re-visits ES(hm3(k - 1)) = 3, so there is no hm3(k) which is a contradiction.

Now suppose that k < n, then that means that va(i, hm3(k - 1)) = k < n therefore it implies that ES(hm3(k - 1) + 1) = 4, thus hm3(k - 1) + 3 = hm3(k + 1), so the dom increased by size one cont. 

Therefore it must be that k = n

----

Thus we have proven that dom(hm4) = {0, ..., n - 1}.

So by the sum proof, we have:

    va(sum, hm4(n - 1)) = sum(n).

Since the execution sequence never revists line 4, then it must be that the execution sequence is given by ES(hm4(n - 1)) = 4, 5, 6, 7

sum is never assigned to on lines 5 6 thus by transitivity and implicit equalities, we have that va(sum, 6) = va(sum, 5) = va(sum, 4) = va(sum, hm4(n - 1)). 
Thus sum_of_1_to_n(n) = va(sum, hm4(n - 1)) = sum(n), as needed.


*/

/*

Let n in Z

0: abs :: (x : int) {   | va(x, 0) = n, ES(1) = 1
1:     if (x < 0) {     | fa l in hit_map(1), if va(x, l - 1) < 0 then ES(l + 1) = 2 else ES(l + 1) = 4
2:         return -x;   | fa l in hit_map(2), ret = -va(x, l - 1)
3:     }                |
4:      return x;       | fa l in hit_map(4), ret = va(x, 1)
5: }                    |        

We want to prove that for all n in Z, abs(n) = |n|

Suppose that x in Z. When the function starts we know that ES(0) = 0, so therefore va(x, 0) = n. 

If n < 0, then va(x, 0) < 0, thus ES(2) = 2, so 2 in hit_map(2), and we deduce that ret = -va(x, 1) = -va(x, 0) = -n
If n >= 0, then va(x, 0) >= 0, thus ES(2) = 4 and ret = va(x, 1) = va(x, 0) = n.

So abs(n) = |n|

*/

/*


implicit function equality: If a line does f(i) = blah, then we obtain a bunch of pairwise equalities ie fa j != i, va(f, l)(j) = va(f, l - 1)(j), and va(f, l)(i) = blah
otherwise we just do va(f, l) = va(f, l-1) which is function equality which says that they match on everything.


Let k in N and Let f : {0, ..., k - 1} -> N0 be a function


00: bubble :: (a : *[..] int) {                                            | va(a, 0) = f and ES(1) = 1
01:     num_sorted_elements := 0;                                          | va(num_sorted_elements, 1) = 0 and ES(2) = 2
02:     second_largest_index_into_a := (a.*).count - 2;                    | va(second_largest_index_into_l, 2) = |dom(a)| - 2 and ES(3) = 4
03:     while num_sorted_elements != (a.*).count {                         | fa l in hits(3), if va(num_sorted_elements, l - 1) != |dom(va(a, l - 1))| then ES(l+1) = 4 else ES(l+1) = 14
04:         i := 0;                                                        | fa l in hits(4), va(i, l - 1) = 0, ES(l + 1) = 5
05:         while i <= second_largest_index_into_a - num_sorted_elements { | fa l in hits(5), if va(i, l - 1) <= va(sliia, l - 1) - va(nse, l - 1) then ES(l + 1) = 6 else ES(l + 1) = 13
06:             curr : int = (a.*)[i];                                     | fa l in hits(6), va(curr, l) = va(a, l-1)(va(i, l - 1)) 
07:             next : int = (a.*)[i+1];                                   | fa l in hits(7), va(next, l) = va(a, l-1)(va(i, l - 1) + 1)
08:             if curr > next {                                           | fa l in hits(8), if va(curr, l - 1) > va(next, l - 1) then ES(l + 1) = 9 else ES(l + 1) = 11
09:                 swap(*(a.*)[i], *(a.*)[i + 1]);                        | fa l in hits(9), va(a, l)(i) = va(a, l - 1)(i+1) and va(a, l)(i+1) = va(a, l - 1)(i) and (pairwise rest eqs)
10:             }                                                          | 
11:             i += 1;                                                    | fa l in hits(11), va(i, l) = va(i, l - 1) + 1, ES(l + 1) = 5
12:         }                                                              | 
13:         num_sorted_elements += 1;                                      | fa l in hits(13), va(num_sorted_elements, l) = va(num_sorted_elements, l - 1) + 1
14:     }                                                                  |
15: }                       

Suppose that ES is the execution sequence of bubble on f. 

----

We will prove that bubble terminates, that is equivalent to showing that 14 in ES, then ES is finite 
that is equivalent to finding some l, such that va(num_sorted_elements, l - 1) == |dom(va(a, l - 1))|

First we show that the inner while loop terminates. Note that second_largest_index_into_a is constant, that means that for any l in dom(ES), va(second_largest_index_into_a, l) = _

Let hm5 = hit_map(5) and suppose that l in dom(hm5), if the while loop never terminated then ES = (... 5, 6, 7, 8, 9, 10, 11, 5 6, 7, 8, 9, 10, 11 ...) and line 13 is never reached. 

None ES(5) ... ES(11) do not modify second_largest_index_into_a or num_sorted_elements, thus by the implicit equalites we can show that 

for any j >= hm5(l), va(second_largest_index_into_a, j) = va(second_largest_index_into_a, l - 1) and va(num_sorted_elements, j) = va(num_sorted_elements, l - 1)

(this would be proven by induction).

we can also prove that fa k in N0  va(i, hm5(l + k)) = k (induction), thus we can pick k to be larger than va(second_larget_index_into_a, l - 1) - va(num_sorted_elements, l - 1), which would get us exit the loop which is a contradiction. Thus it must be that the inner while loop always terminates sometime after it starts.

Let hm3 = hit_map(3), now we want to prove that if l in dom(hm3), then there is some x > l st ES(x) = 14. Suppose that's not the case, that implies that the execution sequence must be

ES = (... 3 4 [5 ... 13] 3 4 [5 ... 13] ...)

Because none of ES({5, ..., 13}) modify num_sorted_elements, then we can prove that l in dom(hm3), va(num_sorted_elements, hm3(l)) = l.

Note that |dom(va(a, l))| is constant, because they are constructed via componentwise equality from the original, let this contant value be C.

Therefore we can pick some l > C, and then we will go to line 14, which is a contradiction, so the outer while loop must terminate, therefore bubble will terminate.

----

Now we will prove that bubble sorts the input list, we want to prove that va(l, |dom(ES)| - 1) is an increasing function. We can prove that for any x, x+1 that l(x) <= l(x + 1).

We will do this by proving that fa l in dom(hm3), increasing(restrict(va(a, hm3(l)), {|dom(ES)| - 1 - l, ..., |dom(ES)| - 1})).



*/



build :: () {
    w := compiler_create_workspace("Target");
    
    options := get_build_options(w);
    options.output_type = .NO_OUTPUT;
    set_build_options(options, w);
    
    compiler_begin_intercept(w);
    
    add_build_string(#string DONE
        sum_of_1_to_n :: (n : int) -> int {
            sum := 0;
            i := 1;
            while i <= n {
                sum += i;
                i += 1;
            }
            return sum;
        }
        
        main :: () {}
    DONE, w);
    
    while true {
        message := compiler_wait_for_message();
        if !message break;
        
        if message.kind == {
            case .TYPECHECKED;
                tc := cast(*Message_Typechecked) message;
                
                for tc.procedure_bodies {
                    body := it.expression;
                    if body.header && body.header.name == "sum_of_1_to_n" {
                        facts := generate_procedure_facts(body);
                        print_procedure_assumptions(body, facts.assumptions);
                        create_initial_sum_termination_proof(facts);
                        // test_triangular_number_induction();
                        // test_finite_range_induction();
                        // test_finite_set_forall_with_successors();
                    }
                }
                
            case .COMPLETE;
                break;
        }
    }
    
    compiler_end_intercept(w);
}

#run build();
