#import "Basic";
#import "tbx/proof";

Triangular_Arithmetic_Facts :: struct {
    base_one: *Formula;
    mul_successor_expansion: *Formula;
    successor_as_half_twice: *Formula;
    add_halves: *Formula;
    distribute_two_successor: *Formula;
    collect_triangular_numerator: *Formula;
    successor_successor_as_plus_two: *Formula;
}

Finite_Set_Order_Facts :: struct {
    zero_lt_one: *Formula;
    succ_lt_0_to_1: *Formula;
    succ_lt_1_to_2: *Formula;
    succ_lt_2_to_3: *Formula;
    trans_1_2_3: *Formula;
    trans_1_3_4: *Formula;
    trans_2_3_4: *Formula;
}

arith_lt :: (a: *Term, b: *Term) -> *Formula {
    return make_rel("<", a, b);
}

arith_sum :: (t: *Term) -> *Term {
    return make_function("sum", t);
}

arith_add :: (a: *Term, b: *Term) -> *Term {
    return make_function("+", a, b);
}

arith_mul :: (a: *Term, b: *Term) -> *Term {
    return make_function("*", a, b);
}

arith_div :: (a: *Term, b: *Term) -> *Term {
    return make_function("/", a, b);
}

arith_succ :: (t: *Term) -> *Term {
    return make_function("succ", t);
}

arith_triangular_rhs :: (t: *Term) -> *Term {
    one := make_constant("1");
    two := make_constant("2");
    return arith_div(arith_mul(t, arith_add(t, one)), two);
}

make_triangular_arithmetic_facts :: (domain: *Term) -> Triangular_Arithmetic_Facts {
    facts: Triangular_Arithmetic_Facts;

    one := make_constant("1");
    two := make_constant("2");
    k := make_variable("k");
    k_plus_one := arith_add(k, one);
    k_plus_two := arith_add(k, two);
    k_squared := arith_mul(k, k);
    k_squared_plus_k := arith_add(k_squared, k);
    twice_k_plus_one := arith_mul(two, k_plus_one);
    twice_k_plus_two := arith_add(arith_mul(two, k), two);

    facts.base_one = make_eq(one, arith_triangular_rhs(one));

    facts.mul_successor_expansion = make_forall(
        "k",
        domain,
        make_eq(arith_mul(k, k_plus_one), k_squared_plus_k)
    );

    facts.successor_as_half_twice = make_forall(
        "k",
        domain,
        make_eq(k_plus_one, arith_div(twice_k_plus_one, two))
    );

    facts.add_halves = make_forall(
        "k",
        domain,
        make_eq(
            arith_add(arith_div(k_squared_plus_k, two), arith_div(twice_k_plus_one, two)),
            arith_div(arith_add(k_squared_plus_k, twice_k_plus_one), two)
        )
    );

    facts.distribute_two_successor = make_forall(
        "k",
        domain,
        make_eq(twice_k_plus_one, twice_k_plus_two)
    );

    facts.collect_triangular_numerator = make_forall(
        "k",
        domain,
        make_eq(
            arith_add(k_squared_plus_k, twice_k_plus_two),
            arith_mul(k_plus_one, k_plus_two)
        )
    );

    facts.successor_successor_as_plus_two = make_forall(
        "k",
        domain,
        make_eq(arith_add(k_plus_one, one), k_plus_two)
    );

    return facts;
}

add_triangular_arithmetic_facts :: (assumptions: *[..]*Formula, facts: Triangular_Arithmetic_Facts) {
    array_add(assumptions, facts.base_one);
    array_add(assumptions, facts.mul_successor_expansion);
    array_add(assumptions, facts.successor_as_half_twice);
    array_add(assumptions, facts.add_halves);
    array_add(assumptions, facts.distribute_two_successor);
    array_add(assumptions, facts.collect_triangular_numerator);
    array_add(assumptions, facts.successor_successor_as_plus_two);
}

make_finite_set_order_facts :: () -> Finite_Set_Order_Facts {
    facts: Finite_Set_Order_Facts;

    zero := make_constant("0");
    one := make_constant("1");
    two := make_constant("2");
    three := make_constant("3");
    four := make_constant("4");

    facts.zero_lt_one = arith_lt(zero, one);
    facts.succ_lt_0_to_1 = make_implies(arith_lt(zero, one), arith_lt(one, two));
    facts.succ_lt_1_to_2 = make_implies(arith_lt(one, two), arith_lt(two, three));
    facts.succ_lt_2_to_3 = make_implies(arith_lt(two, three), arith_lt(three, four));

    facts.trans_1_2_3 = make_implies(make_and(arith_lt(one, two), arith_lt(two, three)), arith_lt(one, three));
    facts.trans_1_3_4 = make_implies(make_and(arith_lt(one, three), arith_lt(three, four)), arith_lt(one, four));
    facts.trans_2_3_4 = make_implies(make_and(arith_lt(two, three), arith_lt(three, four)), arith_lt(two, four));

    return facts;
}

add_finite_set_order_facts :: (assumptions: *[..]*Formula, facts: Finite_Set_Order_Facts) {
    array_add(assumptions, facts.zero_lt_one);
    array_add(assumptions, facts.succ_lt_0_to_1);
    array_add(assumptions, facts.succ_lt_1_to_2);
    array_add(assumptions, facts.succ_lt_2_to_3);
    array_add(assumptions, facts.trans_1_2_3);
    array_add(assumptions, facts.trans_1_3_4);
    array_add(assumptions, facts.trans_2_3_4);
}
