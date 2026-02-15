#import "tbx/proof";

// the domain is created using make constant.
make_transitivity_formula :: (domain: *Term) -> *Formula {
    a := make_variable("a_");
    b := make_variable("b_");
    c := make_variable("c_");

    a_eq_b := make_eq(a, b);
    b_eq_c := make_eq(b, c);
    a_eq_c := make_eq(a, c);
    a_eq_b_and_b_eq_c := make_and(a_eq_b, b_eq_c);
    a_eq_b_and_b_eq_c_implies_a_eq_c := make_implies(a_eq_b_and_b_eq_c, a_eq_c);
    
    forall_c := make_forall("c_", domain, a_eq_b_and_b_eq_c_implies_a_eq_c);
    forall_b := make_forall("b_", domain, forall_c);
    forall_a := make_forall("a_", domain, forall_b);
    transitivity := forall_a;

    return transitivity;
}

make_symmetry_formula :: (domain: *Term) -> *Formula {
    a := make_variable("a_");
    b := make_variable("b_");

    innermost := make_implies(make_eq(a, b), make_eq(b, a));
    inner := make_forall("b_", domain, innermost);
    symmetry := make_forall("a_", domain, inner);
    
    return symmetry;
}
