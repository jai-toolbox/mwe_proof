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
            
            if arg_type && arg_type.type == .POINTER {
                ptr_info := cast(*Type_Info_Pointer) arg_type;
                pointed_type := ptr_info.pointer_to;
                
                type_set := get_type_set(pointed_type);
                if type_set != "?" {
                    fact: TypeFact;
                    fact.expr = tprint("%.*", arg.name);
                    fact.type_set = type_set;
                    array_add(*type_facts, fact);
                }
            } else if arg_type {
                // non-pointer argument
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

build :: () {
    w := compiler_create_workspace("Target");
    
    options := get_build_options(w);
    options.output_type = .NO_OUTPUT;
    set_build_options(options, w);
    
    compiler_begin_intercept(w);
    
    add_build_string(#string DONE
        swap :: (x: *int, y: *int) {
            temp := y.*;
            y.* = x.*;
            x.* = temp;
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
                    if body.header && body.header.name == "swap" {
                        type_facts := generate_type_facts(body);
                        value_facts := generate_facts(body);
                        
                        create_proof_from_extracted_facts(type_facts, value_facts);
                    }
                }
                
            case .COMPLETE;
                break;
        }
    }
    
    compiler_end_intercept(w);
}

#run build();
