#import "Basic";
#import "Hash_Table";
#import "knowledge";

#import "tbx/proof";
#import "tbx/graph";

Edge_Key :: struct {
    from: int;
    to: int;
}

// for hash_table, need to define hash and comparison
edge_key_hash :: (key: Edge_Key) -> u32 {
    //  hash combining both integers where we XOR the two values with some bit mixing
    h1 := cast(u32)(key.from * 31);
    h2 := cast(u32)(key.to);
    return h1 ^ h2;
}

edge_key_equal :: (a: Edge_Key, b: Edge_Key) -> bool {
    return a.from == b.from && a.to == b.to;
}

Equality_Graph :: struct {

    graph: Graph;
    
    // term <-> node mappings
    term_to_node: Table(string, int);
    node_to_term: [..] *Term;
    
    // edge metadata: maps (from, to) -> proof_line
    // we store both directions since equality is symmetric
    edge_proof_lines: Table(Edge_Key, int, edge_key_hash, edge_key_equal);
}

make_equality_graph :: () -> Equality_Graph {
    log("make_equality_graph: creating new graph");
    g: Equality_Graph;
    g.graph = make_graph(0);  // will grow dynamically starting with zero for now
    return g;
}

get_or_create_node :: (g: *Equality_Graph, t: *Term) -> int {
    key := term_to_string(t);
    log("get_or_create_node: looking for term '%'", key);
    
    existing := table_find_pointer(*g.term_to_node, key);
    if existing {
        log("get_or_create_node: found existing node % for '%'", <<existing, key);
        return <<existing;
    }
    
    idx := g.graph.node_count;
    
    // add to term mappings
    table_add(*g.term_to_node, key, idx);
    array_add(*g.node_to_term, copy_term(t));
    
    empty: [..] int;
    array_add(*g.graph.adjacency, empty);
    g.graph.node_count += 1;
    
    log("get_or_create_node: created new node % for '%'", idx, key);
    return idx;
}

add_equality_edge :: (g: *Equality_Graph, t1: *Term, t2: *Term, proof_line: int) {
    log("add_equality_edge: adding edge between '%' and '%' from proof line %", 
        term_to_string(t1), term_to_string(t2), proof_line);
    
    n1 := get_or_create_node(g, t1);
    n2 := get_or_create_node(g, t2);
    
    // add bidirectional edges to underlying graph 
    add_edge(*g.graph, n1, n2);
    add_edge(*g.graph, n2, n1);
    
    // store edge metadata (both directions for lookup convenience)
    key1 := Edge_Key.{from = n1, to = n2};
    key2 := Edge_Key.{from = n2, to = n1};
    table_add(*g.edge_proof_lines, key1, proof_line);
    table_add(*g.edge_proof_lines, key2, proof_line);
    
    log("add_equality_edge: added bidirectional edge between nodes % and %", n1, n2);
}

// get the proof line for an edge between two nodes
get_edge_proof_line :: (g: *Equality_Graph, from: int, to: int) -> int {
    key := Edge_Key.{from = from, to = to};
    ptr := table_find_pointer(*g.edge_proof_lines, key);
    if ptr return <<ptr;
    return -1;  // Not found
}


// returns array of proof line indices along the path
find_equality_path :: (g: *Equality_Graph, start_term: *Term, end_term: *Term) -> [..] int {
    result: [..] int;
    
    start_key := term_to_string(start_term);
    end_key := term_to_string(end_term);
    
    log("find_equality_path: searching for path from '%' to '%'", start_key, end_key);
    
    start_node_ptr := table_find_pointer(*g.term_to_node, start_key);
    end_node_ptr := table_find_pointer(*g.term_to_node, end_key);
    
    if !start_node_ptr || !end_node_ptr {
        log("find_equality_path: one or both terms not found in graph");
        return result;
    }
    
    start_node := <<start_node_ptr;
    end_node := <<end_node_ptr;
    
    log("find_equality_path: start_node = %, end_node = %", start_node, end_node);
    
    if start_node == end_node {
        log("find_equality_path: same node, returning empty path");
        return result;
    }
    
    // use external bfs to find node path
    node_path := bfs_find_path(*g.graph, start_node, end_node);
    defer array_free(node_path);
    
    if node_path.count < 2 {
        log("find_equality_path: no path found");
        return result;
    }
    
    log("find_equality_path: found node path with % nodes", node_path.count);
    
    // convert node path to proof line path
    for i: 0..node_path.count-2 {
        from_node := node_path[i] ;
        to_node := node_path[i + 1] ;
        proof_line := get_edge_proof_line(g, from_node, to_node);
        
        log("find_equality_path: edge % -> % has proof line %", from_node, to_node, proof_line);
        array_add(*result, proof_line);
    }
    
    log("find_equality_path: returning path with % edges", result.count);
    return result;
}


build_equality_graph_from_proof :: (proof: *Proof) -> Equality_Graph {
    log("build_equality_graph_from_proof: starting");
    
    g := make_equality_graph();
    
    for line, idx: proof.lines {
        f := line.statement;
        if f.kind == .EQUALITY {
            add_equality_edge(*g, f.equality.l, f.equality.r, idx);
        }
    }
    
    // scan assumptions (encoded as negative indices)
    for assumption, idx: proof.assumptions {
        if assumption.kind == .EQUALITY {
            add_equality_edge(*g, assumption.equality.l, assumption.equality.r, -(idx + 1));
        }
    }
    
    log("build_equality_graph_from_proof: finished, graph has % nodes", g.graph.node_count);
    return g;
}


find_line_with_formula :: (proof: *Proof, f: *Formula) -> int {
    target_str := formula_to_string(f);
    log("find_line_with_formula: looking for '%'", target_str);
    for line, i: proof.lines {
        if formula_to_string(line.statement) == target_str {
            log("find_line_with_formula: found at line %", i);
            return i;
        }
    }
    log("find_line_with_formula: not found");
    return -1;
}

ensure_assumption_as_line :: (proof: *Proof, assumption_idx: int) -> int {
    log("ensure_assumption_as_line: ensuring assumption % is a proof line", assumption_idx);
    assumption := proof.assumptions[assumption_idx] ;
    
    existing := find_line_with_formula(proof, assumption);
    if existing >= 0 {
        log("ensure_assumption_as_line: already exists at line %", existing);
        return existing;
    }
    
    add_line_to_proof(proof, assumption, "ASSUMPTION");
    log("ensure_assumption_as_line: added as new line %", proof.lines.count - 1);
    return proof.lines.count - 1;
}


try_prove_equality :: (proof: *Proof, var1: *Term, var2: *Term, domain: *Term) -> bool {
    log("try_prove_equality: attempting to prove '%' = '%'", term_to_string(var1), term_to_string(var2));
    
    // first check if they're syntactically equal (reflexivity)
    if term_to_string(var1) == term_to_string(var2) {
        log("try_prove_equality: terms are syntactically equal, using reflexivity");
        eq_formula := make_eq(var1, var2);
        add_line_to_proof(proof, eq_formula, "EQ");
        return true;
    }
    
    log("try_prove_equality: building equality graph");
    g := build_equality_graph_from_proof(proof);
    
    log("try_prove_equality: graph node count = %", g.graph.node_count);
    
    log("try_prove_equality: finding path via BFS");
    path := find_equality_path(*g, var1, var2);
    
    log("try_prove_equality: path.count = %", path.count);
    
    if path.count == 0 {
        log("try_prove_equality: path is empty, checking if same node");
        start_key := term_to_string(var1);
        end_key := term_to_string(var2);
        start_ptr := table_find_pointer(*g.term_to_node, start_key);
        end_ptr := table_find_pointer(*g.term_to_node, end_key);
        
        log("try_prove_equality: start_ptr = %, end_ptr = %", start_ptr != null, end_ptr != null);
        
        if start_ptr && end_ptr && <<start_ptr == <<end_ptr {
            log("try_prove_equality: same node, using reflexivity");
            eq_formula := make_eq(var1, var2);
            add_line_to_proof(proof, eq_formula, "EQ");
            return true;
        }
        
        log("try_prove_equality: cannot prove equality - no path found");
        print("Cannot prove equality: no path found\n");
        return false;
    }
    
    log("try_prove_equality: found path with % edges", path.count);
    
    // first, ensure all assumptions in the path are added as proof lines
    assumption_line_map: Table(int, int);
    
    log("try_prove_equality: processing path edges to ensure assumptions are proof lines");
    for line_idx: path {
        log("try_prove_equality: processing edge from line/assumption %", line_idx);
        if line_idx < 0 {
            assumption_idx := -(line_idx + 1);
            log("try_prove_equality: this is assumption index %", assumption_idx);
            assumption := proof.assumptions[assumption_idx] ;
            
            found_line := -1;
            for existing, i: proof.lines {
                if formula_to_string(existing.statement) == formula_to_string(assumption) {
                    found_line = i;
                    break;
                }
            }
            
            if found_line == -1 {
                log("try_prove_equality: adding assumption as proof line");
                add_line_to_proof(proof, assumption, "ASSUMPTION");
                found_line = proof.lines.count - 1;
            } else {
                log("try_prove_equality: assumption already at line %", found_line);
            }
            
            table_add(*assumption_line_map, line_idx, found_line);
            log("try_prove_equality: mapped % -> %", line_idx, found_line);
        }
    }
    
    get_actual_line :: (line_idx: int, assumption_map: *Table(int, int)) -> int {
        if line_idx < 0 {
            ptr := table_find_pointer(assumption_map, line_idx);
            if ptr return <<ptr;
            return -1;
        }
        return line_idx;
    }
    
    // if path has only one edge
    if path.count == 1 {
        log("try_prove_equality: single edge path");
        actual_line := get_actual_line(path[0] , *assumption_line_map);
        log("try_prove_equality: actual line = %", actual_line);
        eq_stmt := proof.lines[actual_line] .statement;
        
        log("try_prove_equality: equality is '%' = '%'", 
            term_to_string(eq_stmt.equality.l), term_to_string(eq_stmt.equality.r));
        
        if term_to_string(eq_stmt.equality.l) == term_to_string(var1) &&
           term_to_string(eq_stmt.equality.r) == term_to_string(var2) {
            log("try_prove_equality: already in correct form");
            return true;
        } else if term_to_string(eq_stmt.equality.r) == term_to_string(var1) &&
                  term_to_string(eq_stmt.equality.l) == term_to_string(var2) {
            log("try_prove_equality: need to apply symmetry");
            new_line := apply_symmetry_via_axiom(proof, actual_line, domain);
            if new_line < 0 return false;
            return true;
        }
        log("try_prove_equality: single edge case completed");
        return true;
    }
    
    log("try_prove_equality: multi-edge path, need to chain transitivity");
    
    // build term sequence
    terms_in_path: [..] *Term;
    array_add(*terms_in_path, copy_term(var1));
    
    current_term := var1;
    log("try_prove_equality: building term sequence, starting with '%'", term_to_string(current_term));
    
    for line_idx, i: path {
        actual_line := get_actual_line(line_idx, *assumption_line_map);
        eq_stmt := proof.lines[actual_line] .statement;
        
        log("try_prove_equality: path step %: line %, equality '%' = '%'", 
            i, actual_line, term_to_string(eq_stmt.equality.l), term_to_string(eq_stmt.equality.r));
        
        if term_to_string(eq_stmt.equality.l) == term_to_string(current_term) {
            current_term = eq_stmt.equality.r;
            log("try_prove_equality: moving to right side: '%'", term_to_string(current_term));
        } else {
            current_term = eq_stmt.equality.l;
            log("try_prove_equality: moving to left side: '%'", term_to_string(current_term));
        }
        array_add(*terms_in_path, copy_term(current_term));
    }
    
    log("try_prove_equality: term sequence has % terms", terms_in_path.count);
    for t, i: terms_in_path {
        log("try_prove_equality: terms_in_path[%] = '%'", i, term_to_string(t));
    }
    
    // start with first equality
    current_eq_line := get_actual_line(path[0] , *assumption_line_map);
    log("try_prove_equality: starting with line %", current_eq_line);
    
    // orient first equality
    first_eq := proof.lines[current_eq_line] .statement;
    if term_to_string(first_eq.equality.l) != term_to_string(terms_in_path[0] ) {
        log("try_prove_equality: first equality needs flipping");
        current_eq_line = apply_symmetry_via_axiom(proof, current_eq_line, domain);
        if current_eq_line < 0 {
            log("try_prove_equality: failed to apply symmetry");
            return false;
        }
        log("try_prove_equality: flipped equality is now line %", current_eq_line);
    }
    
    // chain transitivity
    log("try_prove_equality: chaining transitivity for % remaining edges", path.count - 1);
    for i: 1..path.count-1 {
        log("try_prove_equality: transitivity step %", i);
        next_line := get_actual_line(path[i] , *assumption_line_map);
        next_eq := proof.lines[next_line] .statement;
        
        middle_term := terms_in_path[i] ;
        log("try_prove_equality: middle term is '%'", term_to_string(middle_term));
        
        oriented_next_line := next_line;
        if term_to_string(next_eq.equality.l) != term_to_string(middle_term) {
            log("try_prove_equality: next equality needs flipping");
            oriented_next_line = apply_symmetry_via_axiom(proof, next_line, domain);
            if oriented_next_line < 0 {
                log("try_prove_equality: failed to apply symmetry");
                return false;
            }
            log("try_prove_equality: flipped equality is now line %", oriented_next_line);
        }
        
        log("try_prove_equality: applying transitivity to get '%' = '%'", 
            term_to_string(terms_in_path[0] ), term_to_string(terms_in_path[i + 1] ));
        
        current_eq_line = apply_transitivity_via_axiom(proof, current_eq_line, oriented_next_line, domain);
        if current_eq_line < 0 {
            log("try_prove_equality: failed to apply transitivity");
            return false;
        }
        log("try_prove_equality: result is line %", current_eq_line);
    }
    
    // clean up
    log("try_prove_equality: cleaning up");
    for t: terms_in_path {
        free_term(t);
    }
    array_free(terms_in_path);
    
    log("try_prove_equality: success!");
    return true;
}

// given line with a = b, derive b = a all at once.
apply_symmetry_via_axiom :: (proof: *Proof, eq_line: int, domain: *Term) -> int {
    log("apply_symmetry_via_axiom: flipping equality at line %", eq_line);
    
    eq_formula := proof.lines[eq_line] .statement;
    if eq_formula.kind != .EQUALITY {
        log("apply_symmetry_via_axiom: line is not an equality");
        return -1;
    }
    
    a := eq_formula.equality.l;
    b := eq_formula.equality.r;
    
    log("apply_symmetry_via_axiom: have '%' = '%', want '%' = '%'", 
        term_to_string(a), term_to_string(b), term_to_string(b), term_to_string(a));
    
    symmetry_assumption_idx := find_symmetry_assumption(proof, domain);
    if symmetry_assumption_idx < 0 {
        log("apply_symmetry_via_axiom: no symmetry assumption found");
        return -1;
    }
    log("apply_symmetry_via_axiom: found symmetry axiom at assumption %", symmetry_assumption_idx);
    
    // ensure symmetry axiom is a proof line
    sym_line := ensure_assumption_as_line(proof, symmetry_assumption_idx);
    log("apply_symmetry_via_axiom: symmetry axiom is proof line %", sym_line);
    
    // ensure membership facts: a in domain, b in domain
    a_mem_line := ensure_membership_line(proof, a, domain);
    b_mem_line := ensure_membership_line(proof, b, domain);
    
    if a_mem_line < 0 || b_mem_line < 0 {
        log("apply_symmetry_via_axiom: cannot find membership facts");
        return -1;
    }
    log("apply_symmetry_via_axiom: membership lines: a->%, b->%", a_mem_line, b_mem_line);
    
    // apply GENERALIZED_FORALL to get: (a = b) → (b = a)
    implication := make_implies(make_eq(a, b), make_eq(b, a));
    log("apply_symmetry_via_axiom: deriving implication '%'", formula_to_string(implication));
    add_line_to_proof(proof, implication, "GENERALIZED_FORALL", sym_line, a_mem_line, b_mem_line);
    impl_line := proof.lines.count - 1;
    log("apply_symmetry_via_axiom: implication is line %", impl_line);
    
    // apply IMPLIES to get: b = a
    target := make_eq(b, a);
    log("apply_symmetry_via_axiom: applying modus ponens to get '%'", formula_to_string(target));
    add_line_to_proof(proof, target, "IMPLIES", impl_line, eq_line);
    result_line := proof.lines.count - 1;
    log("apply_symmetry_via_axiom: result is line %", result_line);
    
    return result_line;
}

// given line1 with a = b and line2 with b = c, derive a = c, all at once
apply_transitivity_via_axiom :: (proof: *Proof, eq1_line: int, eq2_line: int, domain: *Term) -> int {
    log("apply_transitivity_via_axiom: chaining lines % and %", eq1_line, eq2_line);
    
    eq1 := proof.lines[eq1_line] .statement;
    eq2 := proof.lines[eq2_line] .statement;
    
    if eq1.kind != .EQUALITY || eq2.kind != .EQUALITY {
        log("apply_transitivity_via_axiom: inputs must be equalities");
        return -1;
    }
    
    a := eq1.equality.l;
    b := eq1.equality.r;
    c := eq2.equality.r;
    
    log("apply_transitivity_via_axiom: have '%' = '%' and '%' = '%'",
        term_to_string(a), term_to_string(b), 
        term_to_string(eq2.equality.l), term_to_string(c));
    
    // verify middle term matches
    if term_to_string(eq2.equality.l) != term_to_string(b) {
        log("apply_transitivity_via_axiom: middle terms don't match: '%' vs '%'",
            term_to_string(b), term_to_string(eq2.equality.l));
        return -1;
    }
    
    // find transitivity axiom
    trans_assumption_idx := find_transitivity_assumption(proof, domain);
    if trans_assumption_idx < 0 {
        log("apply_transitivity_via_axiom: no transitivity assumption found");
        return -1;
    }
    log("apply_transitivity_via_axiom: found transitivity axiom at assumption %", trans_assumption_idx);
    
    trans_line := ensure_assumption_as_line(proof, trans_assumption_idx);
    log("apply_transitivity_via_axiom: transitivity axiom is proof line %", trans_line);
    
    // ensure membership facts
    a_mem_line := ensure_membership_line(proof, a, domain);
    b_mem_line := ensure_membership_line(proof, b, domain);
    c_mem_line := ensure_membership_line(proof, c, domain);
    
    if a_mem_line < 0 || b_mem_line < 0 || c_mem_line < 0 {
        log("apply_transitivity_via_axiom: cannot find all membership facts");
        log("apply_transitivity_via_axiom: a_mem=%, b_mem=%, c_mem=%", a_mem_line, b_mem_line, c_mem_line);
        return -1;
    }
    log("apply_transitivity_via_axiom: membership lines: a->%, b->%, c->%", a_mem_line, b_mem_line, c_mem_line);
    
    // apply GENERALIZED_FORALL to get: ((a = b) ∧ (b = c)) → (a = c)
    antecedent := make_and(make_eq(a, b), make_eq(b, c));
    target := make_eq(a, c);
    implication := make_implies(antecedent, target);
    log("apply_transitivity_via_axiom: deriving implication '%'", formula_to_string(implication));
    add_line_to_proof(proof, implication, "GENERALIZED_FORALL", trans_line, a_mem_line, b_mem_line, c_mem_line);
    impl_line := proof.lines.count - 1;
    log("apply_transitivity_via_axiom: implication is line %", impl_line);
    
    // build (a = b) and (b = c)
    log("apply_transitivity_via_axiom: building conjunction");
    add_line_to_proof(proof, antecedent, "AND", eq1_line, eq2_line);
    and_line := proof.lines.count - 1;
    log("apply_transitivity_via_axiom: conjunction is line %", and_line);
    
    // apply IMPLIES to get the result
    log("apply_transitivity_via_axiom: applying modus ponens to get '%'", formula_to_string(target));
    add_line_to_proof(proof, target, "IMPLIES", impl_line, and_line);
    result_line := proof.lines.count - 1;
    log("apply_transitivity_via_axiom: result is line %", result_line);
    
    return result_line;
}


find_symmetry_assumption :: (proof: *Proof, domain: *Term) -> int {
    log("find_symmetry_assumption: looking for symmetry axiom over domain '%'", term_to_string(domain));
    
    // forall x in D, forall y in D (x = y) implies (y = x)
    for assumption, i: proof.assumptions {
        if assumption.kind == .FORALL {
            // Check if this looks like symmetry
            if assumption.forall.inner.kind == .FORALL {
                inner := assumption.forall.inner;
                if inner.forall.inner.kind == .IMPLIES {
                    impl := inner.forall.inner;
                    if impl.implies.l.kind == .EQUALITY && impl.implies.r.kind == .EQUALITY {
                        // This looks like symmetry
                        log("find_symmetry_assumption: found candidate at %: %", i, formula_to_string(assumption));
                        return i;
                    }
                }
            }
        }
    }
    
    log("find_symmetry_assumption: not found");
    return -1;
}

find_transitivity_assumption :: (proof: *Proof, domain: *Term) -> int {
    log("find_transitivity_assumption: looking for transitivity axiom over domain '%'", term_to_string(domain));
    
    // forall x, y, z in D, ((x = y) and (y = z)) implies (x = z)
    for assumption, i: proof.assumptions {
        if assumption.kind == .FORALL {
            if assumption.forall.inner.kind == .FORALL {
                inner1 := assumption.forall.inner;
                if inner1.forall.inner.kind == .FORALL {
                    inner2 := inner1.forall.inner;
                    if inner2.forall.inner.kind == .IMPLIES {
                        impl := inner2.forall.inner;
                        if impl.implies.l.kind == .AND {
                            // this looks like transitivity
                            log("find_transitivity_assumption: found candidate at %: %", i, formula_to_string(assumption));
                            return i;
                        }
                    }
                }
            }
        }
    }
    
    log("find_transitivity_assumption: not found");
    return -1;
}


ensure_membership_line :: (proof: *Proof, term: *Term, domain: *Term) -> int {
    membership := make_rel(SYM_IN, term, domain);
    log("ensure_membership_line: looking for '%'", formula_to_string(membership));
    
    for line, i: proof.lines {
        if formula_to_string(line.statement) == formula_to_string(membership) {
            log("ensure_membership_line: found at proof line %", i);
            return i;
        }
    }
    
    for assumption, i: proof.assumptions {
        if formula_to_string(assumption) == formula_to_string(membership) {
            log("ensure_membership_line: found at assumption %, adding as proof line", i);
            add_line_to_proof(proof, assumption, "ASSUMPTION");
            return proof.lines.count - 1;
        }
    }
    
    log("ensure_membership_line: not found");
    return -1;
}


test_equality_graph :: () {
    print("=== Equality Graph Test ===\n");
    log("test_equality_graph: starting test");
    
    Z := make_constant("Z");
    
    a := make_variable("a");
    b := make_variable("b");
    c := make_variable("c");
    d := make_variable("d");
    
    log("test_equality_graph: created variables a, b, c, d");
    
    assumptions: [..] *Formula;
    
    array_add(*assumptions, make_symmetry_formula(Z));
    array_add(*assumptions, make_transitivity_formula(Z));
    
    array_add(*assumptions, make_rel(SYM_IN, a, Z));
    array_add(*assumptions, make_rel(SYM_IN, b, Z));
    array_add(*assumptions, make_rel(SYM_IN, c, Z));
    array_add(*assumptions, make_rel(SYM_IN, d, Z));
    
    array_add(*assumptions, make_eq(a, b));
    array_add(*assumptions, make_eq(b, c));
    array_add(*assumptions, make_eq(c, d));
    
    log("test_equality_graph: added % assumptions", assumptions.count);
    for assumption, i: assumptions {
        log("test_equality_graph: assumption[%] = %", i, formula_to_string(assumption));
    }
    
    target := make_eq(a, d);
    log("test_equality_graph: target = %", formula_to_string(target));
    
    proof := create_proof(assumptions, target);
    log("test_equality_graph: created proof");
    
    print("Initial proof state:\n");
    print_proof(*proof);
    
    log("test_equality_graph: calling try_prove_equality");
    success := try_prove_equality(*proof, a, d, Z);
    
    print("\nAfter try_prove_equality:\n");
    print_proof(*proof);
    
    if success {
        print("Successfully proved % = %\n", term_to_string(a), term_to_string(d));
    } else {
        print("Failed to prove equality\n");
    }
    
    if is_valid(*proof) {
        print("Proof is complete!\n");
    }
}

test_equality_graph_complex :: () {
    log("test_equality_graph_complex: starting test");
    
    Z := make_constant("Z");
    
    a := make_variable("a");
    b := make_variable("b");
    c := make_variable("c");
    d := make_variable("d");
    e := make_variable("e");
    f := make_variable("f");
    g := make_variable("g");
    h := make_variable("h");
    i := make_variable("i");
    j := make_variable("j");
    k := make_variable("k");
    
    /*
        
              b --- e --- h
             /       \
        a --+         +-- j --- k
             \       /
              c --- f --- i
             /
            d --- g
        
        So we have:
        - a = b, a = c
        - b = e
        - c = f, c = d
        - d = g
        - e = h, e = j
        - f = i, f = j
        - j = k
        
        Target: prove a = k (requires path a -> b -> e -> j -> k or a -> c -> f -> j -> k)
        Also: prove g = k (requires longer path g -> d -> c -> f -> j -> k or g -> d -> c -> a -> b -> e -> j -> k)
    */
    
    assumptions: [..] *Formula;
    
    array_add(*assumptions, make_symmetry_formula(Z));
    array_add(*assumptions, make_transitivity_formula(Z));
    
    array_add(*assumptions, make_rel(SYM_IN, a, Z));
    array_add(*assumptions, make_rel(SYM_IN, b, Z));
    array_add(*assumptions, make_rel(SYM_IN, c, Z));
    array_add(*assumptions, make_rel(SYM_IN, d, Z));
    array_add(*assumptions, make_rel(SYM_IN, e, Z));
    array_add(*assumptions, make_rel(SYM_IN, f, Z));
    array_add(*assumptions, make_rel(SYM_IN, g, Z));
    array_add(*assumptions, make_rel(SYM_IN, h, Z));
    array_add(*assumptions, make_rel(SYM_IN, i, Z));
    array_add(*assumptions, make_rel(SYM_IN, j, Z));
    array_add(*assumptions, make_rel(SYM_IN, k, Z));
    
    array_add(*assumptions, make_eq(a, b));
    array_add(*assumptions, make_eq(a, c));
    array_add(*assumptions, make_eq(b, e));
    array_add(*assumptions, make_eq(c, f));
    array_add(*assumptions, make_eq(c, d));
    array_add(*assumptions, make_eq(d, g));
    array_add(*assumptions, make_eq(e, h));
    array_add(*assumptions, make_eq(e, j));
    array_add(*assumptions, make_eq(f, i));
    array_add(*assumptions, make_eq(f, j));
    array_add(*assumptions, make_eq(j, k));
    
    log("test_equality_graph_complex: added % assumptions", assumptions.count);
    
    print("\n--- Test 1: Prove a = k ---\n");
    target1 := make_eq(a, k);
    
    proof1 := create_proof(assumptions, target1);
    print("Initial proof state:\n");
    print_proof(*proof1);
    
    success1 := try_prove_equality(*proof1, a, k, Z);
    
    print("\nAfter try_prove_equality:\n");
    print_proof(*proof1);
    
    if success1 && is_valid(*proof1) {
        print("SUCCESS: Proved a = k\n");
    } else {
        print("FAILED: Could not prove a = k\n");
    }
    
    print("\n--- Test 2: Prove g = k ---\n");
    target2 := make_eq(g, k);
    
    proof2 := create_proof(assumptions, target2);
    print("Initial proof state:\n");
    print_proof(*proof2);
    
    success2 := try_prove_equality(*proof2, g, k, Z);
    
    print("\nAfter try_prove_equality:\n");
    print_proof(*proof2);
    
    if success2 && is_valid(*proof2) {
        print("SUCCESS: Proved g = k\n");
    } else {
        print("FAILED: Could not prove g = k\n");
    }
    
    print("\n--- Test 3: Prove h = i ---\n");
    target3 := make_eq(h, i);
    
    proof3 := create_proof(assumptions, target3);
    print("Initial proof state:\n");
    print_proof(*proof3);
    
    success3 := try_prove_equality(*proof3, h, i, Z);
    
    print("\nAfter try_prove_equality:\n");
    print_proof(*proof3);
    
    if success3 && is_valid(*proof3) {
        print("SUCCESS: Proved h = i\n");
    } else {
        print("FAILED: Could not prove h = i\n");
    }
    
    print("\n--- Test 4: Prove g = h ---\n");
    target4 := make_eq(g, h);
    
    proof4 := create_proof(assumptions, target4);
    print("Initial proof state:\n");
    print_proof(*proof4);
    
    success4 := try_prove_equality(*proof4, g, h, Z);
    
    print("\nAfter try_prove_equality:\n");
    print_proof(*proof4);
    
    if success4 && is_valid(*proof4) {
        print("SUCCESS: Proved g = h\n");
    } else {
        print("FAILED: Could not prove g = h\n");
    }
    
    print("\n--- Test 5: Prove a = z (should fail - z not in graph) ---\n");
    z := make_variable("z");
    target5 := make_eq(a, z);
    
    proof5 := create_proof(assumptions, target5);
    
    success5 := try_prove_equality(*proof5, a, z, Z);
    
    if !success5 {
        print("SUCCESS: Correctly failed to prove a = z (z not connected)\n");
    } else {
        print("FAILED: Should not have been able to prove a = z\n");
    }
    
    print("\n--- Test 6: Prove a = a (reflexivity) ---\n");
    target6 := make_eq(a, a);
    
    proof6 := create_proof(assumptions, target6);
    
    success6 := try_prove_equality(*proof6, a, a, Z);
    
    print("\nAfter try_prove_equality:\n");
    print_proof(*proof6);
    
    if success6 && is_valid(*proof6) {
        print("SUCCESS: Proved a = a\n");
    } else {
        print("FAILED: Could not prove a = a\n");
    }
    
    print("\n--- Test 7: Prove k = a (symmetry of test 1) ---\n");
    target7 := make_eq(k, a);
    
    proof7 := create_proof(assumptions, target7);
    
    success7 := try_prove_equality(*proof7, k, a, Z);
    
    print("\nAfter try_prove_equality:\n");
    print_proof(*proof7);
    
    if success7 && is_valid(*proof7) {
        print("SUCCESS: Proved k = a\n");
    } else {
        print("FAILED: Could not prove k = a\n");
    }
    
    print("\n=== Summary ===\n");
    print("Test 1 (a = k):     %\n", ifx success1 && is_valid(*proof1) then "PASS" else "FAIL");
    print("Test 2 (g = k):     %\n", ifx success2 && is_valid(*proof2) then "PASS" else "FAIL");
    print("Test 3 (h = i):     %\n", ifx success3 && is_valid(*proof3) then "PASS" else "FAIL");
    print("Test 4 (g = h):     %\n", ifx success4 && is_valid(*proof4) then "PASS" else "FAIL");
    print("Test 5 (a = z):     %\n", ifx !success5 then "PASS" else "FAIL");
    print("Test 6 (a = a):     %\n", ifx success6 && is_valid(*proof6) then "PASS" else "FAIL");
    print("Test 7 (k = a):     %\n", ifx success7 && is_valid(*proof7) then "PASS" else "FAIL");
}
