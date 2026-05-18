#import "Basic";
#import "tbx/proof";

logic_contradiction :: () -> *Formula {
    return make_rel("contradiction");
}

make_refute_left_fact :: (P: *Formula, Q: *Formula) -> *Formula {
    return make_implies(
        make_and(make_or(P, Q), make_implies(P, logic_contradiction())),
        Q
    );
}

make_refute_right_fact :: (P: *Formula, Q: *Formula) -> *Formula {
    return make_implies(
        make_and(make_or(P, Q), make_implies(Q, logic_contradiction())),
        P
    );
}
