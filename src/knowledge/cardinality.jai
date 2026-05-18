#import "Basic";
#import "tbx/proof";

cardinality :: (set: *Term) -> *Term {
    return make_function("card", set);
}

domain :: (f: *Term) -> *Term {
    return make_function("domain", f);
}

image :: (f: *Term) -> *Term {
    return make_function("image", f);
}

make_finite_or_infinite_cardinality_fact :: () -> *Formula {
    X := make_variable("X");
    N0 := make_constant("N0");
    Set := make_constant("Set");
    infinity := make_constant("infinity");

    return make_forall(
        "X",
        Set,
        make_xor(
            make_rel(SYM_IN, cardinality(X), N0),
            make_eq(cardinality(X), infinity)
        )
    );
}
