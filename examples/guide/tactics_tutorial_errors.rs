// rust_verify/tests/example.rs expect-failures
#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use verus_builtin_macros::*;
use vstd::prelude::*;

// The failing examples of the tutorial `tutorial-tactics.md` (and `.ko.md`): each `// FAILS`
// line fails, and the error says which step (and which case) made the assertion.
verus! {

// ANCHOR: split_fails
proof fn e_split(x: int, y: int)
    requires
        x > 0,
{
    // FAILS at `y > 0`: from the tactic step `split` (part 2 of 2)
    assert(x > 0 && y > 0) by(tactic) {
        split();
    }
}
// ANCHOR_END: split_fails

// ANCHOR: unfold_fails
#[verifier::opaque]
spec fn inv(x: int) -> bool {
    0 < x && x < 10 && x != 5
}

proof fn e_unfold(x: int)
    requires
        x == 5,
{
    // FAILS at `x != 5` in the body of `inv`:
    // from the tactic step `split` (part 3 of 3, after `unfold`)
    assert(inv(x)) by(tactic) {
        unfold(inv);
        split();
    }
}
// ANCHOR_END: unfold_fails

// ANCHOR: induct_fails
enum List {
    Nil,
    Cons(int, Box<List>),
}

spec fn len(l: List) -> nat
    decreases l,
{
    match l {
        List::Nil => 0,
        List::Cons(_, t) => 1 + len(*t),
    }
}

spec fn total(l: List) -> int
    decreases l,
{
    match l {
        List::Nil => 0,
        List::Cons(h, t) => h + total(*t),
    }
}

proof fn e_induct_base(l: List) {
    // not true for `Nil`; FAILS: from the tactic step `induct` (`l` is `List::Nil`)
    assert(len(l) > 0) by(tactic) {
        induct(l);
    }
}

proof fn e_induct_step(l: List) {
    // not true: the elements may be negative; the `have` fails in the case `Cons`
    assert(total(l) >= 0) by(tactic) {
        induct(l);
        have(total(l) >= 0);  // FAILS: from the tactic step `have`, where `l` is `List::Cons`
    }
}
// ANCHOR_END: induct_fails

} // verus!
