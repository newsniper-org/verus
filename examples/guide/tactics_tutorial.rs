#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use verus_builtin_macros::*;
use vstd::prelude::*;

// The code of the tutorial `tutorial-tactics.md` (and `.ko.md`): every function here verifies.
verus! {

// ANCHOR: split
proof fn t_split(x: int, y: int)
    requires
        x > 0,
        y > 0,
{
    assert(x > 0 && y > 0) by(tactic) {
        split();
    }
}
// ANCHOR_END: split

// ANCHOR: apply
spec fn f(x: int) -> int {
    x + 1
}

proof fn lemma_f(x: int)
    ensures
        f(x) > x,
{
}

proof fn t_apply(x: int, y: int) {
    assert(f(x) > x && f(y) > y) by(tactic) {
        split({ apply(lemma_f(x)); }, { apply(lemma_f(y)); });
    }
    assert(f(f(x)) > x) by(tactic) {
        apply(lemma_f(x));
        apply(lemma_f(f(x)));
        have(f(f(x)) > f(x));
    }
}
// ANCHOR_END: apply

// ANCHOR: intro
proof fn t_intro(n: int) {
    assert(forall|i: int| 0 <= i < n ==> #[trigger] f(i) > i) by(tactic) {
        intro();
        apply(lemma_f(i));
    }
    assert(n > 0 ==> f(n) > 1) by(tactic) {
        intro();
        apply(lemma_f(n));
    }
}
// ANCHOR_END: intro

// ANCHOR: inst
uninterp spec fn g(x: int) -> int;

proof fn t_inst(a: int)
    requires
        forall|x: int| #[trigger] g(x) >= 0,
{
    assert(g(a + 1) >= 0) by(tactic) {
        inst(forall|x: int| #[trigger] g(x) >= 0, a + 1);
    }
}
// ANCHOR_END: inst

// ANCHOR: cases_bool
proof fn t_cases_bool(x: int) {
    assert(x * x >= 0) by(tactic) {
        cases(x >= 0, { smt(nonlinear_arith, x >= 0); }, { smt(nonlinear_arith, x < 0); });
    }
}
// ANCHOR_END: cases_bool

// ANCHOR: cases_enum
enum Shape {
    Dot,
    Line(u64),
    Rect(u64, u64),
}

spec fn corners(s: Shape) -> nat {
    match s {
        Shape::Dot => 1,
        Shape::Line(_) => 2,
        Shape::Rect(_, _) => 4,
    }
}

proof fn t_cases_enum(s: Shape) {
    // one case per variant
    assert(corners(s) >= 1) by(tactic) {
        cases(s);
    }
    // the fields, named by a pattern
    assert(corners(s) <= 4) by(tactic) {
        cases(match s {
            Shape::Rect(w, h) => { have(corners(s) == 4); },
            _ => { },
        });
    }
}
// ANCHOR_END: cases_enum

// ANCHOR: unfold
spec fn sum(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        n + sum((n - 1) as nat)
    }
}

#[verifier::opaque]
spec fn inv(x: int) -> bool {
    0 < x && x < 10 && x != 5
}

proof fn t_unfold(x: int)
    requires
        x == 3,
{
    // more fuel for a recursive function
    assert(sum(3) == 6) by(tactic) {
        unfold(sum, 4);
    }
    // the body of an opaque function, split into its parts
    assert(inv(x)) by(tactic) {
        unfold(inv);
        split();
    }
}
// ANCHOR_END: unfold

// ANCHOR: unfold_intro
spec fn small(i: int) -> bool {
    i < 100
}

#[verifier::opaque]
spec fn all_small(n: int) -> bool {
    forall|i: int| 0 <= i < n ==> #[trigger] small(i)
}

proof fn t_unfold_intro(n: int)
    requires
        n <= 100,
{
    assert(all_small(n)) by(tactic) {
        unfold(all_small);
        intro();
    }
}
// ANCHOR_END: unfold_intro

// ANCHOR: show
proof fn t_show(y: int)
    requires
        y == 2,
{
    assert(inv(y + 1)) by(tactic) {
        have(y > 1);
        unfold(inv);
        show();
        split();
    }
}
// ANCHOR_END: show

// ANCHOR: induct_nat
spec fn pow2(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        1
    } else {
        2 * pow2((n - 1) as nat)
    }
}

spec fn tri(i: int) -> int
    decreases i,
{
    if i <= 0 {
        0
    } else {
        i + tri(i - 1)
    }
}

proof fn t_induct_nat(n: nat, i: int)
    requires
        i >= 0,
{
    // the rest of the script proves both cases
    assert(pow2(n) >= 1) by(tactic) {
        induct(n);
    }
    // a block for each case
    assert(pow2(n) >= 1) by(tactic) {
        induct(n, { }, { have(pow2(n) == 2 * pow2((n - 1) as nat)); });
    }
    // an `int`, from a start
    assert(tri(i) >= 0) by(tactic) {
        induct(i, from(0));
    }
}
// ANCHOR_END: induct_nat

// ANCHOR: induct_list
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

spec fn append(a: List, b: List) -> List
    decreases a,
{
    match a {
        List::Nil => b,
        List::Cons(h, t) => List::Cons(h, Box::new(append(*t, b))),
    }
}

proof fn t_induct_list(a: List, b: List) {
    assert(len(append(a, b)) == len(a) + len(b)) by(tactic) {
        induct(a);
    }
    assert(total(append(a, b)) == total(a) + total(b)) by(tactic) {
        induct(a);
    }
}
// ANCHOR_END: induct_list

// ANCHOR: induct_hyp
spec fn allpos(l: List) -> bool
    decreases l,
{
    match l {
        List::Nil => true,
        List::Cons(h, t) => h > 0 && allpos(*t),
    }
}

proof fn t_induct_hyp(l: List)
    requires
        allpos(l),
{
    // a hypothesis about the induction variable goes into the goal
    assert(allpos(l) ==> total(l) >= len(l)) by(tactic) {
        induct(l);
    }
}
// ANCHOR_END: induct_hyp

// ANCHOR: induct_tree
enum Tree {
    Leaf,
    Node { left: Box<Tree>, val: int, right: Box<Tree> },
}

spec fn size(t: Tree) -> nat
    decreases t,
{
    match t {
        Tree::Leaf => 1,
        Tree::Node { left, right, .. } => size(*left) + 1 + size(*right),
    }
}

spec fn leaves(t: Tree) -> nat
    decreases t,
{
    match t {
        Tree::Leaf => 1,
        Tree::Node { left, right, .. } => leaves(*left) + leaves(*right),
    }
}

proof fn t_induct_tree(t: Tree) {
    // two hypotheses in the case `Node`: for `left` and for `right`
    assert(size(t) + 1 == 2 * leaves(t)) by(tactic) {
        induct(t);
    }
}
// ANCHOR_END: induct_tree

// ANCHOR: induct_exec
fn t_induct_exec(Ghost(l): Ghost<List>, k: u64) -> (r: u64)
    ensures
        r == k,
{
    proof {
        assert(len(l) >= 0) by(tactic) {
            induct(l);
        }
    }
    k
}
// ANCHOR_END: induct_exec

// ANCHOR: isolate
#[verifier::rlimit(1)]
proof fn t_isolate() {
    // only this proof gets the larger rlimit
    assert(sum(12) == 78) by(tactic) {
        isolate(rlimit = 10);
        unfold(sum, 13);
    }
}

#[verifier::rlimit(1)]
proof fn t_isolate_ensures(n: nat)
    ensures
        #![verifier::tactic(isolate(rlimit = 10))]
        sum(12) == 78,
        n + 0 == n,
{
    reveal_with_fuel(sum, 13);
}
// ANCHOR_END: isolate

} // verus!
