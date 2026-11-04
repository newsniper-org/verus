#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Without -V alloc-check, the `allocates` clause is parsed and carried into VIR but not checked.

test_verify_one_file! {
    #[test] allocates_literal_and_param_ok verus_code! {
        use vstd::prelude::*;
        fn make(x: u8) -> (r: Box<u8>)
            ensures *r == x
            allocates 1
        {
            Box::new(x)
        }

        fn fill(v: &mut Vec<u8>, n: usize)
            allocates n
        {
        }

        fn parenthesized(n: usize)
            allocates(n + 1)
        {
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] allocates_on_external_body_ok verus_code! {
        use vstd::prelude::*;
        #[verifier::external_body]
        fn leaf(x: u8) -> Box<u8>
            allocates 1
        {
            Box::new(x)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] allocates_spec_fn_rejected verus_code! {
        spec fn f(x: nat) -> nat
            allocates 0
        {
            x
        }
    } => Err(err) => assert_vir_error_msg(err, "an `allocates` specification can only be given on exec functions")
}

test_verify_one_file! {
    #[test] allocates_proof_fn_rejected verus_code! {
        proof fn f(x: nat)
            allocates x
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "an `allocates` specification can only be given on exec functions")
}

test_verify_one_file! {
    #[test] allocates_exec_expr_rejected verus_code! {
        fn g() -> u8 {
            3
        }

        fn f()
            allocates g()
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `test_crate::g` with mode exec")
}

test_verify_one_file! {
    #[test] allocates_two_exprs_rejected verus_code! {
        fn f()
            allocates 1, 2
        {
        }
    } => Err(err) => assert_help_error_msg(err, "allocates takes exactly one expression, e.g. `allocates n`")
}

test_verify_one_file! {
    #[test] allocates_is_not_a_reserved_word verus_code! {
        fn allocates(allocates: u8) -> u8 {
            allocates
        }

        fn g() {
            let allocates = allocates(1);
        }
    } => Ok(())
}

// With -V alloc-check: a ghost counter, charged with the callee's `allocates` bound at each exec
// call, must stay within the function's own bound at every normal return.

const ALLOC_LEAF: &str = verus_code_str! {
    use vstd::prelude::*;
    #[verifier::external_body]
    fn mk(x: u8) -> (r: Box<u8>)
        ensures *r == x
        allocates 1
    {
        Box::new(x)
    }
};

test_verify_one_file_with_options! {
    #[test] alloc_check_straight_line ["vstd", "-V alloc-check"] => ALLOC_LEAF.to_string() + verus_code_str! {
        fn zero(x: u8) -> (r: u8)
            ensures r == x
            allocates 0
        {
            x
        }

        fn two(x: u8)
            allocates 2
        {
            let _a = mk(x);
            let _b = mk(x);
        }

        fn two_wrong(x: u8)
            allocates 1 // FAILS
        {
            let _a = mk(x);
            let _b = mk(x);
        }

        fn branch(n: u8)
            allocates if n > 3 { 1int } else { 0int }
        {
            if n > 3 {
                let _a = mk(n);
            }
        }

        fn calls_zero()
            allocates 0
        {
            let _x = zero(1);
        }

        fn nested()
            allocates 3
        {
            two(1);
            let _c = mk(2);
        }

        fn nested_wrong()
            allocates 2 // FAILS
        {
            two(1);
            let _c = mk(2);
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] alloc_check_unspecified_callee_rejected ["vstd", "-V alloc-check"] => verus_code! {
        fn no_spec(x: u8) -> u8 {
            x
        }

        fn calls_no_spec()
            allocates 0
        {
            let _y = no_spec(1);
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot bound the allocations of this call: `test_crate::no_spec` has no `allocates` specification")
}

test_verify_one_file_with_options! {
    #[test] alloc_check_loops_and_recursion ["vstd", "-V alloc-check"] => ALLOC_LEAF.to_string() + verus_code_str! {
        fn looped(n: u8)
            allocates n
        {
            let mut i: u8 = 0;
            while i < n
                invariant
                    i <= n,
                    allocated() == i,
                decreases n - i
            {
                let _a = mk(i);
                i = i + 1;
            }
        }

        fn looped_wrong(n: u8)
            allocates n // FAILS
        {
            let mut i: u8 = 0;
            while i < n
                invariant
                    i <= n,
                    allocated() <= 2 * i,
                decreases n - i
            {
                let _a = mk(i);
                let _b = mk(i);
                i = i + 1;
            }
        }

        fn rec(n: u8)
            decreases n
            allocates n
        {
            if n > 0 {
                let _a = mk(n);
                rec(n - 1);
            }
        }

        fn mid()
            allocates 2
        {
            let _a = mk(1);
            assert(allocated() == 1);
            let _b = mk(2);
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] alloc_check_loop_needs_counter_invariant ["vstd", "-V alloc-check"] => ALLOC_LEAF.to_string() + verus_code_str! {
        // The counter is havocked across the loop; without an invariant on it the bound cannot
        // be shown (it must not pass by accident).
        fn looped(n: u8)
            allocates n // FAILS
        {
            let mut i: u8 = 0;
            while i < n
                invariant
                    i <= n,
                decreases n - i
            {
                let _a = mk(i);
                i = i + 1;
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] alloc_check_allocated_outside_checked_fn ["vstd", "-V alloc-check"] => verus_code! {
        fn no_bound() {
            assert(allocated() == 0);
        }
    } => Err(err) => assert_vir_error_msg(err, "`allocated()` can only be used in the body of an exec function with an `allocates` specification")
}

test_verify_one_file_with_options! {
    #[test] alloc_check_allocated_in_ensures_rejected ["vstd", "-V alloc-check"] => verus_code! {
        fn f()
            ensures allocated() == 0
            allocates 0
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "`allocated()` can only be used in the body of an exec function with an `allocates` specification")
}

test_verify_one_file! {
    #[test] alloc_check_off_does_not_check verus_code! {
        fn no_spec(x: u8) -> u8 {
            x
        }

        fn wrong()
            allocates 0
        {
            let _y = no_spec(1);
        }
    } => Ok(())
}

// Drop rule: implicit drops leave no trace in VIR, so every `Drop::drop` that a checked function
// may run must be bounded by `allocates 0`.

const ALLOC_DROPS: &str = verus_code_str! {
    use vstd::prelude::*;
    pub struct Good {
        pub x: u8,
    }

    impl Drop for Good {
        #[verifier::external_body]
        fn drop(&mut self)
            opens_invariants none
            no_unwind
            allocates 0
        {
        }
    }

    pub struct Bad {
        pub x: u8,
    }

    impl Drop for Bad {
        #[verifier::external_body]
        fn drop(&mut self)
            opens_invariants none
            no_unwind
        {
            let _b = Box::new(1u8);
        }
    }

    pub struct WrapBad {
        pub b: Bad,
    }

    #[verifier::external_body]
    fn mk_bad() -> Bad
        allocates 0
    {
        Bad { x: 0 }
    }
};

test_verify_one_file_with_options! {
    #[test] alloc_check_drop_bounded_ok ["vstd", "-V alloc-check"] => ALLOC_DROPS.to_string() + verus_code_str! {
        fn p(g: Good, v: Vec<u8>, b: Box<u8>, o: Option<Box<u8>>)
            allocates 0
        {
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] alloc_check_drop_unbounded_param ["vstd", "-V alloc-check"] => ALLOC_DROPS.to_string() + verus_code_str! {
        fn p(b: Bad)
            allocates 0
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "its `Drop::drop` is not bounded by `allocates 0`")
}

test_verify_one_file_with_options! {
    #[test] alloc_check_drop_unbounded_field ["vstd", "-V alloc-check"] => ALLOC_DROPS.to_string() + verus_code_str! {
        fn p(w: WrapBad)
            allocates 0
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "its `Drop::drop` is not bounded by `allocates 0`")
}

test_verify_one_file_with_options! {
    #[test] alloc_check_drop_unbounded_in_container ["vstd", "-V alloc-check"] => ALLOC_DROPS.to_string() + verus_code_str! {
        fn p(v: Vec<Bad>)
            allocates 0
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "its `Drop::drop` is not bounded by `allocates 0`")
}

test_verify_one_file_with_options! {
    #[test] alloc_check_drop_unbounded_temporary ["vstd", "-V alloc-check"] => ALLOC_DROPS.to_string() + verus_code_str! {
        fn p() -> u8
            allocates 0
        {
            mk_bad().x
        }
    } => Err(err) => assert_vir_error_msg(err, "its `Drop::drop` is not bounded by `allocates 0`")
}

test_verify_one_file_with_options! {
    #[test] alloc_check_drop_generic_rejected ["vstd", "-V alloc-check"] => verus_code! {
        fn p<T>(t: T)
            allocates 0
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "add the bound `T: vstd::alloc_check::AllocFreeDrop` (or `T: Copy`)")
}

test_verify_one_file_with_options! {
    #[test] alloc_check_verified_drop_body_checked ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::external_body]
        fn mk(x: u8) -> (r: Box<u8>)
            ensures *r == x
            opens_invariants none
            no_unwind
            allocates 1
        {
            Box::new(x)
        }

        pub struct D {
            pub x: u8,
        }

        impl Drop for D {
            fn drop(&mut self)
                opens_invariants none
                no_unwind
                allocates 0 // FAILS
            {
                let _b = mk(1);
            }
        }
    } => Err(err) => assert_one_fails(err)
}

// vstd: Box/Rc/Arc and Vec carry `allocates` bounds; Vec has a capacity model built from what std
// documents as guaranteed (push never reallocates when capacity suffices).

test_verify_one_file_with_options! {
    #[test] alloc_check_vstd_vec_capacity ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        broadcast use vstd::std_specs::vec::group_vec_axioms;

        fn make(x: u8) -> (r: Box<u8>)
            ensures *r == x
            allocates 1
        {
            Box::new(x)
        }

        fn fill_reserved(n: usize) -> (v: Vec<u8>)
            ensures v@.len() == n
            allocates 1
        {
            let mut v: Vec<u8> = Vec::with_capacity(n);
            let mut i: usize = 0;
            while i < n
                invariant
                    i <= n,
                    v@.len() == i,
                    v.capacity() >= n,
                    allocated() <= 1,
                decreases n - i
            {
                v.push(0);
                i = i + 1;
            }
            v
        }

        fn fill_unreserved(n: usize) -> (v: Vec<u8>)
            ensures v@.len() == n
            allocates n
        {
            let mut v: Vec<u8> = Vec::new();
            let mut i: usize = 0;
            while i < n
                invariant
                    i <= n,
                    v@.len() == i,
                    allocated() <= i,
                decreases n - i
            {
                v.push(0);
                i = i + 1;
            }
            v
        }

        fn fill_unreserved_wrong(n: usize) -> (v: Vec<u8>)
            ensures v@.len() == n
            allocates 1 // FAILS
        {
            let mut v: Vec<u8> = Vec::new();
            let mut i: usize = 0;
            while i < n
                invariant
                    i <= n,
                    v@.len() == i,
                    allocated() <= i,
                decreases n - i
            {
                v.push(0);
                i = i + 1;
            }
            v
        }

        fn pop_and_clear(v: &mut Vec<u8>)
            allocates 0
        {
            let _x = v.pop();
            v.clear();
        }
    } => Err(err) => assert_one_fails(err)
}

// W: a generic function's bound mentions its callbacks with `call_allocates`; calls through a
// trait method are charged with `call_allocates(T::m, args)`, tied to each impl's own bound.
// M: `vstd::alloc_check::AllocFreeDrop` marks types whose drop cannot allocate (checked).

test_verify_one_file_with_options! {
    #[test] alloc_check_call_allocates_generic_and_default ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::AllocFreeDrop;

        pub struct C {
            pub x: u8,
        }

        impl AllocFreeDrop for C {}

        impl Clone for C {
            fn clone(&self) -> (r: C)
                ensures r.x == self.x
                allocates 0
            {
                C { x: self.x }
            }
        }

        pub struct H {
            pub x: u8,
        }

        impl AllocFreeDrop for H {}

        impl Clone for H {
            #[verifier::external_body]
            fn clone(&self) -> (r: H)
                allocates 1
            {
                let _b = Box::new(1u8);
                H { x: self.x }
            }
        }

        fn dup<T: Clone + AllocFreeDrop>(x: &T) -> (r: T)
            allocates call_allocates(T::clone, (x,))
        {
            x.clone()
        }

        fn use_c(c: &C)
            allocates 0
        {
            let _d = dup(c);
        }

        fn use_h(h: &H)
            allocates 1
        {
            let _d = dup(h);
        }

        fn use_h_wrong(h: &H)
            allocates 0 // FAILS
        {
            let _d = dup(h);
        }

        pub trait Tr {
            fn req(&self) -> u8;

            fn twice(&self) -> (r: (u8, u8))
                allocates 2 * call_allocates(Self::req, (self,))
            {
                (self.req(), self.req())
            }
        }

        pub struct S;

        impl Tr for S {
            fn req(&self) -> u8
                allocates 1
            {
                let _b = Box::new(1u8);
                7
            }
        }

        fn use_twice(s: &S)
            allocates 2
        {
            let _r = s.twice();
        }

        fn use_twice_wrong(s: &S)
            allocates 1 // FAILS
        {
            let _r = s.twice();
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] alloc_check_marker_bound_ok ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::AllocFreeDrop;

        pub struct Wrap<T> {
            pub t: T,
        }

        impl<T: AllocFreeDrop> AllocFreeDrop for Wrap<T> {}

        fn take<T: AllocFreeDrop>(w: Wrap<T>, v: Vec<T>)
            allocates 0
        {
        }

        fn take_copy<T: Copy>(t: T)
            allocates 0
        {
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] alloc_check_marker_impl_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::AllocFreeDrop;

        pub struct Bad {
            pub x: u8,
        }

        impl Drop for Bad {
            #[verifier::external_body]
            fn drop(&mut self)
                opens_invariants none
                no_unwind
            {
                let _b = Box::new(1u8);
            }
        }

        impl AllocFreeDrop for Bad {}
    } => Err(err) => assert_vir_error_msg(err, "its `Drop::drop` is not bounded by `allocates 0`")
}

// Decision 1: user impls called by std functions are charged through vstd's `call_allocates`
// bounds (`?` -> From::from, `&a == &b` -> PartialEq::eq, Vec::clone -> T::clone per element).

test_verify_one_file_with_options! {
    #[test] alloc_check_std_callbacks ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::AllocFreeDrop;
        broadcast use vstd::std_specs::vec::group_vec_axioms;

        pub struct E1 {}

        pub struct E2 {}

        impl AllocFreeDrop for E1 {}

        impl AllocFreeDrop for E2 {}

        impl From<E1> for E2 {
            #[verifier::external_body]
            fn from(_e: E1) -> E2
                allocates 1
            {
                let _b = Box::new(1u8);
                E2 {}
            }
        }

        fn q(r: Result<u8, E1>) -> Result<u8, E2>
            allocates 1
        {
            let v = r?;
            Ok(v)
        }

        fn q_wrong(r: Result<u8, E1>) -> Result<u8, E2>
            allocates 0 // FAILS
        {
            let v = r?; // FAILS
            Ok(v) // FAILS
        }

        pub struct Q {
            pub x: u8,
        }

        impl AllocFreeDrop for Q {}

        impl PartialEq for Q {
            #[verifier::external_body]
            fn eq(&self, o: &Q) -> bool
                allocates 1
            {
                let _b = Box::new(1u8);
                self.x == o.x
            }
        }

        fn eqr(a: &Q, b: &Q) -> bool
            allocates 1
        {
            a == b
        }

        fn eqr_wrong(a: &Q, b: &Q) -> bool
            allocates 0 // FAILS
        {
            a == b // FAILS
        }

        pub struct C {
            pub x: u8,
        }

        impl AllocFreeDrop for C {}

        impl Clone for C {
            fn clone(&self) -> (r: C)
                ensures r.x == self.x
                allocates 0
            {
                C { x: self.x }
            }
        }

        fn vc(v: &Vec<C>) -> Vec<C>
            allocates 1
        {
            v.clone()
        }
    } => Err(err) => assert_fails(err, 2)
}

// A trait method's own `allocates` bound bounds every impl (and an impl's own bound must be
// within it), so calls through `dyn` or an unresolved type parameter get the trait's bound.

test_verify_one_file_with_options! {
    #[test] alloc_check_trait_declaration_bound ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::external_body]
        fn mk() -> Box<u8>
            allocates 1
        {
            Box::new(1)
        }

        pub trait Tr {
            fn m(&self) -> u8
                allocates 1; // FAILS
        }

        pub struct A;

        impl Tr for A {
            fn m(&self) -> u8
                allocates 0
            {
                1
            }
        }

        pub struct B;

        impl Tr for B {
            fn m(&self) -> u8 {
                let _b = mk();
                2
            }
        }

        pub struct C;

        impl Tr for C {
            fn m(&self) -> u8
                allocates 2
            {
                let _b = mk();
                3
            }
        }

        pub struct D;

        impl Tr for D {
            fn m(&self) -> u8 {
                let _a = mk();
                let _b = mk();
                4
            }
        }

        fn call_dyn(t: &dyn Tr) -> u8
            allocates 1
        {
            t.m()
        }

        fn call_gen<T: Tr>(t: &T) -> u8
            allocates 1
        {
            t.m()
        }

        fn call_a(a: &A) -> u8
            allocates 0
        {
            a.m()
        }

        fn call_dyn_wrong(t: &dyn Tr) -> u8
            allocates 0 // FAILS
        {
            t.m() // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file_with_options! {
    #[test] alloc_check_strict_requires_no_unwind ["vstd", "-V alloc-check-strict"] => verus_code! {
        fn f() -> u8
            allocates 0
        {
            3
        }
    } => Err(err) => assert_vir_error_msg(err, "must be `no_unwind`")
}

test_verify_one_file_with_options! {
    #[test] alloc_check_strict_no_unwind_ok ["vstd", "-V alloc-check-strict"] => verus_code! {
        fn f() -> u8
            no_unwind
            allocates 0
        {
            3
        }

        fn g() -> u8
            no_unwind
            allocates 0
        {
            f()
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // `catch_unwind` cannot be specified at all today (its result holds `dyn Any + Send`), so no
    // checked function can observe a caught panic; alloc-check also rejects it explicitly.
    #[test] alloc_check_catch_unwind_unspecifiable ["vstd", "-V alloc-check"] => verus_code! {
        pub assume_specification<F: FnOnce() -> R + std::panic::UnwindSafe, R>[ std::panic::catch_unwind::<F, R> ](f: F) -> std::thread::Result<R>;

        fn f() -> bool
            allocates 0
        {
            let r = std::panic::catch_unwind(|| 3u8);
            r.is_ok()
        }
    } => Err(err) => assert_vir_error_msg(err, "does not currently support dyn with more than one trait")
}

// `format_args!`: Verus decodes rustc's template to count how often each argument is formatted
// (`{0}{0}` formats argument 0 twice), and `Formatter::write_fmt` charges that many `fmt` calls.
// This test breaks if a toolchain update changes the template encoding.
const FMT_INNER: &str = verus_code_str! {
    use core::fmt::{Display, Formatter, Error};

    pub struct Inner;

    impl Display for Inner {
        fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>
            allocates 1
        {
            let _b = mk(3);
            Ok(())
        }
    }

    impl vstd::std_specs::fmt::DisplaySpecImpl for Inner {
        open spec fn fmt_req(&self, f: &Formatter<'_>) -> bool { true }
    }
};

test_verify_one_file_with_options! {
    #[test] alloc_check_format_template ["vstd", "-V alloc-check"] => ALLOC_LEAF.to_string() + FMT_INNER + verus_code_str! {
        pub struct Twice(Inner);

        impl Display for Twice {
            fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>
                allocates 2
            {
                write!(f, "{0}{0}", self.0)
            }
        }

        impl vstd::std_specs::fmt::DisplaySpecImpl for Twice {
            open spec fn fmt_req(&self, f: &Formatter<'_>) -> bool { true }
        }

        pub struct Mixed(Inner, Inner);

        impl Display for Mixed {
            // literal pieces, a placeholder with options, an explicit index, and a dynamic width
            fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>
                allocates 3
            {
                let w: usize = 4;
                write!(f, "a{}b{:>w$}{0}", self.0, self.1)
            }
        }

        impl vstd::std_specs::fmt::DisplaySpecImpl for Mixed {
            open spec fn fmt_req(&self, f: &Formatter<'_>) -> bool { true }
        }

        pub struct Literal;

        impl Display for Literal {
            fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>
                allocates 0
            {
                write!(f, "hello")?;
                f.write_str("world")
            }
        }

        impl vstd::std_specs::fmt::DisplaySpecImpl for Literal {
            open spec fn fmt_req(&self, f: &Formatter<'_>) -> bool { true }
        }

        pub struct TwiceWrong(Inner);

        impl Display for TwiceWrong {
            fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>
                allocates 1 // FAILS
            {
                write!(f, "{0}{0}", self.0)
            }
        }

        impl vstd::std_specs::fmt::DisplaySpecImpl for TwiceWrong {
            open spec fn fmt_req(&self, f: &Formatter<'_>) -> bool { true }
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] alloc_check_fmt_bound_depends_on_formatter ["vstd", "-V alloc-check"] => verus_code! {
        use core::fmt::{Display, Formatter, Error};

        pub uninterp spec fn cost(f: Formatter<'_>) -> nat;

        pub struct S;

        impl Display for S {
            fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>
                allocates cost(*f)
            {
                Ok(())
            }
        }

        impl vstd::std_specs::fmt::DisplaySpecImpl for S {
            open spec fn fmt_req(&self, f: &Formatter<'_>) -> bool { true }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot depend on the `Formatter`")
}
