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

        unsafe impl AllocFreeDrop for C {}

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

        unsafe impl AllocFreeDrop for H {}

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

        unsafe impl<T: AllocFreeDrop> AllocFreeDrop for Wrap<T> {}

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

        unsafe impl AllocFreeDrop for Bad {}
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

        unsafe impl AllocFreeDrop for E1 {}

        unsafe impl AllocFreeDrop for E2 {}

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

        unsafe impl AllocFreeDrop for Q {}

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

        unsafe impl AllocFreeDrop for C {}

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
                allocates 2 // FAILS
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

test_verify_one_file_with_options! {
    // A forwarding impl passes its formatter on to the inner `fmt`; its bound may mention the
    // formatter only in that position.
    #[test] alloc_check_fmt_forwarding ["vstd", "-V alloc-check"] => ALLOC_LEAF.to_string() + FMT_INNER + verus_code_str! {
        pub struct Wrap<U>(pub U);

        impl<U: Display> Display for Wrap<U> {
            fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>
                allocates call_allocates(<U as Display>::fmt, (&self.0, f))
            {
                write!(f, "{}", self.0)
            }
        }

        impl<U: Display> vstd::std_specs::fmt::DisplaySpecImpl for Wrap<U> {
            open spec fn fmt_req(&self, f: &Formatter<'_>) -> bool {
                forall|g: &Formatter<'_>| vstd::std_specs::fmt::DisplaySpec::fmt_req(&self.0, g)
            }
        }

        pub struct UseWrap;

        impl Display for UseWrap {
            fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>
                allocates 1
            {
                write!(f, "{}", Wrap(Inner))
            }
        }

        impl vstd::std_specs::fmt::DisplaySpecImpl for UseWrap {
            open spec fn fmt_req(&self, f: &Formatter<'_>) -> bool { true }
        }

        pub struct UseWrapWrong;

        impl Display for UseWrapWrong {
            fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>
                allocates 0 // FAILS
            {
                write!(f, "{}", Wrap(Inner))
            }
        }

        impl vstd::std_specs::fmt::DisplaySpecImpl for UseWrapWrong {
            open spec fn fmt_req(&self, f: &Formatter<'_>) -> bool { true }
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] alloc_check_fmt_primitives ["vstd", "-V alloc-check"] => verus_code! {
        use core::fmt::{Display, Formatter, Error};

        pub struct P(pub u8, pub bool, pub char);

        impl Display for P {
            fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>
                allocates 0
            {
                write!(f, "{} {:?} {:x} {:#b} {}", self.0, self.1, self.0, self.0, self.2)
            }
        }

        impl vstd::std_specs::fmt::DisplaySpecImpl for P {
            open spec fn fmt_req(&self, f: &Formatter<'_>) -> bool { true }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] alloc_check_vstd_slice_option_result ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        fn f(s: &mut [u8], o: Option<u8>, r: Result<u8, ()>) -> (x: u8)
            requires
                s.len() >= 2,
                o is Some,
                r is Ok,
            allocates 0
        {
            s.swap(0, 1);
            let a = s[0];
            let b = o.unwrap();
            let c = r.unwrap();
            let d = if s.is_empty() { 0 } else { *s.first().unwrap() };
            let _ = o.is_some();
            let _ = s.len();
            (a / 4) + (b / 4) + (c / 4) + (d / 4)
        }

        fn g(a: u8, b: u8) -> u8
            allocates 0
        {
            a.wrapping_add(b)
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] alloc_check_vstd_elementwise ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        fn eq_slices(a: &[u8], b: &[u8], c: &Vec<u8>, d: &Vec<u8>) -> bool
            allocates 0
        {
            let x = a == b;
            let y = a.contains(&3u8);
            let z = a.starts_with(b);
            let w = c == d;
            let u = a.ends_with(b);
            x && y && z && w && u
        }

        fn arrays(a: [u8; 3]) -> [u8; 3]
            allocates 0
        {
            let b = a.clone();
            if b == a { b } else { a }
        }

        fn grow(v: &mut Vec<u8>, s: &[u8])
            requires old(v).capacity() - old(v).len() >= s.len()
            allocates 0
        {
            v.extend_from_slice(s);
        }

        fn grow_may_alloc(v: &mut Vec<u8>, s: &[u8])
            allocates 1
        {
            v.extend_from_slice(s);
        }

        fn resized(v: &mut Vec<u8>)
            allocates 1
        {
            v.resize(10, 0u8);
        }

        fn filled() -> Vec<u8>
            allocates 1
        {
            vec![0u8; 10]
        }

        fn too_few(v: &mut Vec<u8>, s: &[u8])
            allocates 0 // FAILS
        {
            v.extend_from_slice(s); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] alloc_check_vstd_string ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::string::*;

        fn f(s: &mut String, t: &str) -> bool
            allocates 2
        {
            s.push_str(t);
            s.push('a');
            s.is_empty() || s.as_str().len() == 0
        }

        fn g(t: &str) -> String
            allocates 1
        {
            t.to_owned()
        }

        fn h() -> String
            allocates 0
        {
            String::new()
        }

        fn bad(s: &mut String, t: &str)
            allocates 1 // FAILS
        {
            s.push_str(t);
            s.push('a'); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] alloc_check_vstd_vecdeque_hashmap ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use std::collections::{VecDeque, HashMap};

        fn q(d: &mut VecDeque<u8>) -> usize
            requires old(d)@.len() > 0
            allocates 2
        {
            d.push_back(1);
            d.push_front(2);
            let _ = d.pop_front();
            d.len()
        }

        fn m(h: &HashMap<u8, u8>) -> bool
            allocates 0
        {
            h.is_empty() || h.len() == 0
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] alloc_check_closures ["vstd", "-V alloc-check"] => ALLOC_LEAF.to_string() + verus_code_str! {
        fn direct(x: u8) -> u8
            allocates 1
        {
            let c = |y: u8| -> (r: u8)
                ensures r == y
                allocates 1
            {
                let _b = mk(y);
                y
            };
            c(x)
        }

        fn via_map(o: Option<u8>) -> Option<u8>
            allocates 1
        {
            o.map(|v: u8| -> (r: u8) allocates 1 { let _b = mk(v); v })
        }

        fn pure_closure(o: Option<u8>) -> Option<u8>
            allocates 0
        {
            o.map(|v: u8| -> (r: u8) allocates 0 { v })
        }

        fn counted(x: u8) -> u8
            allocates 2
        {
            let c = |y: u8| -> (r: u8) allocates 1 { let _b = mk(y); y };
            let a = c(x);
            c(a)
        }

        fn too_many(x: u8) -> u8
            allocates 1 // FAILS
        {
            let c = |y: u8| -> (r: u8) allocates 1 { let _b = mk(y); y };
            let a = c(x);
            c(a)
        }

        fn closure_overclaims(x: u8) -> u8
            allocates 1
        {
            let c = |y: u8| -> (r: u8) allocates 0 { let _b = mk(y); y }; // FAILS
            c(x)
        }

        fn unbounded_closure(x: u8) -> u8
            allocates 0 // FAILS
        {
            let c = |y: u8| -> (r: u8) { y };
            c(x)
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file_with_options! {
    // a checked closure inside an unchecked function: its captures' drops still count
    #[test] alloc_check_closure_capture_drop ["vstd", "-V alloc-check"] => ALLOC_DROPS.to_string() + verus_code_str! {
        fn unchecked_outer(b: Bad) -> u8 {
            let c = move || -> (r: u8) allocates 0 {
                let _x = &b;
                3
            };
            c()
        }
    } => Err(err) => assert_vir_error_msg(err, "its `Drop::drop` is not bounded by `allocates 0`")
}

test_verify_one_file_with_options! {
    #[test] alloc_check_closure_strict ["vstd", "-V alloc-check-strict"] => verus_code! {
        fn f() -> u8
            no_unwind
            allocates 0
        {
            let c = |y: u8| -> (r: u8) allocates 0 { y };
            c(1)
        }
    } => Err(err) => assert_vir_error_msg(err, "a closure cannot have an `allocates` bound")
}

test_verify_one_file_with_options! {
    // the bound is evaluated at function entry, also through a `&mut` parameter
    #[test] alloc_check_bound_through_mut_ref_is_pre_state ["vstd", "-V alloc-check"] => ALLOC_LEAF.to_string() + verus_code_str! {
        fn h(v: &mut Vec<u8>)
            requires old(v).len() >= 1
            allocates v.len()
        {
            let _b = mk(0);
            v.clear();
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] alloc_check_for_loops ["vstd", "-V alloc-check"] => ALLOC_LEAF.to_string() + verus_code_str! {
        fn range(n: usize) -> usize
            allocates 0
        {
            let mut s = 0usize;
            for i in 0..n
                invariant s <= i, allocated() == 0,
            {
                s = i;
            }
            s
        }

        fn slice(v: &[u8]) -> u8
            allocates 0
        {
            let mut s = 0u8;
            for x in v.iter()
                invariant allocated() == 0,
            {
                s = *x;
            }
            s
        }

        fn vec_iter(v: &Vec<u8>) -> u8
            allocates 0
        {
            let mut s = 0u8;
            for x in v.iter()
                invariant allocated() == 0,
            {
                s = *x;
            }
            s
        }

        fn vec_into(v: Vec<u8>) -> u8
            allocates 0
        {
            let mut s = 0u8;
            for x in v
                invariant allocated() == 0,
            {
                s = x;
            }
            s
        }

        fn alloc_in_loop(n: usize)
            allocates n
        {
            for i in 0..n
                invariant allocated() <= i,
            {
                let _b = mk(0);
            }
        }

        fn alloc_in_loop_wrong(n: usize)
            allocates 0 // FAILS
        {
            for i in 0..n
                invariant allocated() <= i,
            {
                let _b = mk(0);
            }
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] alloc_check_for_loop_adapters ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        fn zipped(v: &Vec<u8>, w: &Vec<u8>) -> u8
            allocates 0
        {
            let mut s = 0u8;
            for x in iter: v.iter().zip(w.iter())
                invariant allocated() == 0,
            {
                s = *x.0;
            }
            s
        }

        fn nested(v: &Vec<u8>) -> u8
            allocates 0
        {
            let mut s = 0u8;
            for x in iter: v.iter().skip(1).take(2).rev()
                invariant allocated() == 0,
            {
                s = *x;
            }
            s
        }

        fn mapped(v: &Vec<u8>) -> u8
            allocates 0
        {
            let mut s = 0u8;
            for x in iter: v.iter().map(|x: &u8| -> (r: u8) allocates 0 { *x })
                invariant allocated() == 0,
            {
                s = x;
            }
            s
        }

        fn filtered(v: &Vec<u8>) -> u8
            allocates 0
        {
            let mut s = 0u8;
            for x in iter: v.iter().filter(|x: &&u8| -> (r: bool) allocates 0 { **x > 0 })
                invariant allocated() == 0,
            {
                s = *x;
            }
            s
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // a bound that mentions a captured variable is not the same for every value of the closure
    // type, so a `Map` over such a closure is not known to be allocation-free
    #[test] alloc_check_closure_capturing_bound ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        fn capturing(v: &Vec<u8>, n: usize) -> u8
            allocates 0
        {
            let mut s = 0u8;
            for x in iter: v.iter().map(|x: &u8| -> (r: u8) allocates n { *x }) // FAILS
                invariant allocated() == 0, // FAILS
            {
                s = x;
            }
            s
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] alloc_check_vstd_misc_bounds ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use std::collections::VecDeque;

        fn contains(r: &core::ops::Range<usize>, x: usize) -> bool
            allocates 0
        {
            r.contains(&x)
        }

        fn deque(d: &VecDeque<u8>) -> VecDeque<u8>
            allocates 1
        {
            d.clone()
        }

        fn opts(a: Option<u8>, b: Option<u8>) -> bool
            allocates 0
        {
            a == b
        }

        fn conv(x: u32) -> Result<u8, core::num::TryFromIntError>
            allocates 0
        {
            u8::try_from(x)
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // `clear` drops the elements behind the `&mut`, so their type counts as droppable
    #[test] alloc_check_drop_through_mut_ref_in_std_call ["vstd", "-V alloc-check"] => ALLOC_DROPS.to_string() + verus_code_str! {
        fn p(v: &mut Vec<Bad>)
            allocates 0
        {
            v.clear();
        }
    } => Err(err) => assert_vir_error_msg(err, "its `Drop::drop` is not bounded by `allocates 0`")
}

test_verify_one_file_with_options! {
    #[test] alloc_check_mut_ref_to_droppable_ok ["vstd", "-V alloc-check"] => verus_code! {
        fn p(v: &mut Vec<u8>)
            requires old(v).capacity() > old(v).len()
            allocates 0
        {
            v.push(1);
            v.clear();
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] alloc_check_vstd_hashmap ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use std::collections::{HashMap, HashSet};

        fn lookups(m: &mut HashMap<u8, u8>, s: &mut HashSet<u32>) -> bool
            allocates 2
        {
            let _ = m.insert(1, 2);
            let _ = s.insert(3);
            m.contains_key(&1) && s.contains(&3)
        }

        fn gets(m: &HashMap<u32, u8>) -> bool
            allocates 0
        {
            m.get(&1).is_some()
        }

        fn too_many(m: &mut HashMap<u8, u8>)
            allocates 1 // FAILS
        {
            let _ = m.insert(1, 2);
            let _ = m.insert(2, 3);
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    // `to_string` has no numeric bound (the growth of the output `String` depends on its length),
    // but it is no longer "unspecified": its cost is the callbacks plus an opaque growth term
    #[test] alloc_check_to_string_opaque_growth ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::fmt::sink_growth;

        fn show(x: &u8) -> String
            allocates sink_growth(x)
        {
            x.to_string()
        }

        fn show_wrong(x: &u8) -> String
            allocates 0 // FAILS
        {
            x.to_string()
        }
    } => Err(err) => assert_fails(err, 1)
}

// Soundness regressions (reported 2026-11-05)

// The trait declaration's bound only holds where its `requires` holds, so an impl may have a
// larger bound outside the requires without making the axioms contradict each other.
test_verify_one_file_with_options! {
    #[test] alloc_check_trait_bound_outside_requires ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        pub trait Tr {
            fn m(x: u8)
                requires x > 0
                allocates 0;
        }
        pub struct S;
        impl Tr for S {
            fn m(x: u8)
                allocates if x == 0 { 100int } else { 0int }
            {
            }
        }
        proof fn outside() {
            assert(call_allocates(<S as Tr>::m, (0u8,)) == 100);
        }
        proof fn no_contradiction() {
            assert(call_allocates(<S as Tr>::m, (0u8,)) <= 0); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

// An impl's bound must be within the declaration's for every input satisfying the requires, even
// if the body never returns.
test_verify_one_file_with_options! {
    #[test] alloc_check_trait_impl_bound_checked_on_entry ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        pub trait Tr {
            fn m(x: u8) allocates 0;
        }
        pub struct S;
        impl Tr for S {
            #[verifier::exec_allows_no_decreases_clause]
            fn m(x: u8)
                allocates 100
            {
                loop {}
            }
        }
    } => Err(err) => assert_error_msgs(err, &["this `allocates` bound may exceed the trait method's `allocates` bound"])
}

// Without -V alloc-check nothing is checked, so no `call_allocates` axiom may be assumed.
test_verify_one_file! {
    #[test] alloc_check_off_no_call_allocates_axioms verus_code! {
        use vstd::prelude::*;
        pub trait Tr {
            fn m(x: u8) allocates 0;
        }
        pub struct S;
        impl Tr for S {
            fn m(x: u8) allocates 100 { }
        }
        proof fn own_bound() {
            assert(call_allocates(<S as Tr>::m, (0u8,)) == 100); // FAILS
        }
        proof fn decl_bound() {
            assert(call_allocates(<S as Tr>::m, (0u8,)) <= 0); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] alloc_check_unverified_impl_own_bound_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        pub trait Tr {
            fn m(x: u8) allocates 0;
        }
        pub struct S;
        impl Tr for S {
            #[verifier::external_body]
            fn m(x: u8) allocates 100 { }
        }
    } => Err(err) => assert_vir_error_msg(err, "without a verified body it cannot state its own bound")
}

// An opaque type may hide a field whose `Drop` allocates
test_verify_one_file_with_options! {
    #[test] alloc_check_drop_opaque_type_rejected ["vstd", "-V alloc-check"] => ALLOC_DROPS.to_string() + verus_code_str! {
        #[verifier::external_body]
        pub struct Hide {
            b: Bad,
        }

        fn p(h: Hide)
            allocates 0
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "its fields are not visible")
}

test_verify_one_file_with_options! {
    #[test] alloc_check_drop_opaque_copy_type_ok ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::external_body]
        #[derive(Clone, Copy)]
        pub struct C {
            x: u8,
        }

        fn p(c: C)
            allocates 0
        {
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] alloc_check_skip_drops_only_in_vstd ["vstd", "-V alloc-check"] => ALLOC_DROPS.to_string() + verus_code_str! {
        #[verifier::alloc_check_skip_drops]
        fn p()
            allocates 0
        {
            let b = Bad { x: 0 };
        }
    } => Err(err) => assert_vir_error_msg(err, "`#[verifier::alloc_check_skip_drops]` is only allowed in vstd")
}

test_verify_one_file_with_options! {
    #[test] alloc_check_strict_trait_impl ["vstd", "-V alloc-check-strict"] => verus_code! {
        use vstd::prelude::*;
        pub trait Tr {
            fn m(&self) no_unwind allocates 0;
        }
        pub struct S;
        impl Tr for S {
            fn m(&self) { }
        }
        fn g<T: Tr>(t: &T)
            no_unwind
            allocates 0
        {
            t.m()
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] alloc_check_bool_then_charges_closure ["vstd", "-V alloc-check"] => ALLOC_LEAF.to_string() + verus_code_str! {
        fn then_ok(b: bool) -> Option<Box<u8>>
            allocates if b { 1int } else { 0int }
        {
            b.then(|| -> (r: Box<u8>) allocates 1 { mk(0) })
        }

        fn then_wrong(b: bool) -> Option<Box<u8>>
            allocates 0 // FAILS
        {
            b.then(|| -> (r: Box<u8>) allocates 1 { mk(0) })
        }
    } => Err(err) => assert_fails(err, 1)
}

// Soundness regressions from the adversarial hunt (2026-11-05)

// The `call_allocates` axiom of a blanket impl only holds where its bounds hold: `S` is not `Copy`,
// so the blanket's bound says nothing about `S`'s own impl (no contradiction), and a generic
// caller gets no bound from the blanket either.
test_verify_one_file_with_options! {
    #[test] alloc_check_blanket_impl_axiom_guarded ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        pub trait Tr { fn m(&self); }
        impl<T: Copy> Tr for T {
            fn m(&self) allocates 0 {}
        }
        pub struct S;
        impl Tr for S {
            fn m(&self) allocates 1 { let _b = Box::new(1u8); }
        }
        proof fn no_contradiction(s: S)
            ensures false // FAILS
        {
            let a = call_allocates(<S as Tr>::m, (&s,));
        }
    } => Err(err) => assert_fails(err, 1)
}

// `impl<T: Send>`: VIR drops auto-trait bounds, so the axiom cannot be guarded and is not emitted
test_verify_one_file_with_options! {
    #[test] alloc_check_auto_trait_bound_axiom_dropped ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        pub trait Tr { fn m(&self); }
        impl<T: Send> Tr for T {
            fn m(&self) allocates 0 {}
        }
        pub fn use_it<T: Tr>(t: &T) allocates 0 {
            t.m()
        }
    } => Err(err) => assert_error_msgs(err, &["postcondition not satisfied"])
}

// Without -V alloc-check, no closure bound is assumed either (and a negative bound is clamped)
test_verify_one_file! {
    #[test] alloc_check_off_no_closure_axiom verus_code! {
        use vstd::prelude::*;
        fn f()
            ensures false // FAILS
        {
            let c = |n: u8| -> (r: u8) allocates n - 1 { n };
            assert(call_allocates(c, (0u8,)) >= 0);
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] alloc_check_allocated_in_closure_spec_rejected ["vstd", "-V alloc-check"] => ALLOC_LEAF.to_string() + verus_code_str! {
        fn f() allocates 1 {
            let _a = mk(1);
            let c = || -> (r: u8) ensures allocated() == 0 allocates 0 { 0 };
            let _x = c();
        }
    } => Err(err) => assert_vir_error_msg(err, "`allocated()` cannot be used in a closure's `requires`, `ensures` or `allocates`")
}

// A private field in another module is still seen by the drop rule
test_verify_one_file_with_options! {
    #[test] alloc_check_drop_private_field_other_module ["vstd", "-V alloc-check"] => ALLOC_DROPS.to_string() + verus_code_str! {
        pub mod m {
            use vstd::prelude::*;
            pub struct Hide { b: super::Bad }
        }
        fn p(h: m::Hide)
            allocates 0
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "is not bounded by `allocates 0`")
}

// A `Copy` impl for one instantiation says nothing about another
test_verify_one_file_with_options! {
    #[test] alloc_check_copy_exemption_per_instantiation ["vstd", "-V alloc-check"] => ALLOC_DROPS.to_string() + verus_code_str! {
        pub trait Tr { type A; }
        pub struct K1;
        pub struct K2;
        impl Tr for K1 { type A = u8; }
        impl Tr for K2 { type A = Bad; }
        #[verifier::external_body]
        #[verifier::reject_recursive_types(T)]
        pub struct W<T: Tr> { a: T::A }
        impl Clone for W<K1> {
            #[verifier::external_body]
            fn clone(&self) -> Self { W { a: self.a } }
        }
        impl Copy for W<K1> {}
        fn p(w: W<K2>)
            allocates 0
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "its fields are not visible")
}

test_verify_one_file_with_options! {
    #[test] alloc_check_assume_external_rejected ["vstd", "-V alloc-check"] => code! {
        use vstd::prelude::*;
        fn ext() -> u8 { let b = Box::new(3u8); *b }
        verus! {
        #[verifier(assume(externals_available_without_declaration))]
        fn f() -> u8
            allocates 0
        {
            ext()
        }
        }
    } => Err(err) => assert_vir_error_msg(err, "only allowed by `externals_available_without_declaration`")
}

// A std function used as a value may drop values behind its `&mut` parameters
test_verify_one_file_with_options! {
    #[test] alloc_check_std_fn_item_drops ["vstd", "-V alloc-check"] => ALLOC_DROPS.to_string() + verus_code_str! {
        fn p(o: Option<&mut Vec<Bad>>)
            allocates 0
        {
            let _ = o.map(Vec::<Bad>::clear);
        }
    } => Err(err) => assert_vir_error_msg(err, "is not bounded by `allocates 0`")
}

// A call through a std operator trait (no impl with a bound) used to crash
test_verify_one_file_with_options! {
    #[test] alloc_check_std_ops_trait_call_no_crash ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        fn g<T: core::ops::Add<Output = T> + Copy>(a: T) -> T
            requires call_requires(T::add, (a, a))
            allocates 0
        {
            a + a
        }
    } => Err(err) => assert_error_msgs(err, &["postcondition not satisfied"])
}

test_verify_one_file_with_options! {
    #[test] alloc_check_non_regular_type_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use std::mem::ManuallyDrop;
        struct P<T> { v: T, next: Option<Box<P<(T, T)>>> }
        fn f(p: ManuallyDrop<P<u8>>) allocates 0 {}
    } => Err(err) => assert_vir_error_msg(err, "nested too deeply")
}

test_verify_one_file_with_options! {
    #[test] alloc_check_std_iterators_still_bounded ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use std::collections::HashMap;
        fn c(r: &mut core::ops::Range<char>)
            allocates 0
        {
            broadcast use vstd::std_specs::range::group_range_axioms;
            let _x = r.next();
        }
        fn u(r: &mut core::ops::Range<u8>)
            allocates 0
        {
            broadcast use vstd::std_specs::range::group_range_axioms;
            let _x = r.next();
        }
        fn h(m: &HashMap<u64, u64>, k: &u64) -> bool
            allocates 0
        {
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            m.contains_key(k)
        }
        fn hs(m: &HashMap<String, u64>, k: &str) -> bool
            allocates 0
        {
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            m.contains_key(k)
        }
    } => Ok(())
}

// False rejections fixed after the adversarial hunt (2026-11-05)

test_verify_one_file_with_options! {
    #[test] alloc_check_rc_arc_clone_bounds ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use std::rc::Rc;
        use std::sync::Arc;
        pub trait Tr { fn m(); }
        pub struct W<T> { x: T }
        impl<T: Clone> Tr for W<T> { fn m() allocates 0 { } }
        fn a1() allocates 0 { <W<Rc<u8>> as Tr>::m(); }
        fn a2() allocates 0 { <W<Arc<u8>> as Tr>::m(); }
        fn c1(r: &Rc<u8>) -> Rc<u8> allocates 0 { r.clone() }
    } => Ok(())
}

// A bounded `derive(Copy)` on an opaque type: `W<u8>` is `Copy` because `u8: Tr + Copy`
test_verify_one_file_with_options! {
    #[test] alloc_check_opaque_bounded_derive_copy ["vstd", "-V alloc-check"] => code! {
        use vstd::prelude::*;
        use std::marker::PhantomData;
        verus! {
        pub trait Tr { }
        impl Tr for u8 { }
        #[verifier::external_body]
        #[verifier::reject_recursive_types(T)]
        #[derive(Copy)]
        pub struct W<T: Tr> { a: u8, p: PhantomData<T> }
        fn p(w: W<u8>) allocates 0 { }
        }
        impl<T: Tr + Copy> Clone for W<T> { fn clone(&self) -> Self { *self } }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] alloc_check_user_declared_std_adapter ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::external_type_specification]
        #[verifier::external_body]
        #[verifier::reject_recursive_types(I)]
        pub struct ExT<I>(std::iter::Enumerate<I>);
        fn f(x: std::iter::Enumerate<std::vec::IntoIter<u8>>) allocates 0 { }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] alloc_check_ipv4_range ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        fn n(r: &mut core::ops::Range<std::net::Ipv4Addr>)
            allocates 0
        {
            broadcast use vstd::std_specs::range::group_range_axioms;
            let _x = r.next();
        }
    } => Ok(())
}

// Ghost/tracked values used only in ghost code are never dropped at run time
test_verify_one_file_with_options! {
    #[test] alloc_check_ghost_tracked_types_in_ghost_code ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::external_body]
        pub tracked struct Tok {
            no_copy: core::marker::PhantomData<u8>,
        }
        impl Tok {
            pub uninterp spec fn id(&self) -> int;
            pub proof fn touch(tracked &self) ensures self.id() == self.id() {}
        }
        fn use_tok(Tracked(t): Tracked<Tok>) -> (r: u8)
            ensures r == 0
            allocates 0
        {
            proof { t.touch(); }
            0
        }
        #[verifier::external_body]
        pub ghost struct Model { x: u8 }
        fn use_model(Ghost(m): Ghost<Model>) -> (r: u8)
            allocates 0
        {
            let ghost mm = m;
            0
        }
    } => Ok(())
}

// Soundness fixes after the third reading and the check of the false-rejection fixes (2026-11-05)

test_verify_one_file_with_options! {
    // unverified, safe client code may implement a public safe trait without staying within
    // a bound of its declaration
    #[test] alloc_check_safe_api_trait_allocates_rejected ["vstd", "-V alloc-check", "-V check-api-safety"] => verus_code! {
        use vstd::prelude::*;
        pub trait T {
            fn m(&self) allocates 0;
        }
    } => Err(err) => assert_vir_error_msg(err, "safe API violation: `allocates` clause is nontrivial")
}

test_verify_one_file_with_options! {
    #[test] alloc_check_safe_api_unsafe_or_private_trait_allocates_ok ["vstd", "-V alloc-check", "-V check-api-safety"] => verus_code! {
        use vstd::prelude::*;
        pub unsafe trait T {
            fn m(&self) allocates 0;
        }
        trait P {
            fn m(&self) allocates 0;
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // an `external_body` drop is accepted by Verus unverified, so its `allocates 0` is not trusted
    #[test] alloc_check_external_body_drop_not_trusted ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        pub struct S {
            pub x: u8,
        }
        impl Drop for S {
            #[verifier::external_body]
            fn drop(&mut self)
                opens_invariants none
                no_unwind
                allocates 0
            {
                let _b = Box::new(1u8);
            }
        }
        fn f(s: S) allocates 0 { }
    } => Err(err) => assert_vir_error_msg(err, "its `Drop::drop` is not bounded by `allocates 0`")
}

test_verify_one_file_with_options! {
    #[test] alloc_check_verified_drop_trusted ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        pub struct S {
            pub x: u8,
        }
        impl Drop for S {
            fn drop(&mut self)
                opens_invariants none
                no_unwind
                allocates 0
            {
            }
        }
        fn f(s: S) allocates 0 { }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // `Vec::splice` reserves and collects inside `Splice::drop` (std alloc/src/vec/splice.rs)
    #[test] alloc_check_splice_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        fn f(v: &mut Vec<u8>) allocates 0 {
            let _s = v.splice(0..0, [1u8]);
        }
    } => Err(err) => assert_any_vir_error_msg(err, "`alloc::vec::splice::Splice` is not supported")
}

test_verify_one_file_with_options! {
    // a bounded closure that drops an outer closure drops that closure's captures
    #[test] alloc_check_closure_drops_outer_closure_captures ["vstd", "-V alloc-check"] => ALLOC_DROPS.to_string() + verus_code_str! {
        fn unchecked_outer(b: Bad) -> u8 {
            let c1 = move || -> (r: u8) { let _x = &b; 3 };
            let c2 = move || -> (r: u8) allocates 0 { let _y = c1; 3 };
            c2()
        }
    } => Err(err) => assert_vir_error_msg(err, "its `Drop::drop` is not bounded by `allocates 0`")
}

test_verify_one_file_with_options! {
    #[test] alloc_check_closure_drops_outer_closure_ok ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        fn unchecked_outer(x: u8) -> u8 {
            let c1 = move || -> (r: u8) { x };
            let c2 = move || -> (r: u8) allocates 0 { let _y = c1; 3 };
            c2()
        }
    } => Ok(())
}

// An imported crate that was verified without -V alloc-check and implements a trait method with
// an `allocates` bound is rejected, even if this crate only reaches that trait through the bounds
// of an impl in another crate (a.rs: the trait; b.rs: the unchecked impl; c.rs: the checked user).
#[test]
fn alloc_check_unchecked_impl_reached_through_impl_bounds() {
    let tempdir = tempfile::TempDir::new().expect("temp dir");
    let dir = tempdir.path();
    let pre = format!("{}\nuse vstd::prelude::*;\n", FEATURE_PRELUDE);
    let files = [
        (
            "a.rs",
            "verus!{
            pub trait Tr { fn m(&self) allocates 0; }
            pub trait Q { fn q(&self) allocates 0; }
            pub struct Wrap<X>(pub X);
            impl<X: Tr> Q for Wrap<X> { fn q(&self) allocates 0 { self.0.m() } }
            }",
        ),
        (
            "b.rs",
            "verus!{
            pub struct S;
            impl a::Tr for S { fn m(&self) { let mut v: Vec<u8> = Vec::new(); v.push(1); } }
            pub fn make() -> a::Wrap<S> { a::Wrap(S) }
            }",
        ),
        (
            "c.rs",
            "verus!{
            pub fn run<Y: a::Q>(y: &Y) allocates 0 { y.q() }
            }",
        ),
    ];
    for (name, body) in files.iter() {
        std::fs::write(dir.join(name), format!("{}{}\n", pre, body)).expect("write source file");
    }
    let a = run_verus_raw(
        &["--crate-type=lib", "--export", "a.vir", "a.rs", "-V", "alloc-check", "--compile"],
        dir,
    );
    assert!(a.status.success(), "a failed:\n{}", String::from_utf8_lossy(&a.stderr));
    let b = run_verus_raw(
        &[
            "--crate-type=lib",
            "--export",
            "b.vir",
            "b.rs",
            "--import",
            "a=a.vir",
            "--extern",
            "a=liba.rlib",
            "--compile",
        ],
        dir,
    );
    assert!(b.status.success(), "b failed:\n{}", String::from_utf8_lossy(&b.stderr));
    let c = run_verus_raw(
        &[
            "--crate-type=lib",
            "c.rs",
            "--import",
            "a=a.vir",
            "--extern",
            "a=liba.rlib",
            "--import",
            "b=b.vir",
            "--extern",
            "b=libb.rlib",
            "-V",
            "alloc-check",
        ],
        dir,
    );
    let stderr = String::from_utf8_lossy(&c.stderr);
    assert!(!c.status.success(), "c should be rejected:\n{}", stderr);
    assert!(
        stderr.contains("implements a trait method with an `allocates` bound, but its crate was not verified with -V alloc-check"),
        "unexpected error:\n{}", stderr
    );
}

test_verify_one_file_with_options! {
    // `Rc<T, Rc<Global, MyA>>` is not the global allocator just because its outer layer is an
    // `Rc` over `Global`: its allocator argument is a user allocator
    #[test] alloc_check_rc_allocator_arg_not_global ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use std::rc::Rc;
        use std::alloc::{Allocator, AllocatorClone, AllocError, Global, Layout};
        use std::ptr::NonNull;
        #[verifier::external]
        impl Clone for MyA {
            fn clone(&self) -> Self { let b = Box::new(7u8); MyA }
        }
        #[verifier::external]
        unsafe impl Allocator for MyA {
            fn allocate(&self, l: Layout) -> Result<NonNull<[u8]>, AllocError> { Global.allocate(l) }
            unsafe fn deallocate(&self, p: NonNull<u8>, l: Layout) { unsafe { Global.deallocate(p, l) } }
        }
        #[verifier::external]
        unsafe impl AllocatorClone for MyA {}
        pub struct MyA;
        fn clone_opt(o: &Option<Rc<u8, Rc<Global, MyA>>>) -> (res: Option<Rc<u8, Rc<Global, MyA>>>)
            allocates 0
        {
            o.clone()
        }
    } => Err(err) => assert_vir_error_msg(err, "custom allocators (`allocator_api`) are not supported yet")
}

// VIR drops `Send` bounds, so an impl of `Copy` with an auto-trait bound does not show that a
// type is `Copy` (here `W<NotSend>` is not `Copy`, and dropping it drops an `Alloc`). (A file of
// its own: it needs crate-level features.)
#[test]
fn alloc_check_copy_impl_with_auto_trait_bound_not_copy() {
    let tempdir = tempfile::TempDir::new().expect("temp dir");
    let code = format!(
        "{}\n{}",
        FEATURE_PRELUDE,
        r#"
#![feature(with_negative_coherence)]
#![feature(negative_impls)]
use vstd::prelude::*;
pub trait Unk {}
impl<T: ?Sized> Unk for T {}
impl !Send for NotSend {}
impl<T: Send> Pick for T { type Out = u8; }
impl Pick for NotSend where NotSend: Unk { type Out = Alloc; }
verus! {
pub struct Alloc { pub v: u8 }
impl Drop for Alloc {
    #[verifier::external_body]
    fn drop(&mut self) opens_invariants none no_unwind { }
}
pub struct NotSend { pub v: u8 }
pub trait Pick { type Out; }
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct W<T: Pick> { x: <T as Pick>::Out }
impl<T: Send> Clone for W<T> {
    #[verifier::external_body]
    fn clone(&self) -> Self { *self }
}
impl<T: Send> Copy for W<T> {}
pub fn drop_it(w: W<NotSend>) allocates 0 { }
}
"#
    );
    std::fs::write(tempdir.path().join("test.rs"), code).expect("write source file");
    let out = run_verus_raw(&["--crate-type=lib", "test.rs", "-V", "alloc-check"], tempdir.path());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(!out.status.success(), "should be rejected:\n{}", stderr);
    assert!(
        stderr.contains("cannot bound the allocations of dropping a value of type")
            && stderr.contains("its fields are not visible"),
        "unexpected error:\n{}",
        stderr
    );
}

test_verify_one_file_with_options! {
    // a `Copy` obligation on a closure type cannot be stated; rejected instead of crashing
    #[test] alloc_check_copy_obligation_with_closure_type ["vstd", "-V alloc-check"] => code! {
        use vstd::prelude::*;
        use std::marker::PhantomData;
        verus! {
        pub trait Tr { }
        impl<F: Fn(u8) -> u8> Tr for F { }
        #[verifier::external_body]
        #[verifier::reject_recursive_types(T)]
        #[verifier::reject_recursive_types(U)]
        pub struct W<T, U: Tr> { a: T, p: PhantomData<U> }
        #[verifier::external_body]
        fn mk<U: Tr>(u: &U) -> W<u8, U> allocates 0 { W { a: 0, p: PhantomData } }
        fn f() allocates 0 {
            let c = |x: u8| -> (r: u8) allocates 0 { x };
            let w = mk(&c);
        }
        }
        impl<T: Copy, U: Tr> Clone for W<T, U> { fn clone(&self) -> Self { *self } }
        impl<T: Copy, U: Tr> Copy for W<T, U> { }
    } => Err(err) => assert_vir_error_msg(err, "its fields are not visible")
}

// Adversarial round on the fixes above (2026-11-05)

test_verify_one_file_with_options! {
    // `AllocFreeDrop` is an `unsafe trait`, and an impl that Verus does not see is not trusted
    #[test] alloc_check_alloc_free_drop_impl_outside_verus_rejected ["vstd", "-V alloc-check"] => code! {
        use vstd::prelude::*;
        use vstd::alloc_check::AllocFreeDrop;
        pub struct Evil { pub b: Box<u8> }
        impl Drop for Evil { fn drop(&mut self) { let _x = Box::new(1u8); } }
        unsafe impl AllocFreeDrop for Evil {}
        verus! {
        fn consume<X: AllocFreeDrop>(x: X) allocates 0 { }
        }
    } => Err(err) => assert_vir_error_msg(err, "this `AllocFreeDrop` impl is not checked by Verus")
}

test_verify_one_file_with_options! {
    // an impl that Verus does not see may not implement a method whose declaration has a bound
    #[test] alloc_check_bounded_method_impl_outside_verus_rejected ["vstd", "-V alloc-check"] => code! {
        use vstd::prelude::*;
        verus! {
        pub trait Tr { fn m(&self) allocates 0; }
        fn use_it<T: Tr>(t: &T) allocates 0 { t.m() }
        }
        pub struct S;
        impl Tr for S { fn m(&self) { let _v = Box::new(1u8); } }
    } => Err(err) => assert_vir_error_msg(err, "whose declaration has an `allocates` bound, but Verus does not check this impl")
}

test_verify_one_file_with_options! {
    // `rev`/`map`/`filter`/`skip`/`take`/`zip` may be overridden by an iterator type other than
    // std's, so they cost 0 only for iterators that are known to be std's (`iter_aux_alloc_free`)
    #[test] alloc_check_iterator_provided_methods_per_impl ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::AllocFreeDrop;
        use std::iter::Rev;
        fn ok<I: DoubleEndedIterator + AllocFreeDrop>(i: I) -> Rev<I>
            requires vstd::std_specs::iter::iter_aux_alloc_free::<I>(),
            allocates 0
        {
            i.rev()
        }
        fn concrete(v: &Vec<u8>) -> usize allocates 0 {
            let _it = v.iter().rev();
            0
        }
        fn bad<I: DoubleEndedIterator + AllocFreeDrop>(i: I) -> Rev<I>
            allocates 0 // FAILS
        {
            i.rev()
        }
    } => Err(err) => assert_one_fails(err)
}

// A dependency named `std` that is not the toolchain's is rejected, also when `--sysroot` is
// chosen so that it lies inside it (the toolchain's std is then a second crate named `std`)
#[test]
fn alloc_check_second_std_crate_rejected() {
    let tempdir = tempfile::TempDir::new().expect("temp dir");
    let dir = tempdir.path();
    let libdir = run_verus_raw(&["--print", "target-libdir"], dir);
    let libdir =
        String::from_utf8_lossy(&libdir.stdout).lines().next().unwrap_or("").trim().to_string();
    assert!(!libdir.is_empty(), "no target-libdir");
    std::fs::write(
        dir.join("fakestd.rs"),
        format!("{}\n{}\npub struct Hidden;\n", FEATURE_PRELUDE, USE_PRELUDE),
    )
    .expect("write");
    let fake = run_verus_raw(
        &[
            "--crate-type=rlib",
            "--crate-name",
            "std",
            "-C",
            "metadata=fake",
            "--no-vstd",
            "--no-verify",
            "--compile",
            "fakestd.rs",
            "-o",
            "libfstd.rlib",
        ],
        dir,
    );
    assert!(fake.status.success(), "fake std failed:\n{}", String::from_utf8_lossy(&fake.stderr));
    let code = format!(
        "{}\nuse vstd::prelude::*;\nverus! {{ fn f() allocates 0 {{ }} }}\npub fn g(_h: fstd::Hidden) {{ }}\n",
        FEATURE_PRELUDE
    );
    std::fs::write(dir.join("c.rs"), code).expect("write");
    for extra in [&[][..], &["--sysroot", "/", "-L", libdir.as_str()][..]] {
        let mut args =
            vec!["--crate-type=lib", "c.rs", "-V", "alloc-check", "--extern", "fstd=libfstd.rlib"];
        args.extend_from_slice(extra);
        let c = run_verus_raw(&args, dir);
        let stderr = String::from_utf8_lossy(&c.stderr);
        assert!(!c.status.success(), "should be rejected ({:?}):\n{}", extra, stderr);
        assert!(
            stderr.contains(
                "-V alloc-check trusts a crate named `std` only if it is the toolchain's"
            ),
            "unexpected error ({:?}):\n{}",
            extra,
            stderr
        );
    }
}

// An imported crate named `vstd` must have been verified as vstd
#[test]
fn alloc_check_fake_vstd_rejected() {
    let tempdir = tempfile::TempDir::new().expect("temp dir");
    let dir = tempdir.path();
    let fv = format!(
        "{}\n{}\npub mod prelude {{ pub use verus_builtin::*; pub use verus_builtin_macros::*; }}\nverus! {{ pub struct Opq {{ pub x: u8 }} }}\n",
        FEATURE_PRELUDE, USE_PRELUDE
    );
    std::fs::write(dir.join("fv.rs"), fv).expect("write");
    let a = run_verus_raw(
        &[
            "--crate-type=lib",
            "--crate-name",
            "vstd",
            "--no-vstd",
            "fv.rs",
            "--export",
            "vstd.vir",
            "--compile",
        ],
        dir,
    );
    assert!(a.status.success(), "fake vstd failed:\n{}", String::from_utf8_lossy(&a.stderr));
    let c = format!(
        "{}\n{}\nverus! {{ fn run(d: vstd::Opq) allocates 0 {{ }} }}\n",
        FEATURE_PRELUDE, USE_PRELUDE
    );
    std::fs::write(dir.join("c.rs"), c).expect("write");
    let out = run_verus_raw(
        &[
            "--crate-type=lib",
            "c.rs",
            "--no-vstd",
            "-V",
            "alloc-check",
            "--import",
            "vstd=vstd.vir",
            "--extern",
            "vstd=libvstd.rlib",
        ],
        dir,
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(!out.status.success(), "should be rejected:\n{}", stderr);
    assert!(
        stderr.contains("the imported crate named `vstd` was not verified as vstd"),
        "unexpected error:\n{}",
        stderr
    );
    // and its .vir paired with a different build of the crate named `vstd`
    let b = run_verus_raw(
        &[
            "--crate-type=lib",
            "--crate-name",
            "vstd",
            "--no-vstd",
            "-C",
            "metadata=other",
            "fv.rs",
            "--compile",
            "--out-dir",
            "other",
        ],
        dir,
    );
    assert!(b.status.success(), "other vstd failed:\n{}", String::from_utf8_lossy(&b.stderr));
    let out = run_verus_raw(
        &[
            "--crate-type=lib",
            "c.rs",
            "--no-vstd",
            "-V",
            "alloc-check",
            "--import",
            "vstd=vstd.vir",
            "--extern",
            "vstd=other/libvstd.rlib",
        ],
        dir,
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(!out.status.success(), "should be rejected:\n{}", stderr);
    assert!(
        stderr.contains("does not belong to the crate named `vstd` that this crate is linked with"),
        "unexpected error:\n{}",
        stderr
    );
}

test_verify_one_file_with_options! {
    // the implementations (and provided methods) of a trait given by an
    // `external_trait_specification` are not checked by Verus, so its methods may not have bounds
    // (vstd's, per-implementation cost terms, are the exception)
    #[test] alloc_check_external_trait_spec_bound_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::external_trait_specification]
        pub trait ExWrite {
            type ExternalTraitSpecificationFor: core::fmt::Write;
            fn write_str(&mut self, s: &str) -> core::fmt::Result allocates 0;
        }
    } => Err(err) => assert_vir_error_msg(err, "an `allocates` bound on a method of an `external_trait_specification` is not supported outside vstd")
}

// A .vir written by a run whose -V alloc-check verification failed does not mark its bounds as
// checked
#[test]
fn alloc_check_failed_export_not_trusted() {
    let tempdir = tempfile::TempDir::new().expect("temp dir");
    let dir = tempdir.path();
    let pre = format!("{}\nuse vstd::prelude::*;\n", FEATURE_PRELUDE);
    std::fs::write(
        dir.join("a.rs"),
        format!(
            "{pre}verus!{{ pub fn f() -> (r: u64) allocates 0 {{ let b = Box::new(7u64); *b }} }}\n"
        ),
    )
    .expect("write");
    std::fs::write(
        dir.join("c.rs"),
        format!("{pre}verus!{{ pub fn run() -> (r: u64) allocates 0 {{ a::f() }} }}\n"),
    )
    .expect("write");
    let failed = run_verus_raw(
        &[
            "--crate-type=lib",
            "--crate-name",
            "a",
            "--export",
            "a.vir",
            "a.rs",
            "-V",
            "alloc-check",
        ],
        dir,
    );
    assert!(!failed.status.success(), "a should fail verification");
    std::fs::rename(dir.join("a.vir"), dir.join("a_failed.vir")).expect("a.vir written");
    let rlib = run_verus_raw(
        &["--crate-type=lib", "--crate-name", "a", "a.rs", "--no-verify", "--compile"],
        dir,
    );
    assert!(rlib.status.success(), "a rlib:\n{}", String::from_utf8_lossy(&rlib.stderr));
    let c = run_verus_raw(
        &[
            "--crate-type=lib",
            "c.rs",
            "-V",
            "alloc-check",
            "--import",
            "a=a_failed.vir",
            "--extern",
            "a=liba.rlib",
        ],
        dir,
    );
    let stderr = String::from_utf8_lossy(&c.stderr);
    assert!(!c.status.success(), "c should be rejected:\n{}", stderr);
    assert!(
        stderr.contains("its crate was not verified with -V alloc-check"),
        "unexpected:\n{}",
        stderr
    );
}

test_verify_one_file_with_options! {
    // `impl<A: Copy> Copy for W<A>` makes `W<D>` `Copy` only if `D` is: with a non-`Copy` `D`,
    // the hidden field of the opaque `W<D>` may be anything (here `<D as Pick>::Out`)
    #[test] alloc_check_generic_copy_impl_needs_copy_args ["vstd", "-V alloc-check"] => code! {
        use vstd::prelude::*;
        pub struct Noisy(pub u8);
        impl Drop for Noisy {
            fn drop(&mut self) { let v: Vec<u8> = vec![self.0; 4]; }
        }
        verus! {
        #[verifier::external_body]
        pub struct ExtNoisy(Noisy);
        pub trait Pick { type Out; }
        impl<T: Copy> Pick for T { type Out = T; }
        pub struct D;
        impl Pick for D { type Out = ExtNoisy; }
        #[verifier::external_body]
        #[verifier::reject_recursive_types(A)]
        pub struct W<A: Pick>(pub <A as Pick>::Out);
        impl<A: Copy> Clone for W<A> {
            fn clone(&self) -> Self { *self }
        }
        impl<A: Copy> Copy for W<A> {}
        pub fn consume(w: W<D>) allocates 0 {}
        pub fn consume_copy(w: W<u8>) allocates 0 {}
        }
    } => Err(err) => assert_vir_error_msg(err, "dropping a value of type `test_crate::W<test_crate::D>`: its fields are not visible")
}

// A checked .vir describes one build of its crate: an rlib of a newer version of the crate (with
// the same crate id) is rejected
#[test]
fn alloc_check_stale_vir_rejected() {
    let tempdir = tempfile::TempDir::new().expect("temp dir");
    let dir = tempdir.path();
    let pre = format!("{}\nuse vstd::prelude::*;\n", FEATURE_PRELUDE);
    std::fs::create_dir_all(dir.join("v1")).expect("mkdir");
    std::fs::create_dir_all(dir.join("v2")).expect("mkdir");
    std::fs::write(
        dir.join("v1/a.rs"),
        format!("{pre}verus!{{ pub fn f() -> (r: u64) allocates 0 {{ 1 }} }}\n"),
    )
    .expect("write");
    std::fs::write(
        dir.join("v2/a.rs"),
        format!(
            "{pre}verus!{{ #[verifier::external_body] fn g() -> u64 {{ let b = Box::new(2u64); *b }} pub fn f() -> (r: u64) {{ g() }} }}\n"
        ),
    )
    .expect("write");
    std::fs::write(
        dir.join("c.rs"),
        format!("{pre}verus!{{ pub fn run() -> (r: u64) allocates 0 {{ a::f() }} }}\n"),
    )
    .expect("write");
    let v1 = run_verus_raw(
        &["--crate-type=lib", "v1/a.rs", "-V", "alloc-check", "--export", "a.vir", "--compile"],
        dir,
    );
    assert!(v1.status.success(), "v1:\n{}", String::from_utf8_lossy(&v1.stderr));
    let ok = run_verus_raw(
        &[
            "--crate-type=lib",
            "c.rs",
            "-V",
            "alloc-check",
            "--import",
            "a=a.vir",
            "--extern",
            "a=liba.rlib",
        ],
        dir,
    );
    assert!(ok.status.success(), "c with v1:\n{}", String::from_utf8_lossy(&ok.stderr));
    let v2 = run_verus_raw(&["--crate-type=lib", "v2/a.rs", "--compile"], dir);
    assert!(v2.status.success(), "v2:\n{}", String::from_utf8_lossy(&v2.stderr));
    let c = run_verus_raw(
        &[
            "--crate-type=lib",
            "c.rs",
            "-V",
            "alloc-check",
            "--import",
            "a=a.vir",
            "--extern",
            "a=liba.rlib",
        ],
        dir,
    );
    let stderr = String::from_utf8_lossy(&c.stderr);
    assert!(!c.status.success(), "stale .vir should be rejected:\n{}", stderr);
    assert!(
        stderr.contains(
            "the imported library file for `a` was not produced together with the build of it"
        ),
        "unexpected:\n{}",
        stderr
    );
}

test_verify_one_file_with_options! {
    // the examples of docs/guide/src/reference-allocates.md (and its Korean counterpart)
    #[test] alloc_check_guide_examples ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::AllocFreeDrop;
        fn make_pair(x: u64) -> (r: (Box<u64>, Box<u64>))
            allocates 2
        {
            (Box::new(x), Box::new(x))
        }

        fn push_one(v: &mut Vec<u64>, x: u64)
            allocates if old(v)@.len() == vstd::std_specs::vec::spec_vec_capacity(&*old(v)) { 1int } else { 0int }
        {
            v.push(x);
        }

        fn boxes(n: usize) -> (r: Vec<Box<usize>>)
            allocates 1 + n
        {
            broadcast use vstd::std_specs::vec::group_vec_axioms;
            let mut v: Vec<Box<usize>> = Vec::with_capacity(n);
            for i in 0..n
                invariant
                    v@.len() == i,
                    n <= vstd::std_specs::vec::spec_vec_capacity(&v),
                    allocated() <= 1 + i,
            {
                v.push(Box::new(i));
            }
            v
        }

        pub trait Shape {
            fn area(&self) -> u64 allocates 0;
        }

        fn total<S: Shape>(a: &S, b: &S) -> u64
            allocates 0
        {
            let x = a.area();
            let y = b.area();
            if x < 1000 && y < 1000 { x + y } else { 0 }
        }

        fn apply<F: Fn(u64) -> u64>(f: &F, x: u64) -> u64
            requires f.requires((x,)),
            allocates call_allocates(*f, (x,))
        {
            f(x)
        }

        fn use_apply() -> u64
            allocates 0
        {
            let half = |y: u64| -> (r: u64) allocates 0 { y / 2 };
            apply(&half, 7)
        }

        fn consume<T: AllocFreeDrop>(t: T)
            allocates 0
        {
        }

        pub struct Handle { pub id: u64 }

        impl Drop for Handle {
            fn drop(&mut self)
                opens_invariants none
                no_unwind
                allocates 0
            {
            }
        }

        unsafe impl AllocFreeDrop for Handle {}

        fn drop_handle(h: Handle) allocates 0 { consume(h) }
    } => Ok(())
}
