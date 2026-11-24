#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// `T: Tr with { fn m(..) .. allocates e; fn drop allocates 0; }`: a specification of a bound's
// methods on a function's type parameter, checked where the function is instantiated

const DUP: &str = verus_code_str! {
    use vstd::prelude::*;

    fn dup<T: Clone with { fn clone(&self) -> Self allocates 0; fn drop allocates 0; }>(x: &T) -> (r: (T, T))
        allocates 0
    {
        (x.clone(), x.clone())
    }

    fn first<T: Clone with { fn clone(&self) -> (r: Self) ensures r == *self allocates 0; fn drop allocates 0; }>(x: &T) -> (r: T)
        ensures r == *x,
        allocates 0
    {
        x.clone()
    }

    pub struct P(pub u64);

    impl Clone for P {
        fn clone(&self) -> (r: Self)
            ensures r == *self
            allocates 0
        {
            P(self.0)
        }
    }
};

test_verify_one_file_with_options! {
    #[test] with_bound_ok ["vstd", "-V alloc-check"] => DUP.to_string() + verus_code_str! {
        fn caller(p: &P)
            allocates 0
        {
            let _ = dup(p);
            let _ = dup(&3u64);
            let q = first(p);
            assert(q == *p);
        }

        fn generic_caller<U: Clone with { fn clone(&self) -> Self allocates 0; fn drop allocates 0; }>(u: &U)
            allocates 0
        {
            let _ = dup(u);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] with_bound_clone_allocates ["vstd", "-V alloc-check"] => DUP.to_string() + verus_code_str! {
        fn caller_bad(s: &Vec<u8>)
            allocates 10
        {
            let _ = dup(s); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] with_bound_drop_allocates ["vstd", "-V alloc-check"] => DUP.to_string() + verus_code_str! {
        #[verifier::external_body]
        fn mk() -> (r: Box<u8>)
            opens_invariants none
            no_unwind
            allocates 1
        {
            Box::new(1)
        }

        pub struct D(pub u64);

        impl Clone for D {
            fn clone(&self) -> (r: Self) { D(self.0) }
        }

        impl Drop for D {
            fn drop(&mut self)
                opens_invariants none
                no_unwind
                allocates 1
            {
                let _b = mk();
            }
        }

        fn caller(d: &D) {
            let _ = dup(d); // (rejected: dropping a `D` allocates)
        }
    } => Err(err) => assert_vir_error_msg(err, "its `Drop::drop` is not bounded by `allocates 0`")
}

test_verify_one_file_with_options! {
    #[test] with_bound_requires ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        pub trait Get {
            fn get(&self, i: u64) -> u64
                requires i < 10;
        }

        fn use_get<T: Get with { fn get(&self, i: u64) -> u64 requires i < 20 allocates 0; }>(t: &T) -> u64
            allocates 0
        {
            t.get(15)
        }

        pub struct S;

        impl Get for S {
            fn get(&self, i: u64) -> u64
                allocates 0
            {
                i
            }
        }

        fn caller() {
            let _ = use_get(&S); // FAILS: Get::get requires i < 10, not i < 20
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] with_bound_where_impl_struct ["vstd", "-V alloc-check"] => DUP.to_string() + verus_code_str! {
        // in a `where` clause
        fn dup2<T>(x: &T) -> (r: (T, T))
            where T: Clone with { fn clone(&self) -> Self allocates 0; fn drop allocates 0; }
            allocates 0
        {
            (x.clone(), x.clone())
        }

        // on an impl block: every exec and proof method gets it
        pub struct Pair<T> { pub a: T }

        impl<T: Clone with { fn clone(&self) -> Self allocates 0; fn drop allocates 0; }> Pair<T> {
            fn twice(&self) -> (r: (T, T))
                allocates 0
            {
                (self.a.clone(), self.a.clone())
            }
        }

        // on a struct: its inherent impl blocks get it
        pub struct Holder<T: Clone with { fn clone(&self) -> Self allocates 0; fn drop allocates 0; }> { pub a: T }

        impl<T: Clone> Holder<T> {
            fn get(&self) -> (r: T)
                allocates 0
            {
                self.a.clone()
            }
        }

        fn caller(p: &P)
            allocates 0
        {
            let _ = dup2(p);
            let q = Pair { a: P(1) };
            let _ = q.twice();
            let h = Holder { a: P(2) };
            let _ = h.get();
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] with_bound_impl_checked_at_call ["vstd", "-V alloc-check"] => DUP.to_string() + verus_code_str! {
        pub struct Pair<T> { pub a: T }

        impl<T: Clone with { fn clone(&self) -> Self allocates 0; fn drop allocates 0; }> Pair<T> {
            fn twice(&self) -> (r: (T, T))
                allocates 0
            {
                (self.a.clone(), self.a.clone())
            }
        }

        fn caller(v: Vec<u8>)
            allocates 10
        {
            let q = Pair { a: v };
            let _ = q.twice(); // FAILS: Vec::clone allocates
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] with_bound_trait_impl_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        pub trait Tr { fn m(&self); }
        pub struct S<T>(pub T);
        impl<T: Clone with { fn clone(&self) -> Self allocates 0; }> Tr for S<T> {
            fn m(&self) {}
        }
    } => Err(err) => assert_vir_error_msg(err, "not supported on a trait impl")
}

// `fn drop allocates 0;` is the precondition `vstd::alloc_check::bound_drop_alloc_free::<T>()`,
// which may also be written directly in `requires` (e.g. in `#[verus_spec]`, which has no `with`)

const APPLY: &str = verus_code_str! {
    use vstd::prelude::*;

    pub fn apply<F: Fn(&u8) -> bool>(x: u8, f: F) -> (r: bool)
        requires
            vstd::alloc_check::bound_drop_alloc_free::<F>(),
            f.requires((&x,)),
        allocates call_allocations(f, (&x,))
    {
        f(&x)
    }

    pub fn eat<T>(t: T)
        requires
            vstd::alloc_check::bound_drop_alloc_free::<T>(),
        allocates 0
    {
    }

    pub struct Quiet { pub a: u8 }

    pub struct Loud { pub a: u8 }

    #[verifier::external_body]
    fn mk() -> (r: Box<u8>)
        opens_invariants none
        no_unwind
        allocates 1
    {
        Box::new(1)
    }

    impl Drop for Loud {
        fn drop(&mut self)
            opens_invariants none
            no_unwind
            allocates 1
        {
            let _b = mk();
        }
    }
};

test_verify_one_file_with_options! {
    #[test] handwritten_drop_marker_ok ["vstd", "-V alloc-check"] => APPLY.to_string() + verus_code_str! {
        // a closure with an `allocates` bound: its captures are checked (a `Quiet` has no drop glue)
        fn caller_quiet(x: u8, w: Quiet) -> (r: bool) {
            apply(x, move |v: &u8| -> (b: bool) allocates 0 { *v > w.a })
        }

        // a `Copy` closure has no drop glue
        fn caller_copy(x: u8) -> (r: bool) {
            apply(x, |v: &u8| -> (b: bool) { *v > 0 })
        }

        // the precondition fills the rule for dropping a type parameter (no `G: Copy` needed)
        fn forward<G: Fn(&u8) -> bool>(x: u8, g: G) -> (r: bool)
            requires
                vstd::alloc_check::bound_drop_alloc_free::<G>(),
                g.requires((&x,)),
            allocates call_allocations(g, (&x,))
        {
            apply(x, g)
        }

        fn caller_values(q: Quiet)
            allocates 0
        {
            eat(q);
            eat(3u64);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] handwritten_drop_marker_checked_at_call ["vstd", "-V alloc-check"] => APPLY.to_string() + verus_code_str! {
        fn caller(w: Loud) {
            eat(w);
        }
    } => Err(err) => assert_vir_error_msg(err, "its `Drop::drop` is not bounded by `allocates 0`")
}

test_verify_one_file_with_options! {
    #[test] handwritten_drop_marker_type_param_unmarked ["vstd", "-V alloc-check"] => APPLY.to_string() + verus_code_str! {
        fn caller<T>(t: T) {
            eat(t);
        }
    } => Err(err) => assert_vir_error_msg(err, "add the bound `T: vstd::alloc_check::AllocFreeDrop`")
}

test_verify_one_file_with_options! {
    #[test] handwritten_drop_marker_bounded_closure_loud ["vstd", "-V alloc-check"] => APPLY.to_string() + verus_code_str! {
        // (the closure's own bound checks what it captures)
        fn caller(x: u8, w: Loud) -> (r: bool) {
            apply(x, move |v: &u8| -> (b: bool) allocates 0 { *v > w.a })
        }
    } => Err(err) => assert_vir_error_msg(err, "its `Drop::drop` is not bounded by `allocates 0`")
}

test_verify_one_file_with_options! {
    #[test] handwritten_drop_marker_unbounded_closure ["vstd", "-V alloc-check"] => APPLY.to_string() + verus_code_str! {
        // a closure without an `allocates` bound: what it captures is not checked, even in a
        // caller without a bound of its own
        fn caller(x: u8, w: Loud) -> (r: bool) {
            apply(x, move |v: &u8| -> (b: bool) { let r = &w; *v > r.a })
        }
    } => Err(err) => assert_vir_error_msg(err, "only checked for a closure with an `allocates` bound")
}

test_verify_one_file_with_options! {
    #[test] handwritten_drop_marker_unbounded_closure_quiet ["vstd", "-V alloc-check"] => APPLY.to_string() + verus_code_str! {
        // (also when it captures nothing that allocates: the captures are not looked at; `&w`
        // makes the closure capture all of `w`, which is not `Copy`)
        fn caller(x: u8, w: Quiet) -> (r: bool) {
            apply(x, move |v: &u8| -> (b: bool) { let r = &w; *v > r.a })
        }
    } => Err(err) => assert_vir_error_msg(err, "only checked for a closure with an `allocates` bound")
}

test_verify_one_file_with_options! {
    #[test] handwritten_drop_marker_nested_unbounded_closure ["vstd", "-V alloc-check"] => APPLY.to_string() + verus_code_str! {
        fn caller(w: Loud) {
            eat((1u8, Some(move || { let r = &w; r.a > 0 })));
        }
    } => Err(err) => assert_vir_error_msg(err, "only checked for a closure with an `allocates` bound")
}

test_verify_one_file_with_options! {
    #[test] with_bound_drop_unbounded_closure ["vstd", "-V alloc-check"] => APPLY.to_string() + verus_code_str! {
        pub trait Tr {}
        impl<T> Tr for T {}

        fn eat_with<F: Tr with { fn drop allocates 0; }>(f: F)
            allocates 0
        {
        }

        fn caller(w: Loud) {
            eat_with(move || { let r = &w; r.a > 0 });
        }
    } => Err(err) => assert_vir_error_msg(err, "only checked for a closure with an `allocates` bound")
}

test_verify_one_file_with_options! {
    #[test] with_bound_drop_bounded_closure_ok ["vstd", "-V alloc-check"] => APPLY.to_string() + verus_code_str! {
        pub trait Tr {}
        impl<T> Tr for T {}

        fn eat_with<F: Tr with { fn drop allocates 0; }>(f: F)
            allocates 0
        {
        }

        fn caller(w: Quiet) {
            eat_with(move || -> (b: bool) allocates 0 { let r = &w; r.a > 0 });
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] handwritten_drop_marker_without_alloc_check ["vstd"] => verus_code! {
        use vstd::prelude::*;

        pub proof fn need<T>()
            requires
                vstd::alloc_check::bound_drop_alloc_free::<T>(),
        {
        }

        // without -V alloc-check, nothing checks the type at a call, so the precondition is not
        // assumed there (it could otherwise be exported for any type)
        pub proof fn launder<T>()
            ensures
                vstd::alloc_check::bound_drop_alloc_free::<T>(),
        {
            need::<T>(); // FAILS
        }
    } => Err(err) => {
        // (one error, at the call; its other span is the callee)
        assert!(err.errors[0].spans.iter().any(|s| s.text.iter().any(|t| t.text.contains("FAILS"))));
        assert_error_msgs(err, &["which is only checked with -V alloc-check"]);
    }
}

test_verify_one_file_with_options! {
    #[test] handwritten_drop_marker_without_alloc_check_forward ["vstd"] => verus_code! {
        use vstd::prelude::*;

        pub proof fn need<T>()
            requires
                vstd::alloc_check::bound_drop_alloc_free::<T>(),
        {
        }

        pub proof fn forward<T>()
            requires
                vstd::alloc_check::bound_drop_alloc_free::<T>(),
        {
            need::<T>();
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] handwritten_drop_marker_verus_spec_attr ["vstd", "-V alloc-check", "--edition 2024"] => code! {
        use vstd::prelude::*;

        #[verus_verify]
        #[verus_spec(r =>
            requires
                vstd::alloc_check::bound_drop_alloc_free::<F>(),
                !vstd::alloc_check::drop_may_deallocate::<F>(),
                f.requires((&x,)),
            ensures
                f.ensures((&x,), r),
            allocates call_allocations(f, (&x,))
            deallocates call_deallocations(f, (&x,))
        )]
        pub fn test_by<F: Fn(&u8) -> bool>(x: u8, f: F) -> bool {
            f(&x)
        }

        #[verus_verify]
        #[verus_spec(r =>
            requires
                vstd::alloc_check::bound_drop_alloc_free::<F>(),
                f.requires((&x,)),
            allocates call_allocations(f, (&x,))
        )]
        pub fn alloc_only<F: Fn(&u8) -> bool>(x: u8, f: F) -> bool {
            f(&x)
        }

        verus! {
        pub struct Quiet { pub a: u8 }

        pub fn caller_quiet(x: u8, w: Quiet) -> (r: bool) {
            alloc_only(x, move |v: &u8| -> (b: bool) allocates 0 { *v > w.a })
        }

        pub fn caller_copy(x: u8) -> (r: bool) {
            test_by(x, |v: &u8| -> (b: bool) allocates 0 deallocates 0 { *v > 1 })
        }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] drop_marker_bounded_closure_captures_marked_param ["vstd", "-V alloc-check"] => APPLY.to_string() + verus_code_str! {
        pub trait Tr {}
        impl<T> Tr for T {}

        // a closure with a bound may capture a value of a marked type parameter of the function
        // that creates it
        fn wrap<T>(t: T)
            requires
                vstd::alloc_check::bound_drop_alloc_free::<T>(),
        {
            eat(move || -> (b: bool) allocates 0 { let r = &t; true });
        }

        fn wrap_with<T: Tr with { fn drop allocates 0; }>(t: T) {
            eat(move || -> (b: bool) allocates 0 { let r = &t; true });
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] drop_marker_unbounded_closure_captures_marked_param ["vstd", "-V alloc-check"] => APPLY.to_string() + verus_code_str! {
        fn wrap<T>(t: T)
            requires
                vstd::alloc_check::bound_drop_alloc_free::<T>(),
        {
            eat(move || { let r = &t; true });
        }
    } => Err(err) => assert_vir_error_msg(err, "only checked for a closure with an `allocates` bound")
}

test_verify_one_file_with_options! {
    #[test] drop_marker_in_spec_recommends ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        // a spec function's `recommends` are not established anywhere, so the marker in them is
        // not assumed at its recursive call (the termination check must not rely on it)
        pub open spec fn bad<T>() -> int
            recommends
                vstd::alloc_check::bound_drop_alloc_free::<T>(),
            decreases 0int,
        {
            if vstd::alloc_check::bound_drop_alloc_free::<T>() {
                0
            } else {
                bad::<T>() + 1 // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] drop_marker_in_spec_recommends_lemma ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        pub proof fn need<T>()
            requires
                vstd::alloc_check::bound_drop_alloc_free::<T>(),
        {
        }

        pub open spec fn f<T>(n: nat) -> nat
            recommends
                vstd::alloc_check::bound_drop_alloc_free::<T>(),
            decreases n,
        {
            if n == 0 {
                0
            } else {
                proof { need::<T>(); }
                f::<T>((n - 1) as nat)
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "add the bound `T: vstd::alloc_check::AllocFreeDrop`")
}

test_verify_one_file_with_options! {
    #[test] drop_marker_in_spec_recommends_without_alloc_check ["vstd"] => verus_code! {
        use vstd::prelude::*;

        pub open spec fn f<T>(n: nat) -> nat
            recommends
                vstd::alloc_check::bound_drop_alloc_free::<T>(),
            decreases n,
        {
            if n == 0 { 0 } else { f::<T>((n - 1) as nat) }
        }
    } => Ok(())
}
