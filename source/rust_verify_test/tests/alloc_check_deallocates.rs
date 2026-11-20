#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// -V alloc-check, `deallocates d`: the number of deallocations of a function (on a normal
// return), counted like `allocates`; `call_deallocations`/`f.deallocations(x)`,
// `call_deallocates`/`f.deallocates(x)`, `deallocated()`, and the condition forms
// `deallocates_when(d, c)`, `allocates_when(a, c)`

const LEAVES: &str = verus_code_str! {
    use vstd::prelude::*;

    #[verifier::external_body]
    fn free_one(x: u64) allocates 0 deallocates 1 { }

    #[verifier::external_body]
    fn free_if(x: u64) allocates 0 deallocates deallocates_when(1int, x > 5) { }

    #[verifier::external_body]
    fn alloc_if(x: u64) allocates allocates_when(2int, x > 5) deallocates 0 { }

    fn unknown(x: u64) { }

    #[verifier::fip]
    fn fipf() { }
};

test_verify_one_file_with_options! {
    #[test] deallocates_counted ["vstd", "-V alloc-check"] => LEAVES.to_string() + verus_code_str! {
        fn two(x: u64) deallocates 2 { free_one(x); free_one(x); }

        fn loopy(n: u64) deallocates n {
            let mut i: u64 = 0;
            while i < n
                invariant i <= n, deallocated() == i,
                decreases n - i,
            {
                free_one(i);
                i = i + 1;
            }
        }

        fn cond_ok() deallocates 0 { free_if(3); }
        fn fip_callee() deallocates 0 { fipf(); }
        #[verifier::fip] fn fip_calls_cond() { free_if(3); }

        // (a verified body may state a condition form: it is counted against `if c { d } else { 0 }`)
        fn verified_cond(x: u64) deallocates deallocates_when(1int, x > 5) {
            if x > 5 { free_one(x); }
        }

        proof fn values() {
            assert(free_one.deallocations(3u64) == 1);
            assert(free_one.deallocates(3u64));
            assert(!free_if.deallocates(3u64));
            assert(free_if.deallocations(9u64) == 1);
            assert(!alloc_if.allocates(3u64));
            assert(alloc_if.allocations(9u64) == 2);
            assert(alloc_if.allocations(3u64) == 0);
            assert(fipf.deallocations() == 0);
        }

        fn generic<F: Fn(u64)>(f: &F)
            requires f.requires((1u64,)), !f.deallocates(1u64),
            deallocates 0
        {
            f(1)
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] deallocates_counted_fail ["vstd", "-V alloc-check"] => LEAVES.to_string() + verus_code_str! {
        fn too_many(x: u64) deallocates 1 { free_one(x); free_one(x); } // FAILS
        fn cond_true() deallocates 0 { free_if(9); } // FAILS
        fn verified_cond_bad(x: u64) deallocates deallocates_when(1int, x > 5) { free_one(x); } // FAILS

        fn after() {}
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file_with_options! {
    #[test] deallocates_callee_without_bound ["vstd", "-V alloc-check"] => LEAVES.to_string() + verus_code_str! {
        fn f(x: u64) deallocates 1 { unknown(x); }
    } => Err(err) => assert_vir_error_msg(err, "cannot bound the deallocations of this call")
}

test_verify_one_file_with_options! {
    #[test] deallocates_implicit_drop_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        fn f(b: Box<u64>) deallocates 5 { }
    } => Err(err) => assert_vir_error_msg(err, "the implicit drops of a function with a `deallocates` bound must not deallocate")
}

test_verify_one_file_with_options! {
    #[test] deallocates_implicit_drop_inherited_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        trait T { fn m(&self, b: Box<u64>) deallocates 1; }
        struct S;
        impl T for S { fn m(&self, b: Box<u64>) { } }
    } => Err(err) => assert_vir_error_msg(err, "the implicit drops of a function with a `deallocates` bound must not deallocate")
}

test_verify_one_file_with_options! {
    #[test] deallocates_trait_contract ["vstd", "-V alloc-check"] => LEAVES.to_string() + verus_code_str! {
        trait T { fn m(&self, x: u64) deallocates 1; }
        struct S;
        impl T for S { fn m(&self, x: u64) { free_one(x); } }
        fn g<X: T>(x: &X) deallocates 1 { x.m(3) }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] deallocates_trait_contract_fail ["vstd", "-V alloc-check"] => LEAVES.to_string() + verus_code_str! {
        trait T { fn m(&self, x: u64) deallocates 1; } // FAILS (the declaration's bound)
        struct S;
        impl T for S { fn m(&self, x: u64) { free_one(x); free_one(x); } }

        fn after() {}
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] deallocates_not_with_fip ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::fip] fn f() deallocates 0 { }
    } => Err(err) => assert_vir_error_msg(err, "cannot state `deallocates`")
}

test_verify_one_file_with_options! {
    #[test] deallocates_closure_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        fn f() { let c = |x: u64| -> (r: u64) deallocates 0 { x }; }
    } => Err(err) => assert_vir_error_msg(err, "a closure cannot have a `deallocates` bound yet")
}

test_verify_one_file_with_options! {
    #[test] deallocates_encapsulates_counts_d ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        pub struct Pool { pub n: u64 }
        impl Pool {
            fn free(&mut self) encapsulates alloc(0, 2) { }
        }
        fn f(p: &mut Pool) deallocates 4 { p.free(); p.free(); }
        fn g(p: &mut Pool) deallocates 3 { p.free(); p.free(); } // FAILS

        fn after() {}
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] deallocates_raw_ptr_leaf ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::raw_ptr::*;
        fn f(p: *mut u8, Tracked(pt): Tracked<PointsToRaw>, Tracked(d): Tracked<Dealloc>)
            requires
                d.addr() == p.addr(), d.size() == 8, d.align() == 8,
                d.provenance() == pt.provenance(),
                pt.is_range(d.addr() as int, 8),
                p@.provenance == d.provenance(),
            deallocates 1
        {
            deallocate(p, 8, 8, Tracked(pt), Tracked(d));
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] deallocates_encapsulates_impl_within_decl ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        trait T { fn m(&mut self) deallocates 1; }
        struct S;
        impl T for S { fn m(&mut self) encapsulates alloc(0, 1) { } }
        struct U;
        impl T for U { fn m(&mut self) encapsulates alloc(0, 2) { } }
    } => Err(err) => assert_vir_error_msg(err, "may count more deallocations than the trait method's")
}

// the vstd specifications state their deallocations (S2b)
const STD_CALLS: &str = verus_code_str! {
    use vstd::prelude::*;
    use std::sync::atomic::{AtomicU64, Ordering};

    fn unwrap_u64(o: Option<u64>) -> (r: u64) deallocates 0 { o.unwrap_or(3) }

    fn unwrap_box(o: Option<Box<u64>>, d: Box<u64>) -> (r: Box<u64>)
        deallocates vstd::alloc_check::drop_deallocations(d)
    {
        o.unwrap_or(d)
    }

    fn unwrap_box_some(o: Option<Box<u64>>) -> (r: Box<u64>)
        requires o.is_none(),
        deallocates 0
    {
        o.unwrap_or(Box::new(3))
    }

    fn push_str(s: &mut String) deallocates 1 { s.push_str("a"); }

    fn atomic(a: &AtomicU64) -> (r: u64) deallocates 0 {
        a.store(1, Ordering::SeqCst);
        a.load(Ordering::SeqCst)
    }

    fn insert_u64(o: &mut Option<u64>) deallocates 0 { let _ = o.insert(3); }
};

test_verify_one_file_with_options! {
    #[test] deallocates_std_specs ["vstd", "-V alloc-check"] => STD_CALLS.to_string() => Ok(())
}

test_verify_one_file_with_options! {
    #[test] deallocates_std_specs_fail ["vstd", "-V alloc-check"] => STD_CALLS.to_string() + verus_code_str! {
        fn unwrap_box_bad(o: Option<Box<u64>>, d: Box<u64>) -> (r: Box<u64>) deallocates 0 { o.unwrap_or(d) } // FAILS
        fn push_str_bad(s: &mut String) deallocates 0 { s.push_str("a"); } // FAILS
        fn insert_box_bad(o: &mut Option<Box<u64>>) deallocates 0 { let _ = o.insert(Box::new(3)); } // FAILS

        fn after() {}
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file_with_options! {
    #[test] deallocates_std_spec_unbounded ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use std::collections::HashMap;
        fn f(m: &mut HashMap<u64, u64>) deallocates 1 { m.insert(1, 2); }
    } => Err(err) => assert_vir_error_msg(err, "cannot bound the deallocations of this call")
}
