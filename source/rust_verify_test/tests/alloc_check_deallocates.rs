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

// the implicit drops are counted (S3)
test_verify_one_file_with_options! {
    #[test] deallocates_implicit_drop_counted ["vstd", "-V alloc-check"] => verus_code_str! {
        use vstd::prelude::*;
        fn f(b: Box<u64>) deallocates 1 { }
        fn g(b: Box<u64>) deallocates 0 { } // FAILS

        fn after() {}
    }.to_string() => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] deallocates_implicit_drop_inherited_counted ["vstd", "-V alloc-check"] => verus_code_str! {
        use vstd::prelude::*;
        trait T { fn m(&self, b: Box<u64>) deallocates 1; }
        struct S;
        impl T for S { fn m(&self, b: Box<u64>) { } }
        trait U { fn m(&self, b: Box<u64>) deallocates 0; } // FAILS
        impl U for S { fn m(&self, b: Box<u64>) { } }
    }.to_string() => Err(err) => assert_fails(err, 1)
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
    #[test] deallocates_closure_fip_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        fn f() { let c = #[verifier::fip] |x: u64| -> (r: u64) deallocates 0 { x }; }
    } => Err(err) => assert_vir_error_msg(err, "a `#[verifier::fip]` closure deallocates nothing: it cannot state `deallocates`")
}

// a closure with a `deallocates` bound counts its deallocations (implicit drops included), and a
// call of it charges them
const CLOSURES: &str = verus_code_str! {
    use vstd::prelude::*;

    fn call_it() deallocates 1 {
        let f = |b: Box<u64>| -> (r: u64) deallocates 1 { *b };
        let y = f(Box::new(3));
    }

    fn local_in_closure() deallocates 2 {
        let f = |x: u64| -> (r: u64) deallocates 1 { let b = Box::new(x); 0 };
        let y = f(3);
        let z = f(4);
    }

    fn temps() deallocates 2 {
        let f = |b: Box<u64>| -> (r: u64) deallocates 2 { let _ = Box::new(1u64); *b };
        let y = f(Box::new(3));
    }

    fn unbounded_outer(x: u64) {
        let f = |b: Box<u64>| -> (r: u64) deallocates 1 { *b };
    }

    fn generic<F: Fn(Box<u64>) -> u64>(f: &F)
        requires
            forall|b: Box<u64>| f.requires((b,)),
            forall|b: Box<u64>| f.deallocations(b) <= 1,
        deallocates 1
    {
        let y = f(Box::new(3));
    }

    fn use_generic() deallocates 1 {
        let f = |b: Box<u64>| -> (r: u64) deallocates 1 { *b };
        generic(&f);
    }
};

test_verify_one_file_with_options! {
    #[test] deallocates_closure ["vstd", "-V alloc-check"] => CLOSURES.to_string() => Ok(())
}

test_verify_one_file_with_options! {
    #[test] deallocates_closure_fail ["vstd", "-V alloc-check"] => CLOSURES.to_string() + verus_code_str! {
        fn tight(x: u64) {
            let f = |b: Box<u64>| -> (r: u64) deallocates 0 { *b }; // FAILS
        }
        fn caller_too_small() deallocates 0 { // FAILS
            let f = |b: Box<u64>| -> (r: u64) deallocates 1 { *b };
            let y = f(Box::new(3));
        }

        fn after() {}
    } => Err(err) => assert_fails(err, 2)
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

// S3: the implicit drops are counted
const DROPS: &str = verus_code_str! {
    use vstd::prelude::*;

    fn consume(b: Box<u64>) deallocates 1 { }

    // a parameter is dropped at the end of the body
    fn drop_param(b: Box<u64>) deallocates 1 { }

    // a moved value is not dropped
    fn pass_param(b: Box<u64>) -> (r: Box<u64>) deallocates 0 { b }

    // a local is dropped at the end of its block
    fn drop_local() deallocates 1 { let b = Box::new(3u64); }

    fn drop_vec() deallocates 1 {
        let mut v: Vec<u64> = Vec::new();
        v.push(1);
    }

    // moved on one path only (a drop flag)
    fn cond_move(b: Box<u64>, c: bool) -> (r: Option<Box<u64>>)
        deallocates deallocates_when(1int, !c)
    {
        if c { Some(b) } else { None }
    }

    // a match that moves the payload
    fn match_move(o: Option<Box<u64>>) deallocates 1 {
        match o {
            Some(b) => consume(b),
            None => {}
        }
    }

    // an early return drops what is in scope
    fn early(b: Box<u64>, c: bool) deallocates 1 {
        if c {
            return;
        }
        let x = 1u64;
    }

    // every iteration drops its locals
    fn per_iteration(n: u64) deallocates n {
        let mut i: u64 = 0;
        while i < n
            invariant i <= n, deallocated() == i,
            decreases n - i,
        {
            let b = Box::new(i);
            i = i + 1;
        }
    }

    // an assignment drops the old value
    fn overwrite_local() deallocates 2 {
        let mut b = Box::new(1u64);
        b = Box::new(2u64);
    }

    fn overwrite_through_ref(o: &mut Option<Box<u64>>) deallocates 1 { *o = None; }

    // an unused result is dropped at the end of its statement
    fn unused_result() deallocates 1 { let _ = Box::new(3u64); }

    // a value whose drop frees nothing
    fn no_dealloc(x: Option<u64>, p: (u64, bool)) deallocates 0 { }
};

test_verify_one_file_with_options! {
    #[test] deallocates_drops ["vstd", "-V alloc-check"] => DROPS.to_string() => Ok(())
}

// each of these bounds is one too small
test_verify_one_file_with_options! {
    #[test] deallocates_drops_fail ["vstd", "-V alloc-check"] => verus_code_str! {
        use vstd::prelude::*;
        fn consume(b: Box<u64>) deallocates 1 { }
        fn drop_param(b: Box<u64>) deallocates 0 { } // FAILS
        fn drop_local() deallocates 0 { let b = Box::new(3u64); } // FAILS
        fn drop_vec() deallocates 0 { // FAILS
            let mut v: Vec<u64> = Vec::new();
            v.push(1);
        }
        fn cond_move(b: Box<u64>, c: bool) -> (r: Option<Box<u64>>) deallocates 0 { // FAILS
            if c { Some(b) } else { None }
        }
        fn match_move(o: Option<Box<u64>>) deallocates 0 { // FAILS
            match o {
                Some(b) => consume(b),
                None => {}
            }
        }
        fn early(b: Box<u64>, c: bool) -> (r: Option<Box<u64>>) deallocates 0 { // FAILS
            if c {
                return None; // FAILS
            }
            Some(b)
        }
        fn per_iteration(n: u64) deallocates n {
            let mut i: u64 = 0;
            while i < n
                invariant i <= n, deallocated() == 0, // FAILS
                decreases n - i,
            {
                let b = Box::new(i);
                i = i + 1;
            }
        }
        fn overwrite_local() deallocates 1 { // FAILS
            let mut b = Box::new(1u64);
            b = Box::new(2u64);
        }
        fn overwrite_through_ref(o: &mut Option<Box<u64>>) deallocates 0 { *o = None; } // FAILS
        fn unused_result() deallocates 0 { let _ = Box::new(3u64); } // FAILS
        fn brk(n: u64) deallocates 0 { // FAILS
            loop
                invariant_except_break deallocated() == 0,
                decreases 1u64,
            {
                let b = Box::new(n);
                break;
            }
        }

        fn after() {}
    }.to_string() => Err(err) => assert_fails(err, 11)
}

// a drop that Verus does not count yet is an error (checked on the compiled program)
// a temporary is dropped at the end of its statement, or of a condition, a branch of an `if`, a
// loop's condition or body (every iteration), a match arm or guard
const TEMP_SCOPES: &str = verus_code_str! {
    use vstd::prelude::*;
    fn mk() -> (r: Box<u64>) deallocates 0 { Box::new(1) }
    fn look(b: &Box<u64>) -> (r: u64) ensures r == 0 deallocates 0 { 0 }
    fn see(b: &Box<u64>) deallocates 0 { }

    fn body_tail(n: u64) deallocates n {
        let mut i: u64 = 0;
        while i < n
            invariant i <= n, deallocated() == i,
            decreases n - i,
        {
            i = i + 1;
            see(&mk())
        };
    }

    fn loop_condition() deallocates 4 {
        let mut i: u64 = 0;
        while look(&mk()) + i < 3
            invariant i <= 3, deallocated() == i,
            decreases 3 - i,
        {
            i = i + 1;
        }
    }

    fn if_condition_and_branch(c: bool) deallocates 3 {
        if look(&mk()) == 0 { look(&mk()); }
        if c { look(&mk()) } else { 0 };
    }

    fn arm(o: Option<u64>) deallocates 1 {
        match o {
            Some(x) => { see(&mk()) }
            None => {}
        }
    }
};

test_verify_one_file_with_options! {
    #[test] deallocates_drop_temporary_scopes ["vstd", "-V alloc-check"] => TEMP_SCOPES.to_string() => Ok(())
}

test_verify_one_file_with_options! {
    #[test] deallocates_drop_temporary_scopes_fail ["vstd", "-V alloc-check"] => TEMP_SCOPES.to_string() + verus_code_str! {
        fn body_tail_bad(n: u64) deallocates n {
            let mut i: u64 = 0;
            while i < n
                invariant i <= n, deallocated() == 0, // FAILS
                decreases n - i,
            {
                i = i + 1;
                see(&mk())
            };
        }
        fn loop_condition_bad() deallocates 3 { // FAILS
            let mut i: u64 = 0;
            while look(&mk()) + i < 3
                invariant i <= 3, deallocated() == i,
                decreases 3 - i,
            {
                i = i + 1;
            }
        }

        fn after() {}
    } => Err(err) => assert_fails(err, 2)
}

// a drop that Verus does not count yet is an error (checked on the compiled program)
test_verify_one_file_with_options! {
    #[test] deallocates_drop_logical_operand_temporary ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        fn mk() -> (r: Box<u64>) deallocates 0 { Box::new(1) }
        fn look(b: &Box<u64>) -> (r: u64) ensures r == 0 deallocates 0 { 0 }
        fn f() deallocates 100 {
            let mut i: u64 = 0;
            while look(&mk()) < 1 && i < 3
                invariant i <= 3, deallocated() <= i + 1,
                decreases 3 - i,
            {
                i = i + 1;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus cannot count this drop of a value of type `std::boxed::Box<u64>` yet")
}

test_verify_one_file_with_options! {
    #[test] deallocates_drop_extended_temporary ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        fn mk() -> (r: Box<u64>) deallocates 0 { Box::new(1) }
        fn f() deallocates 1 { let r = &mk(); }
    } => Err(err) => assert_vir_error_msg(err, "Verus cannot count this drop of a value of type `std::boxed::Box<u64>` yet")
}

test_verify_one_file_with_options! {
    #[test] deallocates_drop_box_moved_out ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        fn f(b: Box<Box<u64>>) -> (r: Box<u64>) deallocates 1 { *b }
    } => Err(err) => assert_vir_error_msg(err, "a `Box` whose contents were moved out of it is freed here")
}

test_verify_one_file_with_options! {
    #[test] deallocates_drop_move_closure ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        // (a closure that moves nothing into itself has no drop glue; a `move` closure that only
        // reads its capture does, which Verus does not count yet)
        fn no_capture(b: Box<u64>) deallocates 1 {
            let f = |x: u64| -> (r: u64) requires x < 100 { x + 1 };
        }
        fn move_read(b: Box<u64>) deallocates 1 {
            let f = move |x: u64| -> (r: u64) requires x < 100 && *b < 100 { x + *b };
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus cannot count this drop of a value of type `{closure")
}

test_verify_one_file_with_options! {
    #[test] deallocates_drops_more ["vstd", "-V alloc-check"] => verus_code_str! {
        use vstd::prelude::*;
        fn mk() -> (r: Box<u64>) deallocates 0 { Box::new(1) }

        // a partial move drops the rest
        fn partial() -> (r: Box<u64>) deallocates 1 {
            let p = (mk(), mk());
            p.0
        }
        fn partial_fail() -> (r: Box<u64>) deallocates 0 { // FAILS
            let p = (mk(), mk());
            p.0
        }

        // a generic value
        fn generic<T>(x: T) deallocates vstd::alloc_check::drop_deallocations(x) { }
        fn generic_fail<T>(x: T) deallocates 0 { } // FAILS
        fn no_dealloc_generic<T: vstd::alloc_check::NoDeallocDrop>(x: T) deallocates 0 { }

        // `?` returns early
        fn question(o: Option<Box<u64>>, b: Box<u64>) -> (r: Option<u64>) deallocates 2 {
            let x = o?;
            Some(*x)
        }

        // `continue` leaves the loop body
        fn cont(n: u64) deallocates n {
            let mut i: u64 = 0;
            while i < n
                invariant i <= n, deallocated() == i,
                decreases n - i,
            {
                let b = mk();
                i = i + 1;
                if i % 2 == 0 { continue; }
            }
        }
    }.to_string() => Err(err) => assert_fails(err, 2)
}
