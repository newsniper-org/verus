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

// (review findings) an allocator type's drop is not free in general: `Box`, `Rc` and `Arc`
// implement `Allocator` by forwarding, and dropping them frees the program's block
test_verify_one_file_with_options! {
    #[test] deallocates_allocator_drop_not_free ["vstd", "-V alloc-check"] => verus_code_str! {
        use vstd::prelude::*;
        proof fn no_contradiction(b: Box<&'static std::alloc::System>) ensures false { // FAILS
            assert(vstd::alloc_check::drop_deallocations(b) >= 0);
        }
        fn consume<A: std::alloc::Allocator>(a: A) deallocates 0 { } // FAILS
        fn consume_global(a: std::alloc::Global) deallocates 0 { }

        fn after() {}
    }.to_string() => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] deallocates_or_pattern_moves ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        fn pick(t: (bool, Box<u64>, Box<u64>, Box<u64>)) -> (r: Box<u64>) deallocates 2 {
            match t {
                (true, x, _, _) | (false, _, x, _) => x,
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus cannot count the drops after an or-pattern whose alternatives move different parts of a value yet")
}

test_verify_one_file_with_options! {
    #[test] deallocates_or_pattern_variants ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        enum E { A(Box<u64>), B(Box<u64>), C }
        fn take(e: E) -> (r: Option<Box<u64>>) deallocates 0 {
            match e {
                E::A(x) | E::B(x) => Some(x),
                E::C => None,
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] deallocates_async_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        async fn f(b: Box<Box<u64>>) -> (r: Box<u64>) deallocates 0 { *b }
    } => Err(err) => assert_vir_error_msg(err, "an async function cannot be `#[verifier::fip]` or have a `deallocates` bound yet")
}

// (portable-fip 2026-11-20) a function whose only counted drop is an overwritten value: one per
// crate, since another function's drops used to keep `drop_deallocations` from being pruned
test_verify_one_file_with_options! {
    #[test] deallocates_only_overwrite_deref ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        pub fn f(r: &mut Box<u64>) deallocates 1 { *r = Box::new(1); }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] deallocates_only_overwrite_option ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        pub fn f(o: &mut Option<Box<u64>>) deallocates 1 { *o = None; }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] deallocates_only_overwrite_copy ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        pub fn f(r: &mut u64) deallocates 0 { *r = 1; }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] deallocates_only_overwrite_field ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        pub struct S { pub b: Box<u64> }
        pub fn f(s: &mut S) deallocates 1 { s.b = Box::new(2); }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] deallocates_only_overwrite_vec_element ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        pub fn f(v: &mut Vec<Box<u64>>) requires old(v)@.len() > 0, deallocates 1 {
            let r = &mut v[0];
            *r = Box::new(1);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] deallocates_only_overwrite_vec_set ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        pub fn f(v: &mut Vec<Box<u64>>) requires old(v)@.len() > 0, deallocates 1 {
            v.set(0, Box::new(1));
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] deallocates_only_overwrite_index_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        pub fn f(v: &mut Vec<Box<u64>>) requires old(v)@.len() > 0, deallocates 1 {
            v[0] = Box::new(1);
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus cannot count this drop of a value of type")
}

test_verify_one_file_with_options! {
    #[test] deallocates_only_overwrite_fails ["vstd", "-V alloc-check"] => verus_code_str! {
        use vstd::prelude::*;
        pub fn f1(r: &mut Box<u64>) deallocates 0 { *r = Box::new(1); } // FAILS
        pub fn f2(o: &mut Option<Box<u64>>) requires old(o).is_some(), deallocates 0 { *o = None; } // FAILS
        pub struct S { pub b: Box<u64> }
        pub fn f3(s: &mut S) deallocates 0 { s.b = Box::new(2); } // FAILS
        pub fn f4(v: &mut Vec<Box<u64>>) requires old(v)@.len() > 0, deallocates 0 { // FAILS
            let r = &mut v[0];
            *r = Box::new(1);
        }
        pub fn f5(v: &mut Vec<Box<u64>>) requires old(v)@.len() > 0, deallocates 0 { // FAILS
            v.set(0, Box::new(1));
        }

        fn after() {}
    }.to_string() => Err(err) => assert_fails(err, 5)
}

test_verify_one_file_with_options! {
    #[test] deallocates_mem_drop ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        pub fn f(b: Box<u64>) deallocates 1 { drop(b); }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] deallocates_mem_drop_bounds ["vstd", "-V alloc-check"] => verus_code_str! {
        use vstd::prelude::*;
        pub fn g<T>(x: T) deallocates vstd::alloc_check::drop_deallocations(x) { drop(x); }
        pub fn k(b: Box<Box<u64>>) deallocates 2 { core::mem::drop(b); }
        pub fn h(b: Box<u64>) deallocates 0 { drop(b); } // FAILS
        pub fn k1(b: Box<Box<u64>>) deallocates 1 { drop(b); } // FAILS

        fn after() {}
    }.to_string() => Err(err) => assert_fails(err, 2)
}

// `for` loops (portable-fip, 2026-11-22): `Iterator::next` is bounded by
// `iter_next_deallocations`, which vstd states 0 for std's iterators whose `next` frees nothing
// (as `allocates`, a loop keeps the counter in its invariant)
test_verify_one_file_with_options! {
    #[test] deallocates_for_loops ["vstd", "-V alloc-check", "--no-cheating"] => verus_code! {
        use vstd::prelude::*;

        pub fn range(n: u64) deallocates 0 {
            for i in 0..n
                invariant deallocated() == 0,
            {
            }
        }

        pub fn range_inclusive(n: u64) deallocates 0 {
            for i in 0..=n
                invariant deallocated() == 0,
            {
            }
        }

        pub fn slice(s: &[u64]) -> (r: u64) allocates 0 deallocates 0 {
            let mut r = 0u64;
            for x in s.iter()
                invariant allocated() == 0, deallocated() == 0,
            {
                r = *x;
            }
            r
        }

        pub fn vec_ref(v: &Vec<u64>) deallocates 0 {
            for x in v
                invariant deallocated() == 0,
            {
            }
        }

        pub fn slice_mut(s: &mut [u64]) deallocates 0 {
            for x in s.iter_mut()
                invariant deallocated() == 0,
            {
            }
        }

        pub fn next_direct(n: u64, s: &[u64]) -> (r: Option<u64>) deallocates 0 {
            let mut it = s.iter();
            let _ = it.next();
            let mut r = 0..n;
            r.next()
        }

        // (in a loop that frees, the invariant states what it frees)
        pub fn frees(n: u64) deallocates n {
            for i in 0..n
                invariant deallocated() == i,
            {
                let b = Box::new(i);
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] deallocates_for_loops_fail ["vstd", "-V alloc-check"] => verus_code_str! {
        use vstd::prelude::*;

        // (without the counter in the invariant, the loop forgets it)
        pub fn no_invariant(n: u64) deallocates 0 { // FAILS
            for i in 0..n {
            }
        }

        // (an owning iterator frees its buffer when it is dropped)
        pub fn owning(v: Vec<u64>) deallocates 0 { // FAILS
            for x in v
                invariant deallocated() == 0,
            {
            }
        }

        fn after() {}
    }.to_string() => Err(err) => assert_fails(err, 2)
}

// integer, `bool` and `char` `min`/`max`/`clamp` (impl items of core since Rust 1.100) and the
// `bool`/`char` comparisons (portable-fip, 2026-11-22)
test_verify_one_file_with_options! {
    #[test] deallocates_ord_methods ["vstd", "-V alloc-check", "--no-cheating"] => verus_code! {
        use vstd::prelude::*;

        pub fn f1(a: usize, b: usize) -> (r: usize)
            ensures r == (if a <= b { a } else { b }),
            allocates 0
        {
            a.min(b)
        }

        pub fn f2(a: i32, b: i32) -> (r: i32)
            ensures r >= a && r >= b,
            deallocates 0
        {
            a.max(b)
        }

        #[verifier::fip]
        pub fn f3(a: usize, b: usize, c: usize) -> (r: usize)
            requires b <= c,
        {
            a.clamp(b, c)
        }

        #[verifier::fip(strict)]
        pub fn f4(a: u8, b: u8) -> (r: u8) {
            a.max(b)
        }

        #[verifier::fip]
        pub fn f5(a: bool, b: bool, c: char, d: char) -> (r: (bool, bool, char)) {
            (a.min(b), c.lt(&d), c.max(d))
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] deallocates_ord_clamp_requires ["vstd", "-V alloc-check"] => verus_code_str! {
        use vstd::prelude::*;

        // (core panics unless `min <= max`)
        #[verifier::fip]
        pub fn f(a: usize, b: usize, c: usize) -> (r: usize) {
            a.clamp(b, c) // FAILS
        }

        fn after() {}
    }.to_string() => Err(err) => assert_one_fails(err)
}

// closures (portable-fip, 2026-11-22): `drop_deallocations` of a closure without drop glue, and
// of a function item, is 0; a function that takes a closure by value counts its drop
test_verify_one_file_with_options! {
    #[test] deallocates_closure_drops ["vstd", "-V alloc-check", "--no-cheating"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        pub fn b1(o: Option<u64>) -> (r: Option<u64>) deallocates 0 {
            o.map(|x: u64| -> (y: u64) deallocates 0 { x })
        }

        pub fn b3(o: Option<u64>) -> (r: u64) deallocates 0 {
            o.unwrap_or_else(|| -> (y: u64) deallocates 0 { 0 })
        }

        pub fn captures_ref(o: Option<u64>, k: &u64) -> (r: Option<u64>) deallocates 0 {
            o.map(|x: u64| -> (y: u64) deallocates 0 { *k })
        }

        pub fn captures_copy(o: Option<u64>, k: u64) -> (r: Option<u64>) deallocates 0 {
            let g = move |x: u64| -> (y: u64) deallocates 0 { k };
            o.map(g)
        }

        #[verifier::fip]
        pub fn id(x: u64) -> (y: u64) {
            x
        }

        pub fn fn_item(o: Option<u64>) -> (r: Option<u64>) deallocates 0 {
            o.map(id)
        }

        // (a let-bound closure is called through a reference: it is not dropped by the call)
        pub fn direct() -> (r: u64) deallocates 0 {
            let c = |x: u64| -> (y: u64) deallocates 0 { x };
            let a = c(1);
            let _ = c(2);
            a
        }

        pub fn apply<F: FnOnce(u64) -> u64>(f: F, x: u64) -> (r: u64)
            requires f.requires((x,)),
            deallocates f.deallocations(x) + drop_deallocations(f),
        {
            f(x)
        }

        pub fn use_apply() -> (r: u64) deallocates 0 {
            let c = |x: u64| -> (y: u64) deallocates 0 { x };
            apply(c, 1)
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] deallocates_closure_drops_counted ["vstd", "-V alloc-check"] => verus_code_str! {
        use vstd::prelude::*;

        // (an `Fn` closure called through `FnOnce` runs its body, then drops itself)
        pub fn apply<F: FnOnce(u64) -> u64>(f: F, x: u64) -> (r: u64)
            requires f.requires((x,)),
            deallocates f.deallocations(x), // FAILS
        {
            f(x)
        }

        // (the drop of a closure that owns a box is not defined yet)
        pub fn owns_box(o: Option<u64>, b: Box<u64>) -> (r: Option<u64>)
            requires o is Some,
            deallocates 1, // FAILS
        {
            let c = move |x: u64| -> (y: u64) deallocates 0 { *b };
            o.map(c)
        }

        fn after() {}
    }.to_string() => Err(err) => assert_fails(err, 2)
}

// the scrutinee of a `match` or `if let` that an arm moves out of is counted with a drop flag,
// like a local (portable-fip, 2026-11-22)
test_verify_one_file_with_options! {
    #[test] deallocates_match_scrutinee ["vstd", "-V alloc-check", "--no-cheating"] => verus_code! {
        use vstd::prelude::*;

        pub fn consume(b: Box<u64>) deallocates 1 { }

        pub fn if_let(v: &mut Vec<Box<u64>>) deallocates 1 {
            if let Some(x) = v.pop() { consume(x); }
        }

        pub fn match_(v: &mut Vec<Box<u64>>) deallocates 1 {
            match v.pop() { Some(x) => consume(x), None => {} }
        }

        pub fn take(o: &mut Option<Box<u64>>) deallocates 1 {
            if let Some(x) = o.take() { consume(x); }
        }

        pub fn else_(v: &mut Vec<Box<u64>>) deallocates 1 {
            if let Some(x) = v.pop() { consume(x); } else { }
        }

        pub fn guard(v: &mut Vec<Box<u64>>) deallocates 1 {
            match v.pop() { Some(x) if *x > 0 => consume(x), _ => {} }
        }

        // (a `Some((b, false))` is dropped whole)
        pub fn residue(v: &mut Vec<(Box<u64>, bool)>) deallocates 1 {
            if let Some((x, true)) = v.pop() { consume(x); }
        }

        pub fn ret(v: &mut Vec<Box<u64>>) -> (r: u64) deallocates 1 {
            match v.pop() { Some(x) => { consume(x); return 1; } None => {} }
            0
        }

        pub fn else_if(v: &mut Vec<Box<u64>>, w: &mut Vec<Box<u64>>) deallocates 1 {
            if let Some(x) = v.pop() { consume(x); } else if let Some(y) = w.pop() { consume(y); }
        }

        pub fn in_loop(v: &mut Vec<Box<u64>>, n: u64) deallocates n {
            let mut i = 0;
            while i < n
                invariant i <= n, deallocated() <= i,
                decreases n - i,
            {
                match v.pop() { Some(x) => consume(x), None => {} }
                i = i + 1;
            }
        }

        pub fn while_let_residue(v: &mut Vec<(Box<u64>, Box<u64>)>)
            requires old(v)@.len() <= 100,
            deallocates 200
        {
            while let Some((x, _)) = v.pop()
                invariant_except_break deallocated() + 2 * v@.len() <= 200,
                ensures deallocated() <= 200,
                decreases v@.len(),
            {
                consume(x);
            }
        }

        pub fn in_closure(v: &mut Vec<Box<u64>>) deallocates 1 {
            let f = |w: &mut Vec<Box<u64>>| deallocates 1 { if let Some(x) = w.pop() { consume(x); } };
            f(v);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] deallocates_match_scrutinee_fails ["vstd", "-V alloc-check"] => verus_code_str! {
        use vstd::prelude::*;

        pub fn consume(b: Box<u64>) deallocates 1 { }

        pub fn if_let(v: &mut Vec<Box<u64>>) deallocates 0 { // FAILS
            if let Some(x) = v.pop() { consume(x); }
        }

        pub fn residue(v: &mut Vec<(Box<u64>, bool)>) deallocates 0 { // FAILS
            if let Some((x, true)) = v.pop() { consume(x); }
        }

        // (the second box is dropped on the matching path too)
        pub fn residue2(v: &mut Vec<(Box<u64>, Box<u64>)>) deallocates 1 { // FAILS
            if let Some((x, _)) = v.pop() { consume(x); }
        }

        pub fn guard(v: &mut Vec<Box<u64>>) deallocates 0 { // FAILS
            match v.pop() { Some(x) if *x > 0 => consume(x), _ => {} }
        }

        fn after() {}
    }.to_string() => Err(err) => assert_fails(err, 4)
}

// A `#[verus_spec(with ..)]` function `f` is verified as its twin `_VERUS_VERIFIED_f`, whose body
// the erase compile replaces: the drops of the compiled `f` are the ones checked against those
// Verus counted (a `Box` whose contents are moved out of it is freed, which is not counted yet)
test_verify_one_file_with_options! {
    #[test] deallocates_verus_spec_with_checked ["vstd", "-V alloc-check"] => code! {
        use vstd::prelude::*;

        #[verus_spec(
            with Ghost(w): Ghost<u32>
            deallocates 1
        )]
        pub fn h(b: Box<u64>) {
        }

        #[verus_spec(ret =>
            with Ghost(w): Ghost<u32>
            deallocates 0
        )]
        pub fn f(b: Box<Box<u64>>) -> Box<u64> {
            *b
        }
    } => Err(err) => assert_vir_error_msg(err, "a `Box` whose contents were moved out of it is freed here")
}
