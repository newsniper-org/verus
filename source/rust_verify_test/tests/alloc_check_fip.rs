#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// -V alloc-check, `#[verifier::fip]` (fully in-place, FP²): a fip function never deallocates on a
// normal return. Its calls are checked by the verifier (`deallocates_when` conditions of the
// callees); the drops that the compiler inserts, on the MIR of the compiled program.

test_verify_one_file_with_options! {
    #[test] fip_in_place_code_accepted ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::{AllocFreeDrop, NoDeallocDrop};
        use vstd::std_specs::vec::spec_vec_capacity;

        pub struct Node { pub val: u64, pub next: Option<Box<Node>> }

        // reuses the box
        #[verifier::fip]
        fn halve(mut b: Box<Node>) -> (r: Box<Node>) {
            b.val = b.val / 2;
            b
        }

        // a match that moves the box out of the `Some` and builds a new `Some` around it
        #[verifier::fip]
        fn halve_opt(o: Option<Box<Node>>) -> (r: Option<Box<Node>>) {
            match o {
                Some(b) => Some(halve(b)),
                None => None,
            }
        }

        // a push into spare capacity neither allocates nor reallocates
        #[verifier::fip]
        fn push_spare(v: &mut Vec<u64>)
            requires
                old(v)@.len() < spec_vec_capacity(&*old(v)),
        {
            v.push(1);
            let _ = v.pop();
        }

        // dropping `u64`s frees nothing
        #[verifier::fip]
        fn clear(v: &mut Vec<u64>) {
            v.clear();
        }

        // fip(1): one allocation, no deallocation
        #[verifier::fip]
        fn make() -> (r: Box<u64>)
            allocates 1
        {
            Box::new(3)
        }

        #[verifier::fip]
        fn consume<T: NoDeallocDrop>(x: T) {
        }

        pub struct Handle { pub id: u64 }

        impl Drop for Handle {
            #[verifier::fip]
            fn drop(&mut self)
                opens_invariants none
                no_unwind
            {
            }
        }

        unsafe impl AllocFreeDrop for Handle {}

        unsafe impl NoDeallocDrop for Handle {}

        #[verifier::fip]
        fn drop_handle(h: Handle) {
            consume(h);
        }

        #[verifier::fip]
        fn drop_handle_here(h: Handle) {
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fip_dropped_parameter_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::fip]
        fn f(b: Box<u64>) {
        }
    } => Err(err) => assert_vir_error_msg(err, "a value of type `std::boxed::Box<u64>` is dropped here")
}

test_verify_one_file_with_options! {
    // moving the contents out of a box frees the box
    #[test] fip_move_out_of_box_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        pub struct N { pub v: u64 }
        #[verifier::fip]
        fn f(b: Box<N>) -> (r: N) {
            *b
        }
    } => Err(err) => assert_vir_error_msg(err, "its contents are moved out of it; reuse it instead")
}

test_verify_one_file_with_options! {
    #[test] fip_conditional_drop_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::fip]
        fn f(c: bool, b: Box<u64>) -> (r: Option<Box<u64>>) {
            if c { Some(b) } else { None }
        }
    } => Err(err) => assert_vir_error_msg(err, "is dropped here")
}

test_verify_one_file_with_options! {
    // a growth from an existing buffer reallocates it (frees the old block)
    #[test] fip_push_may_reallocate ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::fip]
        fn f(v: &mut Vec<u64>)
            allocates 1
        {
            v.push(1);
        }
    } => Err(err) => assert_any_vir_error_msg(err, "this call may deallocate memory")
}

test_verify_one_file_with_options! {
    #[test] fip_clear_of_boxes_fails ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::fip]
        fn f(v: &mut Vec<Box<u64>>) {
            v.clear();
        }
    } => Err(err) => assert_any_vir_error_msg(err, "this call may deallocate memory")
}

test_verify_one_file_with_options! {
    #[test] fip_calls_non_fip_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        fn g(x: u64) -> (r: u64) allocates 0 { x }
        #[verifier::fip]
        fn f() -> (r: u64) {
            g(1)
        }
    } => Err(err) => assert_vir_error_msg(err, "is not `#[verifier::fip]` and has no `deallocates_when` condition")
}

test_verify_one_file_with_options! {
    // the drop rule only needs `AllocFreeDrop`, but dropping a `T` may deallocate
    #[test] fip_generic_drop_needs_marker ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::fip]
        fn f<T: vstd::alloc_check::AllocFreeDrop>(x: T) {
        }
    } => Err(err) => assert_vir_error_msg(err, "a value of type `T` is dropped here")
}

test_verify_one_file_with_options! {
    #[test] no_dealloc_drop_impl_checked ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        pub struct H { pub b: Box<u64> }
        unsafe impl vstd::alloc_check::AllocFreeDrop for H {}
        unsafe impl vstd::alloc_check::NoDeallocDrop for H {}
    } => Err(err) => assert_vir_error_msg(err, "this `NoDeallocDrop` impl is not accepted")
}

test_verify_one_file_with_options! {
    #[test] no_dealloc_drop_impl_needs_fip_drop ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        pub struct H { pub id: u64 }
        impl Drop for H {
            fn drop(&mut self)
                opens_invariants none
                no_unwind
                allocates 0
            {
            }
        }
        unsafe impl vstd::alloc_check::AllocFreeDrop for H {}
        unsafe impl vstd::alloc_check::NoDeallocDrop for H {}
    } => Err(err) => assert_vir_error_msg(err, "its `Drop::drop` is not `#[verifier::fip]`")
}

test_verify_one_file_with_options! {
    #[test] deallocates_when_condition_proved ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::external_body]
        fn maybe_free(v: &mut Vec<u64>, b: bool)
            allocates 0int deallocates deallocates_when(1int, b)
        {
        }
        #[verifier::fip]
        fn f(v: &mut Vec<u64>) {
            maybe_free(v, false);
        }
        #[verifier::fip]
        fn g(v: &mut Vec<u64>, b: bool) {
            maybe_free(v, b); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] deallocates_when_transitional_form_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::external_body]
        fn f(b: bool)
            allocates deallocates_when(0int, b)
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "`allocates deallocates_when(n, c)` is no longer accepted")
}

test_verify_one_file_with_options! {
    #[test] fip_needs_alloc_check ["vstd"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::fip]
        fn f() {}
    } => Err(err) => assert_vir_error_msg(err, "`#[verifier::fip]` needs -V alloc-check")
}

test_verify_one_file_with_options! {
    // (`explicit_tail_calls` is enabled by the test prelude)
    #[test] fip_strict_tail_recursion_accepted ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::fip(strict)]
        fn sum(n: u64, acc: u64) -> (r: u64)
            decreases n
        {
            if n == 0 { acc } else { become sum(n - 1, acc.wrapping_add(n)) }
        }
        #[verifier::fip(strict)]
        fn even(n: u64) -> (r: bool)
            decreases n
        {
            if n == 0 { true } else { become odd(n - 1) }
        }
        #[verifier::fip(strict)]
        fn odd(n: u64) -> (r: bool)
            decreases n
        {
            if n == 0 { false } else { become even(n - 1) }
        }
        // non-tail calls of functions that do not lead back here are fine
        #[verifier::fip(strict)]
        fn caller() -> (r: u64) {
            let a = sum(10, 0);
            if even(4) { a } else { 0 }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fip_strict_non_tail_recursion_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::fip(strict)]
        fn sum(n: u64) -> (r: u64)
            decreases n
        {
            if n == 0 { 0 } else { sum(n - 1).wrapping_add(n) }
        }
    } => Err(err) => assert_vir_error_msg(err, "is not a tail call and can lead back to `sum`")
}

test_verify_one_file_with_options! {
    // a cycle with one non-tail call grows the stack by a frame per round
    #[test] fip_strict_mixed_cycle_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::fip(strict)]
        fn f(n: u64) -> (r: u64)
            decreases n, 1int
        {
            if n == 0 { 0 } else { become g(n) }
        }
        #[verifier::fip(strict)]
        fn g(n: u64) -> (r: u64)
            requires n > 0,
            decreases n, 0int
        {
            f(n - 1).wrapping_add(1)
        }
    } => Err(err) => assert_vir_error_msg(err, "this call of `f` is not a tail call and can lead back to `g`")
}

test_verify_one_file_with_options! {
    #[test] fip_strict_calls_non_strict_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::fip]
        fn plain(n: u64) -> (r: u64) { n }
        #[verifier::fip(strict)]
        fn f() -> (r: u64) { plain(1) }
    } => Err(err) => assert_vir_error_msg(err, "it calls `plain`, which is not `#[verifier::fip(strict)]`")
}

test_verify_one_file_with_options! {
    // a drop runs the type's destructor, which must be strict too
    #[test] fip_strict_destructor_must_be_strict ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::{AllocFreeDrop, NoDeallocDrop};
        pub struct Handle { pub id: u64 }
        impl Drop for Handle {
            #[verifier::fip]
            fn drop(&mut self)
                opens_invariants none
                no_unwind
            {
            }
        }
        unsafe impl AllocFreeDrop for Handle {}
        unsafe impl NoDeallocDrop for Handle {}
        #[verifier::fip(strict)]
        fn f(h: Handle) {
        }
    } => Err(err) => assert_vir_error_msg(err, "which is not `#[verifier::fip(strict)]`")
}

test_verify_one_file_with_options! {
    // `-V fip-lint`: suggestions for recursion that grows the stack
    #[test] fip_lint_suggestions ["vstd", "-V fip-lint"] => verus_code! {
        use vstd::prelude::*;
        pub enum List { Nil, Cons(u64, Box<List>) }

        // in tail position, but not a tail call
        fn sum(n: u64, acc: u64) -> (r: u64)
            decreases n
        {
            if n == 0 { acc } else { sum(n - 1, acc.wrapping_add(n)) }
        }

        // in tail position with a drop pending after the call
        fn sum_v(n: u64, acc: u64, v: Vec<u8>) -> (r: u64)
            decreases n
        {
            if n == 0 { acc } else { sum_v(n - 1, acc, Vec::new()) }
        }

        // recursion modulo a constructor
        fn range(n: u64) -> (r: List)
            decreases n
        {
            if n == 0 { List::Nil } else { List::Cons(n, Box::new(range(n - 1))) }
        }

        // already a tail call, and calls that are not recursive: nothing to suggest
        fn sum2(n: u64, acc: u64) -> (r: u64)
            decreases n
        {
            if n == 0 { acc } else { become sum2(n - 1, acc.wrapping_add(n)) }
        }
        fn h(n: u64) -> (r: u64) {
            sum(n, 0)
        }
    } => Ok(err) => {
        let msgs: Vec<&str> = err
            .warnings
            .iter()
            .map(|w| w.message.as_str())
            .filter(|m| m.starts_with("-V fip-lint"))
            .collect();
        assert_eq!(msgs.len(), 4, "{:?}", msgs);
        assert!(msgs.iter().any(|m| m.contains("call of `sum` is in tail position but is not a tail call")), "{:?}", msgs);
        assert!(msgs.iter().any(|m| m.contains("call of `sum_v` is in tail position") && m.contains("a drop is pending after the call: `std::vec::Vec<u8>`")), "{:?}", msgs);
        assert!(msgs.iter().any(|m| m.contains("recursive call of `test_crate::range` is not a tail call") && m.contains("tail recursion modulo a constructor")), "{:?}", msgs);
        // the rewrite into a loop, as a suggestion
        let rewrite = err
            .warnings
            .iter()
            .find(|w| w.message.contains("`test_crate::range` can be rewritten into a loop"))
            .expect("rewrite warning");
        assert!(rewrite.rendered.contains("'__trmc: loop"), "{}", rewrite.rendered);
        assert!(rewrite.rendered.contains("__trmc_hole = match __trmc_hole"), "{}", rewrite.rendered);
    }
}

test_verify_one_file_with_options! {
    #[test] fip_lint_trmc_not_rewritable ["vstd", "-V fip-lint"] => verus_code! {
        use vstd::prelude::*;
        pub enum List { Nil, Cons(u64, Box<List>) }

        // a second recursive call that is not in tail position
        fn twice(n: u64) -> (r: List)
            decreases n
        {
            if n == 0 {
                List::Nil
            } else {
                let _ = twice(n - 1);
                List::Cons(n, Box::new(twice(n - 1)))
            }
        }

        // no variant without fields to hold the place of the value being built
        pub struct Cell { pub v: u64, pub next: Option<Box<Cell>> }
        fn cells(n: u64) -> (r: Cell)
            decreases n
        {
            if n == 0 { Cell { v: 0, next: None } } else { Cell { v: n, next: Some(Box::new(cells(n - 1))) } }
        }
    } => Ok(err) => {
        let msgs: Vec<&str> = err
            .warnings
            .iter()
            .map(|w| w.message.as_str())
            .filter(|m| m.contains("cannot be rewritten into a loop automatically"))
            .collect();
        assert_eq!(msgs.len(), 2, "{:?}", msgs);
        assert!(msgs.iter().any(|m| m.contains("neither a tail call nor the only recursive call inside a constructor")), "{:?}", msgs);
        assert!(msgs.iter().any(|m| m.contains("must be an enum with a variant without fields")), "{:?}", msgs);
    }
}

/// A user allocator for the fip allocator tests. Its own code allocates twice, frees, clones and
/// recurses: an allocator is the runtime, so none of that is the program's.
const USER_ALLOCATOR: &str = verus_code_str! {
    use vstd::prelude::*;
    use vstd::std_specs::vec::spec_vec_capacity;
    use std::alloc::{Allocator, AllocError, Global, Layout};
    use std::ptr::NonNull;

    pub struct Fwd;

    impl Clone for Fwd {
        fn clone(&self) -> (r: Self) {
            let b = Box::new(1u8);
            Fwd
        }
    }

    impl Drop for Fwd {
        fn drop(&mut self)
            opens_invariants none
            no_unwind
        {
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn spin(n: u64) {
        if n > 0 { spin(n - 1) }
    }

    unsafe impl Allocator for Fwd {
        fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>) {
            let v: Vec<u8> = Vec::with_capacity(4);
            spin(3);
            Global.allocate(layout)
        }

        unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
            #[verifier::trusted_call] { unsafe { Global.deallocate(ptr, layout) } }
        }
    }
};

test_verify_one_file_with_options! {
    // a fip (or strict) function may use any allocator: a call to it is one allocation, and what
    // it does itself is the runtime's
    #[test] fip_user_allocator_is_runtime ["vstd", "-V alloc-check"] => USER_ALLOCATOR.to_string() + verus_code_str! {
        #[verifier::fip]
        fn push_empty(v: &mut Vec<u8, Fwd>)
            requires spec_vec_capacity(&*old(v)) == 0,
            allocates 1
        {
            v.push(1);
        }

        #[verifier::fip(strict)]
        fn push_empty_strict(v: &mut Vec<u8, Fwd>)
            requires spec_vec_capacity(&*old(v)) == 0,
            allocates 1
        {
            v.push(1);
        }

        #[verifier::fip(strict)]
        fn push_generic<A: Allocator>(v: &mut Vec<u8, A>)
            requires spec_vec_capacity(&*old(v)) == 0,
            allocates 1
        {
            v.push(1);
        }

        #[verifier::fip(strict)]
        fn mk() -> (r: Vec<u8, Fwd>)
            allocates 1
        {
            Vec::with_capacity_in(4, Fwd)
        }

        #[verifier::fip(strict)]
        fn direct(a: &Fwd, l: Layout) -> (r: Result<NonNull<[u8]>, AllocError>)
            allocates 1
        {
            a.allocate(l)
        }

        #[verifier::fip(strict)]
        fn copy_alloc(a: &Fwd) -> (r: Fwd)
            allocates 0
        {
            a.clone()
        }

        #[verifier::fip(strict)]
        fn drop_alloc(a: Fwd)
            allocates 0
        {
        }

        // the std allocators' `allocate` never deallocates
        #[verifier::fip]
        fn direct_global(l: Layout) -> (r: Result<NonNull<[u8]>, AllocError>)
            allocates 1
        {
            Global.allocate(l)
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // growing a vector that has a buffer moves it (`grow` frees the old block): the program's
    // deallocation, whatever the allocator
    #[test] fip_user_allocator_grow_rejected ["vstd", "-V alloc-check"] => USER_ALLOCATOR.to_string() + verus_code_str! {
        #[verifier::fip]
        fn push_full(v: &mut Vec<u8, Fwd>)
            requires 0 < spec_vec_capacity(&*old(v)) == old(v)@.len(),
            allocates 1
        {
            v.push(1);
        }
    } => Err(err) => assert_vir_error_msg(err, "this call may deallocate memory")
}

test_verify_one_file_with_options! {
    // dropping a container frees its buffer: the program's deallocation, whatever the allocator
    #[test] fip_user_allocator_container_drop_rejected ["vstd", "-V alloc-check"] => USER_ALLOCATOR.to_string() + verus_code_str! {
        #[verifier::fip]
        fn drop_vec(v: Vec<u8, Fwd>)
            allocates 0
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "is dropped here")
}

test_verify_one_file_with_options! {
    // an allocator's methods count as the `Allocator` declaration says, whatever their own bound
    #[test] fip_user_allocator_call_counts_one ["vstd", "-V alloc-check"] => USER_ALLOCATOR.to_string() + verus_code_str! {
        fn twice(a: &Fwd, l: Layout)
            allocates 1 // FAILS
        {
            let _ = a.allocate(l);
            let _ = a.allocate(l);
        }
    } => Err(err) => assert_one_fails(err)
}

/// A type whose (fip, but not strict) `Drop` recurses
const RECURSIVE_DROP: &str = verus_code_str! {
    use vstd::prelude::*;
    use vstd::alloc_check::{AllocFreeDrop, NoDeallocDrop};

    #[verifier::fip]
    fn deep(n: u64) -> (r: u64)
        decreases n
        opens_invariants none
        no_unwind
    {
        if n == 0 { 0 } else { let r = deep(n - 1); if r < 1000 { r + 1 } else { r } }
    }

    pub struct H { pub n: u64 }

    impl Drop for H {
        #[verifier::fip]
        fn drop(&mut self)
            opens_invariants none
            no_unwind
        {
            let _ = deep(self.n);
        }
    }

    unsafe impl AllocFreeDrop for H {}
    unsafe impl NoDeallocDrop for H {}
};

test_verify_one_file_with_options! {
    // the drop of a value of a type parameter runs a destructor that is not known here
    #[test] fip_strict_generic_drop ["vstd", "-V alloc-check"] => RECURSIVE_DROP.to_string() + verus_code_str! {
        #[verifier::fip(strict)]
        fn sink<T: NoDeallocDrop>(x: T) {
        }
    } => Err(err) => assert_vir_error_msg(err, "it drops a value of type `T`, whose destructor is not known here")
}

test_verify_one_file_with_options! {
    #[test] fip_strict_generic_copy_ok ["vstd", "-V alloc-check"] => RECURSIVE_DROP.to_string() + verus_code_str! {
        #[verifier::fip(strict)]
        fn sink<T: Copy>(x: T) {
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // std code may drop values of its type arguments (`Vec::clear`), running their destructors
    #[test] fip_strict_std_call_runs_destructor ["vstd", "-V alloc-check"] => RECURSIVE_DROP.to_string() + verus_code_str! {
        #[verifier::fip(strict)]
        fn strict_clear(v: &mut Vec<H>) {
            v.clear();
        }
    } => Err(err) => assert_vir_error_msg(err, "which is not `#[verifier::fip(strict)]`")
}

test_verify_one_file_with_options! {
    // (both the MIR checks and the verifier must agree on the kind)
    #[test] fip_two_attributes ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::fip]
        #[verifier::fip(strict)]
        fn f(n: u64) -> u64 {
            n
        }
    } => Err(err) => assert_vir_error_msg(err, "more than one `#[verifier::fip]` attribute")
}

/// The reasons `-V fip-lint` gives for not rewriting recursion modulo a constructor
fn trmc_reasons(err: &TestErr) -> Vec<String> {
    err.warnings
        .iter()
        .map(|w| w.message.clone())
        .filter(|m| m.contains("cannot be rewritten into a loop automatically"))
        .collect()
}

test_verify_one_file_with_options! {
    #[test] fip_lint_trmc_not_rewritable_order_and_names ["vstd", "-V fip-lint"] => verus_code! {
        use vstd::prelude::*;
        pub enum T { Leaf, Node(Box<T>, u64) }
        pub enum L { Nil, Cons(u64, Box<L>) }

        fn tick() -> u64 { 7 }

        // a field after the recursive call that is not a literal or a name
        fn after(n: u64) -> (r: T)
            decreases n
        {
            if n == 0 { T::Leaf } else { T::Node(Box::new(after(n - 1)), tick()) }
        }

        // a parameter's name bound again
        fn shadow(k: u64, n: u64) -> (r: L)
            requires k < 1000,
            decreases n
        {
            let k = k + 1;
            if n == 0 { L::Nil } else { L::Cons(k, Box::new(shadow(k % 1000, n - 1))) }
        }
    } => Ok(err) => {
        let msgs = trmc_reasons(&err);
        assert_eq!(msgs.len(), 2, "{:?}", msgs);
        assert!(msgs.iter().any(|m| m.contains("this field comes after the recursive call")), "{:?}", msgs);
        assert!(msgs.iter().any(|m| m.contains("binds a parameter's name again")), "{:?}", msgs);
    }
}

test_verify_one_file_with_options! {
    #[test] fip_lint_trmc_not_rewritable_user_drop ["vstd", "-V fip-lint"] => verus_code! {
        use vstd::prelude::*;
        pub enum L { Nil, Cons(u64, Box<L>) }
        pub struct D(pub u64);
        impl Drop for D {
            fn drop(&mut self)
                opens_invariants none
                no_unwind
            {
            }
        }

        // `d` is dropped after the recursive call returns
        fn with_drop(n: u64) -> (r: L)
            decreases n
        {
            let d = D(n);
            if n == 0 { L::Nil } else { L::Cons(n, Box::new(with_drop(n - 1))) }
        }
    } => Ok(err) => {
        let msgs = trmc_reasons(&err);
        assert_eq!(msgs.len(), 1, "{:?}", msgs);
        assert!(msgs[0].contains("dropping this value"), "{:?}", msgs);
    }
}

test_verify_one_file_with_options! {
    // temporaries whose drop runs user code (portable-fip, fip-beta 3eb69f3c3, N4), and a name the
    // rewrite reserves (N5)
    #[test] fip_lint_trmc_not_rewritable_temporaries_and_reserved_names ["vstd", "-V fip-lint"] => verus_code! {
        use vstd::prelude::*;
        pub enum L { Nil, Cons(u64, Box<L>) }
        pub enum L2 { Nil, Cons(u64, u64, Box<L2>) }
        pub struct D(pub u64);
        impl Drop for D {
            fn drop(&mut self)
                opens_invariants none
                no_unwind
            {
            }
        }
        fn mkd(n: u64) -> (r: D) ensures r.0 == n { D(n) }

        // a match scrutinee
        fn scrut(n: u64) -> (r: L)
            decreases n
        {
            match mkd(n) { D(v) => if v == 0 { L::Nil } else { L::Cons(v, Box::new(scrut(v - 1))) } }
        }

        // a field taken out of a temporary
        fn temp(n: u64) -> (r: L)
            decreases n
        {
            if n == 0 { L::Nil } else { L::Cons(mkd(n).0, Box::new(temp(n - 1))) }
        }

        // an argument of the recursive call
        fn arg(n: u64) -> (r: L)
            decreases n
        {
            if n == 0 { L::Nil } else { L::Cons(n, Box::new(arg(mkd(n - 1).0))) }
        }

        // a local named like the rewrite's temporaries
        fn named(n: u64) -> (r: L2)
            decreases n
        {
            let __trmc_t0: u64 = 7;
            if n == 0 { L2::Nil } else { L2::Cons(n, __trmc_t0, Box::new(named(n - 1))) }
        }
    } => Ok(err) => {
        let msgs = trmc_reasons(&err);
        assert_eq!(msgs.len(), 4, "{:?}", msgs);
        assert_eq!(msgs.iter().filter(|m| m.contains("dropping this value")).count(), 3, "{:?}", msgs);
        assert!(msgs.iter().any(|m| m.contains("a name starting with `__trmc`")), "{:?}", msgs);
    }
}

// fip(strict) takes `verus_builtin`'s functions as leaves, so a dependency of that name must be
// the one Verus provides: a look-alike (with a deep recursion) brought in under another extern
// name is rejected (portable-fip, fip-beta 3eb69f3c3, N3)
#[test]
fn fip_strict_fake_verus_builtin_rejected() {
    let tempdir = tempfile::TempDir::new().expect("temp dir");
    let dir = tempdir.path();
    let pre = format!("{}\nuse vstd::prelude::*;\n", FEATURE_PRELUDE);
    std::fs::write(
        dir.join("vb.rs"),
        format!(
            "{pre}verus!{{ pub fn deep(n: u64) -> u64 decreases n {{ if n == 0 {{ 0 }} else {{ let r = deep(n - 1); if r < u64::MAX {{ r + 1 }} else {{ r }} }} }} }}\n"
        ),
    )
    .expect("write");
    std::fs::write(
        dir.join("c.rs"),
        format!(
            "{pre}verus!{{ #[verifier::fip(strict)] fn s(n: u64) -> u64 {{ fb::deep(n) }} }}\n"
        ),
    )
    .expect("write");
    // (built without -V alloc-check: with it, the name is refused outright, see below)
    let fake = run_verus_raw(
        &[
            "--crate-type=lib",
            "--crate-name",
            "verus_builtin",
            "-C",
            "metadata=fake",
            "--export",
            "vb.vir",
            "--compile",
            "vb.rs",
            "-o",
            "libfakevb.rlib",
        ],
        dir,
    );
    assert!(fake.status.success(), "fake failed:\n{}", String::from_utf8_lossy(&fake.stderr));
    let c = run_verus_raw(
        &[
            "--crate-type=lib",
            "c.rs",
            "-V",
            "alloc-check",
            "--import",
            "fb=vb.vir",
            "--extern",
            "fb=libfakevb.rlib",
        ],
        dir,
    );
    let stderr = String::from_utf8_lossy(&c.stderr);
    assert!(!c.status.success(), "c should be rejected:\n{}", stderr);
    assert!(
        stderr
            .contains("trusts a crate named `verus_builtin` only if it is the one Verus provides"),
        "unexpected:\n{}",
        stderr
    );
    // and a crate of that name cannot itself be verified with -V alloc-check
    let named = run_verus_raw(
        &["--crate-type=lib", "--crate-name", "verus_builtin", "vb.rs", "-V", "alloc-check"],
        dir,
    );
    let stderr = String::from_utf8_lossy(&named.stderr);
    assert!(!named.status.success(), "should be rejected:\n{}", stderr);
    assert!(
        stderr.contains("a crate named `verus_builtin` cannot be verified with -V alloc-check"),
        "unexpected:\n{}",
        stderr
    );
}

// The marker traits are found by the path where vstd defines them, not by the path rustc prints:
// a loaded crate that re-exports them made the printed path its own, so `NoDeallocDrop` impls and
// user allocators went unchecked and `T: NoDeallocDrop` was not trusted (Y4, 2026-11-15)
#[test]
fn fip_markers_found_through_reexport() {
    let tempdir = tempfile::TempDir::new().expect("temp dir");
    let dir = tempdir.path();
    let pre = format!("{}\nuse vstd::prelude::*;\n", FEATURE_PRELUDE);
    std::fs::write(
        dir.join("facade.rs"),
        format!(
            "{pre}pub use vstd::alloc_check::{{NoDeallocDrop, FipAdd}};\nverus!{{ pub fn f() {{}} }}\n"
        ),
    )
    .expect("write");
    let facade = run_verus_raw(
        &[
            "--crate-type=lib",
            "--crate-name",
            "facade",
            "--export",
            "facade.vir",
            "--compile",
            "facade.rs",
            "-o",
            "libfacade.rlib",
        ],
        dir,
    );
    assert!(facade.status.success(), "facade failed:\n{}", String::from_utf8_lossy(&facade.stderr));
    let with_facade = |name: &str, code: &str| {
        // (`facade::f()` makes rustc load the crate)
        std::fs::write(
            dir.join(name),
            format!("{pre}verus!{{ {code}\npub fn uses_facade() {{ facade::f() }} }}\n"),
        )
        .expect("write");
        run_verus_raw(
            &[
                "--crate-type=lib",
                name,
                "-V",
                "alloc-check",
                "--import",
                "facade=facade.vir",
                "--extern",
                "facade=libfacade.rlib",
            ],
            dir,
        )
    };
    // a `NoDeallocDrop` impl for a type that owns a box is still rejected
    let neg = with_facade(
        "neg.rs",
        "pub struct Holder { pub b: Box<u64> }
        unsafe impl vstd::alloc_check::AllocFreeDrop for Holder {}
        unsafe impl vstd::alloc_check::NoDeallocDrop for Holder {}",
    );
    let stderr = String::from_utf8_lossy(&neg.stderr);
    assert!(!neg.status.success(), "neg should be rejected:\n{}", stderr);
    assert!(
        stderr.contains("this `NoDeallocDrop` impl is not accepted"),
        "unexpected:\n{}",
        stderr
    );
    // and the markers are still trusted at drops and generic operator calls
    let pos = with_facade(
        "pos.rs",
        "use vstd::std_specs::ops::AddSpec;
        #[verifier::fip]
        fn consume<T: vstd::alloc_check::NoDeallocDrop>(x: T) {}
        #[verifier::fip]
        fn add_gen<T: vstd::alloc_check::FipAdd<Output = T> + vstd::alloc_check::NoDeallocDrop>(a: T, b: T) -> T
            requires a.add_req(b),
        {
            a + b
        }",
    );
    assert!(pos.status.success(), "pos should pass:\n{}", String::from_utf8_lossy(&pos.stderr));
}

test_verify_one_file_with_options! {
    // the real `verus_builtin` stays trusted: `Ghost(..)` in a strict function compiles to a call
    // of `Ghost::assume_new_fallback`
    #[test] fip_strict_ghost_wrappers_accepted ["vstd", "-V alloc-check", "--compile"] => verus_code! {
        use vstd::prelude::*;
        pub enum L { Nil, Cons(u64, Box<L>) }
        spec fn len(l: &L) -> nat decreases l { match l { L::Nil => 0, L::Cons(_, t) => 1 + len(t) } }
        #[verifier::fip(strict)]
        fn bump(l: L, Ghost(g): Ghost<int>) -> (r: L)
            ensures len(&r) == len(&l)
            allocates 0
        {
            match l {
                L::Nil => L::Nil,
                L::Cons(x, tl) => {
                    let gh: Ghost<nat> = Ghost(len(&tl));
                    assert(len(&tl) == gh@);
                    L::Cons(x.wrapping_add(1), tl)
                }
            }
        }
    } => Ok(())
}

// A library may provide an allocator, which need not be verified with -V alloc-check (an allocator
// is the runtime), and a strict function of another crate may use it; a marker impl of a crate
// not verified with -V alloc-check is rejected (portable-fip, fip-beta 3eb69f3c3, §2)
#[test]
fn fip_allocator_from_library() {
    let tempdir = tempfile::TempDir::new().expect("temp dir");
    let dir = tempdir.path();
    let pre = format!("{}\nuse vstd::prelude::*;\n", FEATURE_PRELUDE);
    std::fs::write(
        dir.join("lib.rs"),
        format!(
            "{pre}use std::alloc::{{Allocator, AllocError, Global, Layout}};
use std::ptr::NonNull;
verus! {{
pub struct Fwd;
unsafe impl Allocator for Fwd {{
    fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>) {{
        let _ = Global.allocate(layout);
        Global.allocate(layout)
    }}
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {{
        #[verifier::trusted_call] {{ unsafe {{ Global.deallocate(ptr, layout) }} }}
    }}
}}
}}
"
        ),
    )
    .expect("write");
    std::fs::write(
        dir.join("m.rs"),
        format!(
            "{pre}verus!{{ #[verifier::fip(strict)] fn f(v: &mut Vec<u8, lib::Fwd>)
                requires vstd::std_specs::vec::spec_vec_capacity(&*old(v)) == 0,
                allocates 1
            {{ v.push(1); }} }}\n"
        ),
    )
    .expect("write");
    let lib = run_verus_raw(
        // (an allocator is the runtime: its crate need not be verified with -V alloc-check)
        &["--crate-type=lib", "lib.rs", "--compile", "--export", "lib.vir"],
        dir,
    );
    assert!(lib.status.success(), "lib:\n{}", String::from_utf8_lossy(&lib.stderr));
    let m = run_verus_raw(
        &[
            "--crate-type=lib",
            "m.rs",
            "-V",
            "alloc-check",
            "--compile",
            "--import",
            "lib=lib.vir",
            "--extern",
            "lib=liblib.rlib",
        ],
        dir,
    );
    assert!(m.status.success(), "m:\n{}", String::from_utf8_lossy(&m.stderr));

    // a (false) `NoDeallocDrop` in a crate built without -V alloc-check
    std::fs::write(
        dir.join("lib3.rs"),
        format!(
            "{pre}use vstd::alloc_check::{{AllocFreeDrop, NoDeallocDrop}};
verus! {{
pub struct S {{ pub b: Box<u8> }}
unsafe impl AllocFreeDrop for S {{}}
unsafe impl NoDeallocDrop for S {{}}
}}
"
        ),
    )
    .expect("write");
    let lib3 =
        run_verus_raw(&["--crate-type=lib", "lib3.rs", "--compile", "--export", "lib3.vir"], dir);
    assert!(lib3.status.success(), "lib3:\n{}", String::from_utf8_lossy(&lib3.stderr));
    std::fs::write(
        dir.join("m3.rs"),
        format!("{pre}verus!{{ #[verifier::fip] fn eat(s: lib3::S) -> (r: u64) allocates 0 {{ core::mem::forget(s); 0 }} }}\n"),
    )
    .expect("write");
    let m3 = run_verus_raw(
        &[
            "--crate-type=lib",
            "m3.rs",
            "-V",
            "alloc-check",
            "--compile",
            "--import",
            "lib3=lib3.vir",
            "--extern",
            "lib3=liblib3.rlib",
        ],
        dir,
    );
    let stderr = String::from_utf8_lossy(&m3.stderr);
    assert!(!m3.status.success(), "m3 should be rejected:\n{}", stderr);
    assert!(
        stderr.contains("which was not verified (and compiled) with -V alloc-check"),
        "unexpected:\n{}",
        stderr
    );
}

// A strict function may call a strict function of a crate verified and compiled with
// -V alloc-check, and drop a value of a type whose `Drop` is strict there (as leaves); other
// functions and destructors of other crates stay unknown (portable-fip, fip-beta 6f6975af2, §2)
#[test]
fn fip_strict_across_crates() {
    let tempdir = tempfile::TempDir::new().expect("temp dir");
    let dir = tempdir.path();
    let pre = format!("{}\nuse vstd::prelude::*;\n", FEATURE_PRELUDE);
    std::fs::write(
        dir.join("lib.rs"),
        format!(
            "{pre}use vstd::alloc_check::{{AllocFreeDrop, NoDeallocDrop}};
verus! {{
pub struct H {{ pub n: u64 }}
impl Drop for H {{
    #[verifier::fip(strict)]
    fn drop(&mut self) opens_invariants none no_unwind {{}}
}}
unsafe impl AllocFreeDrop for H {{}}
unsafe impl NoDeallocDrop for H {{}}
pub struct G {{ pub n: u64 }}
impl Drop for G {{
    #[verifier::fip]
    fn drop(&mut self) opens_invariants none no_unwind {{}}
}}
unsafe impl AllocFreeDrop for G {{}}
unsafe impl NoDeallocDrop for G {{}}
#[verifier::fip(strict)]
pub fn inc(x: u64) -> (r: u64) allocates 0 {{ x.wrapping_add(1) }}
#[verifier::fip]
pub fn inc_loose(x: u64) -> (r: u64) allocates 0 {{ x.wrapping_add(1) }}
}}
"
        ),
    )
    .expect("write");
    let lib = run_verus_raw(
        &["--crate-type=lib", "lib.rs", "-V", "alloc-check", "--compile", "--export", "lib.vir"],
        dir,
    );
    assert!(lib.status.success(), "lib:\n{}", String::from_utf8_lossy(&lib.stderr));
    let run = |name: &str, body: &str| {
        std::fs::write(dir.join(format!("{name}.rs")), format!("{pre}verus!{{ {body} }}\n"))
            .expect("write");
        let out = run_verus_raw(
            &[
                "--crate-type=lib",
                &format!("{name}.rs"),
                "-V",
                "alloc-check",
                "--compile",
                "--import",
                "lib=lib.vir",
                "--extern",
                "lib=liblib.rlib",
            ],
            dir,
        );
        (out.status.success(), String::from_utf8_lossy(&out.stderr).to_string())
    };
    let (ok, e) = run(
        "ok",
        "#[verifier::fip(strict)] fn s(x: u64, h: lib::H) -> (r: u64) allocates 0 { let y = lib::inc(x); y }",
    );
    assert!(ok, "{}", e);
    let (ok, e) = run(
        "bad1",
        "#[verifier::fip(strict)] fn s(x: u64) -> (r: u64) allocates 0 { lib::inc_loose(x) }",
    );
    assert!(!ok && e.contains("calls `lib::inc_loose` from another crate"), "{}", e);
    let (ok, e) = run("bad2", "#[verifier::fip(strict)] fn s(g: lib::G) { }");
    assert!(!ok && e.contains("<lib::G as std::ops::Drop>::drop` from another crate"), "{}", e);
    // a strict library function generic over the allocator, instantiated with an allocator whose
    // `allocate` calls back into it: the allocator's code is the runtime's, whose stack is not
    // counted, but the cycle is still a recursion that VIR's termination check rejects
    std::fs::write(
        dir.join("glib.rs"),
        format!(
            "{pre}use std::alloc::Allocator;
verus! {{
#[verifier::fip(strict)]
pub fn push_one<A: Allocator + Copy>(v: &mut Vec<u8, A>)
    requires vstd::std_specs::vec::spec_vec_capacity(&*old(v)) == 0,
    allocates 1
{{ v.push(1); }}
}}
"
        ),
    )
    .expect("write");
    let glib = run_verus_raw(
        &["--crate-type=lib", "glib.rs", "-V", "alloc-check", "--compile", "--export", "glib.vir"],
        dir,
    );
    assert!(glib.status.success(), "glib:\n{}", String::from_utf8_lossy(&glib.stderr));
    std::fs::write(
        dir.join("cyc.rs"),
        format!(
            "{pre}use std::alloc::{{Allocator, AllocError, Global, Layout}};
use std::ptr::NonNull;
verus! {{
pub struct Re;
impl Clone for Re {{
    fn clone(&self) -> (r: Self) {{ Re }}
}}
impl Copy for Re {{}}
#[verifier::fip(strict)]
fn g() allocates 1 {{
    let mut v: Vec<u8, Re> = Vec::new_in(Re);
    glib::push_one(&mut v);
    core::mem::forget(v);
}}
unsafe impl Allocator for Re {{
    fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>) {{
        g();
        Global.allocate(layout)
    }}
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {{
        #[verifier::trusted_call] {{ unsafe {{ Global.deallocate(ptr, layout) }} }}
    }}
}}
}}
"
        ),
    )
    .expect("write");
    let cyc = run_verus_raw(
        &[
            "--crate-type=lib",
            "cyc.rs",
            "-V",
            "alloc-check",
            "--compile",
            "--import",
            "glib=glib.vir",
            "--extern",
            "glib=libglib.rlib",
        ],
        dir,
    );
    let e = String::from_utf8_lossy(&cyc.stderr);
    assert!(!cyc.status.success(), "{}", e);
    assert!(e.contains("cyclic self-reference"), "{}", e);
}

test_verify_one_file_with_options! {
    // std's slice views (they reborrow the slice or move elements within it: nothing is dropped
    // or freed, and no user code runs) may be called from a fip function (portable-fip,
    // 2026-11-09 split_at_mut request)
    #[test] fip_slice_views ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::fip]
        pub fn swap_lt(xs: &mut [u64], i: usize, j: usize)
            requires i < j, j < old(xs)@.len(),
            ensures final(xs)@ == old(xs)@.update(i as int, old(xs)@[j as int]).update(j as int, old(xs)@[i as int]),
            no_unwind allocates 0
        {
            let (a, b) = <[u64]>::split_at_mut(xs, j);
            ::core::mem::swap(&mut a[i], &mut b[0]);
            proof { assert(final(xs)@ =~= old(xs)@.update(i as int, old(xs)@[j as int]).update(j as int, old(xs)@[i as int])); }
        }
        #[verifier::fip]
        fn views(xs: &mut [u64], v: &mut Vec<u64>) -> (r: u64)
            requires old(xs)@.len() >= 2, old(v)@.len() >= 1,
            allocates 0
        {
            let n = xs.len();
            let a = xs[0];
            let w = v[0];
            v[0] = a;
            xs.swap(0, 1);
            let _ = xs.split_last();
            let _ = xs.first();
            match xs.split_last_mut() { Some((l, _)) => { *l = w; } None => {} }
            match xs.split_at_mut_checked(1) { Some((p, q)) => { core::mem::swap(&mut p[0], &mut q[0]); } None => {} }
            match xs.get(0) { Some(x) => *x, None => 0 }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // std functions that drop no value of their type arguments (vstd's specifications say so
    // with `alloc_check_skip_drops`) may be called with a `T` whose destructor is not known
    // (portable-fip, 2026-11-09 strict-std-calls request)
    #[test] fip_strict_std_calls_drop_nothing ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::AllocFreeDrop;
        #[verifier::fip(strict)]
        pub fn swap_lt_any<T: AllocFreeDrop>(xs: &mut [T], i: usize, j: usize)
            requires i < j, j < old(xs)@.len(),
            no_unwind allocates 0
        {
            let (a, b) = <[T]>::split_at_mut(xs, j);
            ::core::mem::swap(&mut a[i], &mut b[0]);
        }
        #[verifier::fip(strict)]
        pub fn replace_any<T: AllocFreeDrop>(x: &mut T, y: T) -> (r: T)
            no_unwind allocates 0
        {
            ::core::mem::replace(x, y)
        }
        #[verifier::fip(strict)]
        pub fn views_any<T: AllocFreeDrop>(xs: &mut [T], v: &mut Vec<T>) -> (r: usize)
            requires old(xs)@.len() >= 2, old(v)@.len() >= 1,
            allocates 0
        {
            xs.swap(0, 1);
            let _ = xs.split_last_mut();
            let _ = xs.first();
            let _ = xs.get(0);
            let _ = &v[0];
            let _ = v.as_mut_slice();
            let _ = v.len();
            xs.len()
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // (`Vec::clear` drops the elements)
    #[test] fip_strict_std_call_that_drops_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::{AllocFreeDrop, NoDeallocDrop};
        #[verifier::fip(strict)]
        pub fn clear_any<T: AllocFreeDrop + NoDeallocDrop>(v: &mut Vec<T>)
            allocates 0
        {
            v.clear();
        }
    } => Err(err) => assert_vir_error_msg(err, "which may drop a value of type `T`, whose destructor is not known here")
}


test_verify_one_file_with_options! {
    // `&mut v[i]` calls `<Vec<T> as IndexMut<usize>>::index_mut`, which drops nothing; writing
    // over the element (`v[0] = x`) still drops the old one in this function, which is rejected
    // (portable-fip, 2026-11-10 vec-index-mut request)
    #[test] fip_strict_vec_index_mut ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::AllocFreeDrop;
        #[verifier::fip(strict)]
        pub fn via_index_mut<T: AllocFreeDrop>(v: &mut Vec<T>, w: &mut T)
            requires old(v)@.len() >= 1,
            allocates 0
        {
            ::core::mem::swap(&mut v[0], w);
        }
        #[verifier::fip(strict)]
        pub fn range_index_mut<T: AllocFreeDrop>(v: &mut Vec<T>) -> (r: usize)
            requires old(v)@.len() >= 1,
            allocates 0
        {
            let s = &mut v[0..1];
            s.len()
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fip_strict_vec_index_assign_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::{AllocFreeDrop, NoDeallocDrop};
        #[verifier::fip(strict)]
        pub fn overwrite<T: AllocFreeDrop + NoDeallocDrop>(v: &mut Vec<T>, x: T)
            requires old(v)@.len() >= 1,
            allocates 0
        {
            v[0] = x;
        }
    } => Err(err) => assert_vir_error_msg(err, "it drops a value of type `T`, whose destructor is not known here")
}

test_verify_one_file_with_options! {
    // the examples of the guide's "FIP and FBIP" page (docs/guide/src/fip-fbip.md)
    #[test] fip_guide_examples ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        pub enum List { Nil, Cons(u64, Box<List>) }
        pub open spec fn len(l: List) -> nat
            decreases l
        {
            match l { List::Nil => 0, List::Cons(_, t) => 1 + len(*t) }
        }
        fn push_one(v: &mut Vec<u64>)
            allocates 1
        {
            v.push(1);
        }
        #[verifier::fip]
        fn halve(mut b: Box<List>) -> (r: Box<List>) {
            match &mut *b {
                List::Cons(x, _) => { *x = *x / 2; }
                List::Nil => {}
            }
            b
        }
        #[verifier::fip]
        fn reverse(l: List, acc: List) -> (r: List)
            ensures len(r) == len(l) + len(acc),
            decreases l
        {
            match l {
                List::Nil => acc,
                List::Cons(x, mut b) => {
                    let next = core::mem::replace(&mut *b, acc);
                    reverse(next, List::Cons(x, b))
                }
            }
        }
        #[verifier::fip]
        fn cons(x: u64, l: List) -> (r: List)
            allocates 1
        {
            List::Cons(x, Box::new(l))
        }
        #[verifier::fip(strict)]
        fn reverse_strict(l: List, acc: List) -> (r: List)
            ensures len(r) == len(l) + len(acc),
            decreases l
        {
            match l {
                List::Nil => acc,
                List::Cons(x, mut b) => {
                    let next = core::mem::replace(&mut *b, acc);
                    become reverse_strict(next, List::Cons(x, b))
                }
            }
        }
        #[verifier::fip]
        fn first<T: vstd::alloc_check::NoDeallocDrop>(a: T, b: T) -> (r: T) {
            a
        }
        #[verifier::fip(strict)]
        fn swap_ends<T: vstd::alloc_check::AllocFreeDrop>(xs: &mut [T])
            requires old(xs)@.len() >= 2,
            allocates 0
        {
            let n = xs.len();
            xs.swap(0, n - 1);
        }
        #[verifier::fip]
        fn fill(hole: &mut List, v: List)
            requires *old(hole) is Nil,
        {
            core::mem::forget(core::mem::replace(hole, v));
        }

        // fip-fbip.md, operator markers
        #[verifier::fip]
        fn larger<'a, T: vstd::alloc_check::FipOrd>(a: &'a T, b: &'a T) -> &'a T {
            if a < b { b } else { a }
        }

        // reference-allocates.md, operator traits
        #[verifier::fip]
        fn lt_gen<T: vstd::alloc_check::FipOrd>(a: &T, b: &T) -> bool {
            a < b
        }

        #[verifier::fip(strict)]
        fn eq_gen<T: vstd::alloc_check::FipStrictPartialEq>(a: &T, b: &T) -> bool {
            a == b
        }
    } => Ok(())
}

// Marker traits for core's operator traits (`vstd::alloc_check::{FbipOp, FipOp, FipStrictOp}`): a
// generic call of an operator trait's method is charged 0 through `FbipOp`, may be made in a fip
// function through `FipOp`, and in a strict one through `FipStrictOp`
test_verify_one_file_with_options! {
    #[test] fip_op_markers_generic_calls ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;
        use vstd::std_specs::ops::AddSpec;

        pub struct L { pub x: u64 }
        impl PartialEq for L {
            #[verifier::fip]
            fn eq(&self, o: &L) -> bool allocates 0 { self.x == o.x }
        }
        impl vstd::std_specs::cmp::PartialEqSpecImpl for L {
            open spec fn obeys_eq_spec() -> bool { false }
            open spec fn eq_spec(&self, other: &L) -> bool { self.x == other.x }
        }
        unsafe impl FbipPartialEq for L {}
        unsafe impl FipPartialEq for L {}

        #[verifier::fip]
        fn add_gen<T: FipAdd<Output = T> + NoDeallocDrop>(a: T, b: T) -> T
            requires a.add_req(b),
        {
            a + b
        }

        fn add_counted<T: FbipAdd<Output = T> + AllocFreeDrop>(a: T, b: T) -> T
            requires a.add_req(b),
            allocates 0
        {
            a + b
        }

        #[verifier::fip]
        fn eq_gen<T: FipPartialEq>(a: &T, b: &T) -> bool {
            a == b
        }

        #[verifier::fip]
        fn lt_gen<T: FipOrd>(a: &T, b: &T) -> bool {
            a < b
        }

        #[verifier::fip]
        fn cmp_gen<T: FipOrd>(a: &T, b: &T) -> core::cmp::Ordering {
            a.cmp(b)
        }

        #[verifier::fip]
        fn uses() -> bool {
            let a = add_gen(1u64, 2u64);
            let l = L { x: a };
            let m = L { x: 3 };
            let _o = cmp_gen(&1u8, &2u8);
            eq_gen(&l, &m) && lt_gen(&1u8, &2u8)
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fip_op_markers_missing_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        #[verifier::fip]
        fn eq_gen<T: PartialEq>(a: &T, b: &T) -> bool {
            a == b
        }
    } => Err(err) => assert_any_vir_error_msg(err, "this call may deallocate memory")
}

test_verify_one_file_with_options! {
    #[test] fip_op_marker_impl_not_fip_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        pub struct L { pub x: u64 }
        impl PartialEq for L {
            fn eq(&self, o: &L) -> bool allocates 0 { self.x == o.x }
        }
        unsafe impl FbipPartialEq for L {}
        unsafe impl FipPartialEq for L {}
    } => Err(err) => assert_vir_error_msg(err, "this `vstd::alloc_check::FipPartialEq` impl is not accepted")
}

test_verify_one_file_with_options! {
    #[test] fip_op_marker_impl_allocates_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        pub struct L { pub x: u64 }
        impl PartialEq for L {
            fn eq(&self, o: &L) -> bool allocates 1 { self.x == o.x }
        }
        unsafe impl FbipPartialEq for L {}
    } => Err(err) => assert_vir_error_msg(err, "must be checked by Verus and bounded by `allocates 0`")
}

test_verify_one_file_with_options! {
    #[test] fip_op_marker_impl_derived_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        #[derive(PartialEq)]
        pub struct L { pub x: u64 }
        unsafe impl FbipPartialEq for L {}
    } => Err(err) => assert_vir_error_msg(err, "-V alloc-check: ")
}

test_verify_one_file_with_options! {
    #[test] fip_op_marker_impl_not_strict_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        pub struct L { pub x: u64 }
        impl PartialEq for L {
            #[verifier::fip]
            fn eq(&self, o: &L) -> bool allocates 0 { self.x == o.x }
        }
        unsafe impl FbipPartialEq for L {}
        unsafe impl FipPartialEq for L {}
        unsafe impl FipStrictPartialEq for L {}
    } => Err(err) => assert_vir_error_msg(err, "must be `#[verifier::fip(strict)]`")
}

test_verify_one_file_with_options! {
    #[test] fip_strict_op_markers ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        #[verifier::fip(strict)]
        fn cmp_gen<T: FipStrictOrd>(a: &T, b: &T) -> core::cmp::Ordering {
            a.cmp(b)
        }

        #[verifier::fip(strict)]
        fn eq_gen<T: FipStrictPartialEq>(a: &T, b: &T) -> bool {
            a == b
        }

        #[verifier::fip(strict)]
        fn uses() -> bool {
            let _o = cmp_gen(&1u64, &2u64);
            eq_gen(&1u8, &1u8)
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fip_strict_op_marker_not_strict_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        #[verifier::fip(strict)]
        fn cmp_gen<T: FipOrd>(a: &T, b: &T) -> core::cmp::Ordering {
            a.cmp(b)
        }
    } => Err(err) => assert_vir_error_msg(err, "whose callee is not known here")
}

test_verify_one_file_with_options! {
    #[test] fip_strict_op_marker_max_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        #[verifier::fip(strict)]
        fn max_gen<T: FipStrictOrd + Copy>(a: T, b: T) -> T {
            a.max(b)
        }
    } => Err(err) => assert_vir_error_msg(err, "whose callee is not known here")
}

// `L::eq` calls `same::<L>`, which calls `L::eq` again: within one crate, the verifier already
// rejects the cycle (the compiled-program check would too: a strict generic function's call
// through a marker may reach any strict method of this crate's impls of the operator trait)
test_verify_one_file_with_options! {
    #[test] fip_strict_op_marker_cycle_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        pub struct L { pub x: u64 }
        impl PartialEq for L {
            #[verifier::fip(strict)]
            #[verifier::exec_allows_no_decreases_clause]
            fn eq(&self, o: &L) -> bool allocates 0 { same(self, o) }
        }
        unsafe impl FbipPartialEq for L {}
        unsafe impl FipPartialEq for L {}
        unsafe impl FipStrictPartialEq for L {}

        #[verifier::fip(strict)]
        #[verifier::exec_allows_no_decreases_clause]
        fn same<T: FipStrictPartialEq>(a: &T, b: &T) -> bool allocates 0 {
            let r = a == b;
            r
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

// A strict function of another crate, generic through a marker, instantiated with a type of this
// crate: its calls of the type's methods are calls back into this crate
#[test]
fn fip_strict_op_marker_across_crates() {
    let tempdir = tempfile::TempDir::new().expect("temp dir");
    let dir = tempdir.path();
    let pre = format!("{}\nuse vstd::prelude::*;\nuse vstd::alloc_check::*;\n", FEATURE_PRELUDE);
    std::fs::write(
        dir.join("lib.rs"),
        format!(
            "{pre}verus! {{
#[verifier::fip(strict)]
pub fn same<T: FipStrictPartialEq>(a: &T, b: &T) -> (r: bool) allocates 0 {{ let r = a == b; r }}
}}
"
        ),
    )
    .expect("write");
    let lib = run_verus_raw(
        &["--crate-type=lib", "lib.rs", "-V", "alloc-check", "--compile", "--export", "lib.vir"],
        dir,
    );
    assert!(lib.status.success(), "lib:\n{}", String::from_utf8_lossy(&lib.stderr));
    let run = |name: &str, body: &str| {
        std::fs::write(dir.join(format!("{name}.rs")), format!("{pre}verus!{{ {body} }}\n"))
            .expect("write");
        let out = run_verus_raw(
            &[
                "--crate-type=lib",
                &format!("{name}.rs"),
                "-V",
                "alloc-check",
                "--compile",
                "--import",
                "lib=lib.vir",
                "--extern",
                "lib=liblib.rlib",
            ],
            dir,
        );
        (out.status.success(), String::from_utf8_lossy(&out.stderr).to_string())
    };
    let l = |eq_body: &str| {
        format!(
            "pub struct L {{ pub x: u64 }}
impl PartialEq for L {{
    #[verifier::fip(strict)]
    #[verifier::exec_allows_no_decreases_clause]
    fn eq(&self, o: &L) -> bool allocates 0 {{ {eq_body} }}
}}
impl vstd::std_specs::cmp::PartialEqSpecImpl for L {{
    open spec fn obeys_eq_spec() -> bool {{ false }}
    open spec fn eq_spec(&self, other: &L) -> bool {{ self.x == other.x }}
}}
unsafe impl FbipPartialEq for L {{}}
unsafe impl FipPartialEq for L {{}}
unsafe impl FipStrictPartialEq for L {{}}
"
        )
    };
    let (ok, e) = run(
        "ok",
        &format!(
            "{}
#[verifier::fip(strict)] fn s(a: &L, b: &L) -> (r: bool) allocates 0 {{ lib::same(a, b) }}",
            l("self.x == o.x")
        ),
    );
    assert!(ok, "{}", e);
    // (the verifier rejects the cycle through the trait bound first; the compiled-program check,
    // which follows `lib::same::<L>`'s bounds back to `L::eq`, would too)
    let (ok, e) = run("cyc", &l("let r = lib::same(self, o); r"));
    assert!(
        !ok && (e.contains("is not a tail call and can lead back to")
            || e.contains("found a cyclic self-reference in a definition")),
        "{}",
        e
    );
}

// std's functions that compare their arguments (`contains`, `Option::eq`, `sort_unstable`, ...)
// deallocate only if a comparison does: their `deallocates_when` conditions name the comparison
// markers (`partial_eq_is_fip`, `ord_is_fip`, ...)
test_verify_one_file_with_options! {
    #[test] fip_std_comparisons_through_markers ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        pub struct L { pub x: u64 }
        impl PartialEq for L {
            #[verifier::fip]
            fn eq(&self, o: &L) -> bool allocates 0 { self.x == o.x }
        }
        impl vstd::std_specs::cmp::PartialEqSpecImpl for L {
            open spec fn obeys_eq_spec() -> bool { false }
            open spec fn eq_spec(&self, other: &L) -> bool { self.x == other.x }
        }
        unsafe impl FbipPartialEq for L {}
        unsafe impl FipPartialEq for L {}

        #[verifier::fip]
        fn has<T: FipPartialEq>(s: &[T], x: &T) -> bool {
            s.contains(x)
        }

        #[verifier::fip]
        fn ends<T: FipPartialEq>(s: &[T], p: &[T]) -> bool {
            s.starts_with(p) && s.ends_with(p)
        }

        #[verifier::fip]
        fn opt_eq<T: FipPartialEq>(a: &Option<T>, b: &Option<T>) -> bool {
            a == b
        }

        #[verifier::fip]
        fn opt_cmp<T: FipOrd>(a: &Option<T>, b: &Option<T>) -> core::cmp::Ordering {
            a.cmp(b)
        }

        #[verifier::fip]
        fn sort_it<T: FipOrd>(v: &mut [T]) {
            v.sort_unstable();
        }

        #[verifier::fip]
        fn find<T: FipOrd>(v: &[T], x: &T) -> bool {
            match v.binary_search(x) {
                Ok(_) => true,
                Err(_) => false,
            }
        }

        #[verifier::fip]
        fn in_range(r: &core::ops::Range<u64>, x: &u64) -> bool {
            r.contains(x)
        }

        #[verifier::fip]
        fn bigger<T: FipOrd>(a: T, b: T) -> T {
            core::cmp::max(a, b)
        }

        #[verifier::fip]
        fn uses(v: &mut [u64], l: &[L], k: &L) -> bool {
            sort_it(v);
            has(l, k) && opt_eq(&Some(1u8), &None)
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fip_std_comparison_without_marker_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        #[verifier::fip]
        fn has<T: PartialEq>(s: &[T], x: &T) -> bool {
            s.contains(x)
        }
    } => Err(err) => assert_any_vir_error_msg(err, "this call may deallocate memory")
}

test_verify_one_file_with_options! {
    #[test] fip_strict_std_comparisons_through_markers ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        #[verifier::fip(strict)]
        fn sort_it<T: FipStrictOrd>(v: &mut [T]) {
            v.sort_unstable();
        }

        #[verifier::fip(strict)]
        fn has<T: FipStrictPartialEq>(s: &[T], x: &T) -> bool {
            s.contains(x)
        }

        #[verifier::fip(strict)]
        fn uses(v: &mut [u64]) -> bool {
            sort_it(v);
            has(v, &1)
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fip_strict_std_comparison_not_strict_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        #[verifier::fip(strict)]
        fn sort_it<T: FipOrd>(v: &mut [T]) {
            v.sort_unstable();
        }
    } => Err(err) => assert_any_vir_error_msg(err, "which may call the methods of `T: std::cmp::Ord`, which are not known here")
}

// `Clone` has markers like the operator traits (`FbipClone`, `FipClone`, `FipStrictClone`; vstd
// implements them for the primitive types, `f32` and `f64` included): a generic `clone` through
// them is charged 0, may be made in a fip function, and in a strict one
test_verify_one_file_with_options! {
    #[test] fip_clone_markers_generic_calls ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        pub struct L { pub x: u64 }
        impl Clone for L {
            #[verifier::fip(strict)]
            fn clone(&self) -> L allocates 0 { L { x: self.x } }
        }
        unsafe impl AllocFreeDrop for L {}
        unsafe impl NoDeallocDrop for L {}
        unsafe impl FbipClone for L {}
        unsafe impl FipClone for L {}
        unsafe impl FipStrictClone for L {}

        fn counted<T: FbipClone>(a: &T) -> T allocates 0 {
            a.clone()
        }

        #[verifier::fip]
        fn dup<T: FipClone>(a: &T) -> (T, T) {
            (a.clone(), a.clone())
        }

        #[verifier::fip(strict)]
        fn dup_strict<T: FipStrictClone>(a: &T) -> T {
            a.clone()
        }

        #[verifier::fip(strict)]
        fn uses(l: &L, f: f64) -> u64 {
            let _a = dup_strict(&1u64);
            let _f = dup_strict(&f);
            let _b = dup_strict(&true);
            let m = dup_strict(l);
            m.x
        }

        #[verifier::fip]
        fn uses_fip(l: &L) -> u64 {
            let (a, _b) = dup(l);
            a.x
        }

        fn uses_counted(l: &L) -> u64 allocates 0 {
            let _c = counted(&7u8);
            counted(l).x
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fip_clone_marker_missing_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        #[verifier::fip]
        fn dup<T: Clone + vstd::alloc_check::NoDeallocDrop>(a: &T) -> T {
            a.clone()
        }
    } => Err(err) => assert_any_vir_error_msg(err, "this call may deallocate memory")
}

test_verify_one_file_with_options! {
    #[test] fip_clone_marker_impl_allocates_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        pub struct L { pub x: u64 }
        impl Clone for L {
            fn clone(&self) -> L allocates 1 { L { x: self.x } }
        }
        unsafe impl AllocFreeDrop for L {}
        unsafe impl FbipClone for L {}
    } => Err(err) => assert_vir_error_msg(err, "must be checked by Verus and bounded by `allocates 0`")
}

test_verify_one_file_with_options! {
    #[test] fip_clone_marker_impl_not_strict_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        pub struct L { pub x: u64 }
        impl Clone for L {
            #[verifier::fip]
            fn clone(&self) -> L allocates 0 { L { x: self.x } }
        }
        unsafe impl AllocFreeDrop for L {}
        unsafe impl NoDeallocDrop for L {}
        unsafe impl FbipClone for L {}
        unsafe impl FipClone for L {}
        unsafe impl FipStrictClone for L {}
    } => Err(err) => assert_vir_error_msg(err, "must be `#[verifier::fip(strict)]`")
}

// `<[T]>::to_vec` and `Box<[T]>::from(&[T])` allocate once and clone each element: a strict
// function may call them through `FipStrictClone` (Verigrad's `copy_on_shared`), and the result
// equals the input when `T::clone` returns its argument (a precondition that the callers discharge
// for `i32` and `f64` from vstd's specifications of their `clone`)
test_verify_one_file_with_options! {
    #[test] fip_strict_slice_to_vec ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        #[verifier::fip(strict)]
        pub fn copy_gen<T: Copy + AllocFreeDrop + FipStrictClone>(src: &[T]) -> (r: Vec<T>)
            requires
                forall|a: T, b: T| call_ensures(T::clone, (&a,), b) ==> a == b,
            ensures
                r@ == src@,
            allocates
                if src@.len() == 0 { 0int } else { 1int },
        {
            src.to_vec()
        }

        #[verifier::fip(strict)]
        pub fn copy_boxed<T: Copy + AllocFreeDrop + FipStrictClone>(src: &[T]) -> (r: Vec<T>)
            requires
                forall|a: T, b: T| call_ensures(T::clone, (&a,), b) ==> a == b,
            ensures
                r@ == src@,
            allocates
                if src@.len() == 0 { 0int } else { 1int },
        {
            Box::<[T]>::from(src).into_vec()
        }

        #[verifier::fip(strict)]
        pub fn copy_to_vec(src: &[i32]) -> (r: Vec<i32>)
            ensures
                r@ == src@,
            allocates
                if src@.len() == 0 { 0int } else { 1int },
        {
            src.to_vec()
        }

        #[verifier::fip(strict)]
        pub fn uses(a: &[i32], b: &[f64]) -> (r: (Vec<i32>, Vec<f64>))
            ensures
                r.0@ == a@,
                r.1@ == b@,
            allocates
                2,
        {
            (copy_gen(a), copy_boxed(b))
        }
    } => Ok(())
}

// `x.into()` through std's blanket `impl<T, U: From<T>> Into<U> for T` is `U::from(x)`, so it
// gets the specification of the `From` impl (when that is known): its `deallocates_when` for a fip
// function, and its "drops nothing" for a strict one
test_verify_one_file_with_options! {
    #[test] fip_into_forwards_to_from ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        #[verifier::fip(strict)]
        pub fn copy_into<T: Copy + AllocFreeDrop + FipStrictClone>(src: &[T]) -> (r: Vec<T>)
            requires
                forall|a: T, b: T| call_ensures(T::clone, (&a,), b) ==> a == b,
            ensures
                r@ == src@,
            allocates
                if src@.len() == 0 { 0int } else { 1int },
        {
            let b: Box<[T]> = src.into();
            b.into_vec()
        }

        #[verifier::fip(strict)]
        pub fn boxed(src: &[i32]) -> (r: Box<[i32]>)
            ensures
                r@ == src@,
            allocates
                if src@.len() == 0 { 0int } else { 1int },
        {
            src.into()
        }

        pub struct A { pub x: u8 }
        pub struct B { pub x: u8 }
        impl From<A> for B {
            #[verifier::fip]
            fn from(a: A) -> B allocates 0 { B { x: a.x } }
        }
        impl vstd::std_specs::convert::FromSpecImpl<A> for B {
            open spec fn obeys_from_spec() -> bool { true }
            open spec fn from_spec(a: A) -> B { B { x: a.x } }
        }

        #[verifier::fip]
        fn to_b(a: A) -> (r: B) ensures r.x == a.x allocates 0 {
            a.into()
        }

        #[verifier::fip]
        fn same(a: u64) -> u64 allocates 0 {
            a.into()
        }
    } => Ok(())
}

// `From` and `Into` have markers too; `U: FipFrom<T>` gives `T: FipInto<U>` (std's blanket `Into`
// impl is `U::from(x)`), and vstd marks the reflexive `From<T> for T`
test_verify_one_file_with_options! {
    #[test] fip_from_into_markers ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        pub struct A { pub x: u8 }
        pub struct B { pub x: u8 }
        impl From<A> for B {
            #[verifier::fip(strict)]
            fn from(a: A) -> B allocates 0 { B { x: a.x } }
        }
        impl vstd::std_specs::convert::FromSpecImpl<A> for B {
            open spec fn obeys_from_spec() -> bool { true }
            open spec fn from_spec(a: A) -> B { B { x: a.x } }
        }
        unsafe impl FbipFrom<A> for B {}
        unsafe impl FipFrom<A> for B {}
        unsafe impl FipStrictFrom<A> for B {}
        unsafe impl AllocFreeDrop for A {}
        unsafe impl NoDeallocDrop for A {}
        unsafe impl AllocFreeDrop for B {}
        unsafe impl NoDeallocDrop for B {}

        fn counted<T: AllocFreeDrop, U: FbipFrom<T> + AllocFreeDrop>(t: T) -> U allocates 0 {
            t.into()
        }

        #[verifier::fip]
        fn by_into<T: NoDeallocDrop, U: FipFrom<T> + NoDeallocDrop>(t: T) -> U {
            t.into()
        }

        #[verifier::fip]
        fn by_from<T: NoDeallocDrop, U: FipFrom<T> + NoDeallocDrop>(t: T) -> U {
            U::from(t)
        }

        #[verifier::fip]
        fn by_into_bound<T: FipInto<U> + NoDeallocDrop, U: NoDeallocDrop>(t: T) -> U {
            t.into()
        }

        #[verifier::fip(strict)]
        fn by_into_strict<T: NoDeallocDrop, U: FipStrictFrom<T> + NoDeallocDrop>(t: T) -> U {
            t.into()
        }

        #[verifier::fip(strict)]
        fn by_into_bound_strict<T: FipStrictInto<U> + NoDeallocDrop, U: NoDeallocDrop>(t: T) -> U {
            t.into()
        }

        #[verifier::fip(strict)]
        fn uses(a: A, a2: A, a3: A, n: u64) -> u8 {
            let b: B = by_into_strict(a);
            let c: B = by_into_bound_strict(a2);
            let d: u64 = by_into_strict(n);
            let _e: u64 = by_into_bound_strict(d);
            let f: B = by_into_strict(a3);
            b.x ^ c.x ^ f.x
        }

        #[verifier::fip]
        fn uses_fip(a: A, a2: A, a3: A) -> u8 {
            let b: B = by_into(a);
            let c: B = by_from(a2);
            let d: B = by_into_bound(a3);
            b.x ^ c.x ^ d.x
        }

        fn uses_counted(a: A) -> u8 allocates 0 {
            let b: B = counted(a);
            b.x
        }
    } => Ok(())
}

// An `Into` impl that a crate writes itself (without `From`) can have the `Into` markers, checked
// like the others (they do not conflict with vstd's impls through `From`)
test_verify_one_file_with_options! {
    #[test] fip_into_markers_on_direct_into_impl ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        pub struct A { pub x: u8 }
        pub struct C { pub x: u8 }
        impl Into<C> for A {
            #[verifier::fip(strict)]
            fn into(self) -> C allocates 0 { C { x: self.x } }
        }
        impl vstd::std_specs::convert::IntoSpecImpl<C> for A {
            open spec fn obeys_into_spec() -> bool { true }
            open spec fn into_spec(self) -> C { C { x: self.x } }
        }
        unsafe impl FbipInto<C> for A {}
        unsafe impl FipInto<C> for A {}
        unsafe impl FipStrictInto<C> for A {}
        unsafe impl AllocFreeDrop for A {}
        unsafe impl NoDeallocDrop for A {}
        unsafe impl AllocFreeDrop for C {}
        unsafe impl NoDeallocDrop for C {}

        #[verifier::fip(strict)]
        fn by_into_bound_strict<T: FipStrictInto<U> + NoDeallocDrop, U: NoDeallocDrop>(t: T) -> U {
            t.into()
        }

        #[verifier::fip(strict)]
        fn uses(a: A, a2: A) -> (r: u8)
            ensures r == a.x,
        {
            let c: C = by_into_bound_strict(a2);
            let d: C = a.into();
            let _ = c;
            d.x
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fip_into_marker_impl_not_fip_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        pub struct A { pub x: u8 }
        pub struct C { pub x: u8 }
        impl Into<C> for A {
            fn into(self) -> C allocates 0 { C { x: self.x } }
        }
        unsafe impl FbipInto<C> for A {}
        unsafe impl FipInto<C> for A {}
    } => Err(err) => assert_vir_error_msg(err, "this `vstd::alloc_check::FipInto` impl is not accepted")
}

test_verify_one_file_with_options! {
    #[test] fip_into_without_marker_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        #[verifier::fip]
        fn by_into<T: Into<U> + vstd::alloc_check::NoDeallocDrop, U: vstd::alloc_check::NoDeallocDrop>(t: T) -> U {
            t.into()
        }
    } => Err(err) => assert_any_vir_error_msg(err, "this call may deallocate memory")
}

test_verify_one_file_with_options! {
    #[test] fip_from_marker_impl_not_strict_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        pub struct A { pub x: u8 }
        pub struct B { pub x: u8 }
        impl From<A> for B {
            #[verifier::fip]
            fn from(a: A) -> B allocates 0 { B { x: a.x } }
        }
        unsafe impl FbipFrom<A> for B {}
        unsafe impl FipFrom<A> for B {}
        unsafe impl FipStrictFrom<A> for B {}
    } => Err(err) => assert_vir_error_msg(err, "must be `#[verifier::fip(strict)]`")
}

test_verify_one_file_with_options! {
    #[test] fip_strict_into_marker_not_strict_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        #[verifier::fip(strict)]
        fn by_into<T: NoDeallocDrop, U: FipFrom<T> + NoDeallocDrop>(t: T) -> U {
            t.into()
        }
    } => Err(err) => assert_any_vir_error_msg(err, "which may call the methods of `U: std::convert::From`, which are not known here")
}

test_verify_one_file_with_options! {
    #[test] fip_into_forward_without_marker_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        #[verifier::fip]
        fn boxed<T: Clone + NoDeallocDrop>(src: &[T]) -> Box<[T]> {
            src.into()
        }
    } => Err(err) => assert_any_vir_error_msg(err, "this call may deallocate memory")
}

test_verify_one_file_with_options! {
    #[test] fip_strict_into_forward_not_strict_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        #[verifier::fip(strict)]
        fn boxed<T: FipClone>(src: &[T]) -> Box<[T]>
            allocates if src@.len() == 0 { 0int } else { 1int },
        {
            src.into()
        }
    } => Err(err) => assert_any_vir_error_msg(err, "which may call the methods of `T: std::clone::Clone`, which are not known here")
}

// A `From` impl that Verus does not know: `into` keeps the blanket impl's specification (as before)
test_verify_one_file_with_options! {
    #[test] into_of_unknown_from_impl_still_accepted ["vstd"] => verus_code! {
        use vstd::prelude::*;

        pub struct A { pub x: u8 }
        pub struct B { pub x: u8 }
        #[verifier::external]
        impl From<A> for B {
            fn from(a: A) -> B { B { x: a.x } }
        }

        fn to_b(a: A) -> B {
            a.into()
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fip_slice_to_vec_without_marker_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        #[verifier::fip]
        fn copy<T: Clone + vstd::alloc_check::NoDeallocDrop>(s: &[T]) -> Vec<T> {
            s.to_vec()
        }
    } => Err(err) => assert_any_vir_error_msg(err, "this call may deallocate memory")
}

test_verify_one_file_with_options! {
    #[test] fip_strict_slice_to_vec_not_strict_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        #[verifier::fip(strict)]
        fn copy<T: FipClone>(s: &[T]) -> Vec<T>
            allocates if s@.len() == 0 { 0int } else { 1int },
        {
            s.to_vec()
        }
    } => Err(err) => assert_any_vir_error_msg(err, "which may call the methods of `T: std::clone::Clone`, which are not known here")
}

// `as` casts to and from floats, pointer casts, array indexing, array fill and the array -> slice
// coercions are instructions, not calls: vstd's internal functions for them (`float_cast`,
// `cast_ptr_to_usize`, `array_index_get`, `array_fill_for_copy_types`, `array_as_slice`,
// `ref_mut_array_unsizing_coercion`) allocate nothing, free nothing and drop nothing, so bounded,
// fip and strict functions may use them. (Before: "cannot bound the allocations of this call:
// `vstd::float::float_cast` has no `allocates` specification", and "`vstd::array::array_as_slice`
// is not `#[verifier::fip]` and has no `deallocates_when` condition".)
test_verify_one_file_with_options! {
    #[test] fip_casts_and_array_coercions_accepted ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        fn cast(n: usize) -> (r: f64)
            no_unwind
            allocates 0
        {
            n as f64
        }

        #[verifier::fip(strict)]
        fn narrow(x: f64) -> (r: f32)
            no_unwind
            allocates 0
        {
            x as f32
        }

        #[verifier::fip(strict)]
        fn to_int(x: f64) -> (r: i32)
            no_unwind
            allocates 0
        {
            x as i32
        }

        #[verifier::fip(strict)]
        fn first_mut(a: &mut [i32; 4]) -> (r: i32)
            allocates 0
        {
            let s: &mut [i32] = a;
            s[0]
        }

        #[verifier::fip(strict)]
        fn first_shared(a: &[i32; 4]) -> (r: i32)
            allocates 0
        {
            let s: &[i32] = a;
            s[0]
        }

        #[verifier::fip(strict)]
        fn third(a: &[u8; 4]) -> (r: u8)
            no_unwind
            allocates 0
        {
            a[2]
        }

        #[verifier::fip(strict)]
        fn fill(x: u8) -> (r: [u8; 8])
            no_unwind
            allocates 0
        {
            [x; 8]
        }

        #[verifier::fip(strict)]
        fn address(p: *mut u32) -> (r: usize)
            no_unwind
            allocates 0
        {
            p as usize
        }
    } => Ok(())
}

// The casts are still charged: a function that allocates next to one keeps its bound.
test_verify_one_file_with_options! {
    #[test] fip_cast_does_not_hide_an_allocation ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        fn boxed(n: usize) -> (r: Box<f64>)
            allocates 0 // FAILS
        {
            Box::new(n as f64)
        }
    } => Err(err) => assert_one_fails(err)
}

// `#[verifier::fip]` on a trait method declaration is a contract: a generic call of the method
// is accepted in a fip function, and every implementation must be `#[verifier::fip]` itself, so
// that its calls and its drops are checked. (Before, the generic call was accepted while an
// implementation without the attribute was not checked: it could free memory.)
test_verify_one_file_with_options! {
    #[test] fip_trait_method_contract_accepted ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        pub trait T {
            #[verifier::fip]
            fn f(&self, x: u64) -> u64;

            // a default body is checked where it is declared
            #[verifier::fip]
            fn g(&self, x: u64) -> (r: u64) {
                x
            }
        }

        pub struct S;

        impl T for S {
            #[verifier::fip]
            fn f(&self, x: u64) -> u64 {
                x / 2
            }
        }

        #[verifier::fip]
        pub fn generic<A: T>(a: &A, x: u64) -> u64 {
            a.f(x)
        }

        #[verifier::fip]
        pub fn caller(x: u64) -> u64 {
            generic(&S, x)
        }

        // the inherited default body of a concrete type
        #[verifier::fip]
        pub fn inherited(s: &S, x: u64) -> u64 {
            s.g(x)
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fip_trait_method_impl_without_attribute_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        pub trait T {
            #[verifier::fip]
            fn f(&self, x: u64) -> u64;
        }

        pub struct S;

        impl T for S {
            // not fip, and it frees a box
            fn f(&self, x: u64) -> u64 {
                let b: Option<Box<u64>> = None;
                x
            }
        }

        #[verifier::fip]
        pub fn generic<A: T>(a: &A, x: u64) -> u64 {
            a.f(x)
        }
    } => Err(err) => assert_vir_error_msg(err, "the implementation must be `#[verifier::fip]` too")
}

test_verify_one_file_with_options! {
    #[test] fip_trait_method_impl_that_frees_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        pub trait T {
            #[verifier::fip]
            fn f(&self, x: u64) -> u64;
        }

        pub struct S;

        impl T for S {
            #[verifier::fip]
            fn f(&self, x: u64) -> u64 {
                let b: Option<Box<u64>> = None;
                x
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "is dropped here")
}

test_verify_one_file_with_options! {
    #[test] fip_strict_trait_method_impl_must_be_strict ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        pub trait T {
            #[verifier::fip(strict)]
            fn f(&self, x: u64) -> u64;
        }

        pub struct S;

        impl T for S {
            #[verifier::fip]
            fn f(&self, x: u64) -> u64 {
                x
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "the implementation must be `#[verifier::fip(strict)]` too")
}

test_verify_one_file_with_options! {
    #[test] fip_trait_method_default_body_that_frees_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        pub trait K {
            #[verifier::fip]
            fn m(&self, x: u64) -> (r: u64) {
                let b: Option<Box<u64>> = None;
                x
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "is dropped here")
}

// The guide's example of a generic call of a fip trait method (fip-fbip.md, "Generic code").
test_verify_one_file_with_options! {
    #[test] fip_guide_trait_method_example ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        pub trait Shape {
            #[verifier::fip]
            fn area(&self) -> u64;
        }

        #[verifier::fip]
        fn double<S: Shape>(s: &S) -> (r: u64) {
            s.area().wrapping_mul(2)
        }
    } => Ok(())
}

// `Vec<T>: From<&[T]>` (and `&mut [T]`, `&[T; N]`) is `to_vec`, so `src.into()` and
// `Vec::from(src)` have its specification; `into` reaches it through std's blanket `Into` impl.
test_verify_one_file_with_options! {
    #[test] fip_vec_from_slice ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        pub fn a_into(src: &[i32]) -> (r: Vec<i32>)
            ensures
                r@ == src@,
            allocates
                if src@.len() == 0 { 0int } else { 1int },
        {
            src.into()
        }

        pub fn vec_from(src: &[i32]) -> (r: Vec<i32>)
            ensures
                r@ == src@,
            allocates
                if src@.len() == 0 { 0int } else { 1int },
        {
            Vec::from(src)
        }

        #[verifier::fip(strict)]
        pub fn into_gen<T: Copy + AllocFreeDrop + FipStrictClone>(src: &[T]) -> (r: Vec<T>)
            requires
                forall|a: T, b: T| call_ensures(T::clone, (&a,), b) ==> a == b,
            ensures
                r@ == src@,
            allocates
                if src@.len() == 0 { 0int } else { 1int },
        {
            src.into()
        }

        #[verifier::fip(strict)]
        pub fn from_mut(src: &mut [u64]) -> (r: Vec<u64>)
            ensures
                r@ == old(src)@,
                final(src)@ == old(src)@,
            allocates
                if old(src)@.len() == 0 { 0int } else { 1int },
        {
            Vec::from(src)
        }

        #[verifier::fip(strict)]
        pub fn from_array(src: &[u8; 4]) -> (r: Vec<u8>)
            ensures
                r@ == src@,
            allocates
                1int,
        {
            Vec::from(src)
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fip_vec_from_slice_without_marker_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        #[verifier::fip(strict)]
        pub fn into_gen<T: Copy + AllocFreeDrop>(src: &[T]) -> (r: Vec<T>)
            allocates
                if src@.len() == 0 { 0int } else { 1int },
        {
            src.into()
        }
    } => Err(err) => assert_any_vir_error_msg(err, "this call may deallocate memory")
}

// A derived `clone` whose body is `*self` (`#[derive(Clone, Copy)]` on a type without type
// parameters) is `#[verifier::fip(strict)]` with `allocates 0`.
test_verify_one_file_with_options! {
    #[test] fip_derived_copy_clone ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        #[derive(Clone, Copy)]
        pub struct D { pub x: u32 }

        unsafe impl AllocFreeDrop for D {}
        unsafe impl NoDeallocDrop for D {}
        unsafe impl FbipClone for D {}
        unsafe impl FipClone for D {}
        unsafe impl FipStrictClone for D {}

        pub fn one(d: &D) -> (r: D)
            ensures
                r == *d,
            allocates
                0,
        {
            d.clone()
        }

        #[verifier::fip(strict)]
        pub fn one_strict(d: &D) -> (r: D)
            ensures
                r == *d,
        {
            d.clone()
        }

        pub fn slice_bound(s: &[D]) -> (r: Vec<D>)
            ensures
                r@ == s@,
            allocates
                if s@.len() == 0 { 0int } else { 1int },
        {
            s.to_vec()
        }

        #[verifier::fip(strict)]
        pub fn copy_gen<T: Copy + AllocFreeDrop + FipStrictClone>(src: &[T]) -> (r: Vec<T>)
            requires
                forall|a: T, b: T| call_ensures(T::clone, (&a,), b) ==> a == b,
            ensures
                r@ == src@,
            allocates
                if src@.len() == 0 { 0int } else { 1int },
        {
            src.to_vec()
        }

        #[verifier::fip(strict)]
        pub fn uses(s: &[D]) -> (r: Vec<D>)
            ensures
                r@ == s@,
            allocates
                if s@.len() == 0 { 0int } else { 1int },
        {
            copy_gen(s)
        }
    } => Ok(())
}

// A derived `clone` that clones field by field: `allocates 0` and the lowest level of the fields'
// `Clone` markers (where the impl is: a type parameter needs the bound on the type itself, which
// the derived impl copies). At most `#[verifier::fip]` if a field's type has a type parameter.
test_verify_one_file_with_options! {
    #[test] fip_derived_fieldwise_clone ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        #[verifier::allow(autoderive_clone_without_spec)]
        #[derive(Clone)]
        pub struct E<T: Copy + FipStrictClone> { pub x: T }

        impl<T: Copy + FipStrictClone> Copy for E<T> {}

        unsafe impl<T: Copy + FipStrictClone> AllocFreeDrop for E<T> {}
        unsafe impl<T: Copy + FipStrictClone> NoDeallocDrop for E<T> {}
        unsafe impl<T: Copy + FipStrictClone> FbipClone for E<T> {}
        unsafe impl<T: Copy + FipStrictClone> FipClone for E<T> {}

        #[derive(Clone, Copy)]
        pub struct C { pub x: u64 }

        unsafe impl AllocFreeDrop for C {}
        unsafe impl NoDeallocDrop for C {}
        unsafe impl FbipClone for C {}
        unsafe impl FipClone for C {}
        unsafe impl FipStrictClone for C {}

        #[verifier::allow(autoderive_clone_without_spec)]
        #[derive(Clone)]
        pub struct P { pub a: u32, pub b: bool, pub c: C, pub f: f64 }

        unsafe impl AllocFreeDrop for P {}
        unsafe impl NoDeallocDrop for P {}
        unsafe impl FbipClone for P {}
        unsafe impl FipClone for P {}
        unsafe impl FipStrictClone for P {}

        #[verifier::fip]
        pub fn one<T: Copy + FipStrictClone>(e: &E<T>) -> (r: E<T>) {
            e.clone()
        }

        pub fn one_bounded(e: &E<u8>) -> (r: E<u8>)
            allocates
                0,
        {
            e.clone()
        }

        #[verifier::fip(strict)]
        pub fn two(p: &P) -> (r: P) {
            p.clone()
        }

        pub fn slice_bound(s: &[P]) -> (r: Vec<P>)
            allocates
                if s@.len() == 0 { 0int } else { 1int },
        {
            s.to_vec()
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fip_derived_fieldwise_generic_clone_not_strict ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        #[verifier::allow(autoderive_clone_without_spec)]
        #[derive(Clone)]
        pub struct E<T: Copy + FipStrictClone> { pub x: T }

        impl<T: Copy + FipStrictClone> Copy for E<T> {}

        unsafe impl<T: Copy + FipStrictClone> AllocFreeDrop for E<T> {}
        unsafe impl<T: Copy + FipStrictClone> NoDeallocDrop for E<T> {}
        unsafe impl<T: Copy + FipStrictClone> FbipClone for E<T> {}
        unsafe impl<T: Copy + FipStrictClone> FipClone for E<T> {}
        unsafe impl<T: Copy + FipStrictClone> FipStrictClone for E<T> {}
    } => Err(err) => assert_vir_error_msg(err, "must be `#[verifier::fip(strict)]`")
}

// A field of type `F`, whose `clone` is `#[verifier::fip]` but not strict: the derived `clone` is
// `#[verifier::fip]` too, and not strict.
test_verify_one_file_with_options! {
    #[test] fip_derived_fieldwise_clone_level_is_lowest ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        pub struct F { pub x: u32 }

        impl Clone for F {
            #[verifier::fip]
            fn clone(&self) -> (r: F) {
                F { x: self.x }
            }
        }

        unsafe impl AllocFreeDrop for F {}
        unsafe impl NoDeallocDrop for F {}
        unsafe impl FbipClone for F {}
        unsafe impl FipClone for F {}

        #[verifier::allow(autoderive_clone_without_spec)]
        #[derive(Clone)]
        pub struct Q { pub a: u32, pub f: F }

        unsafe impl AllocFreeDrop for Q {}
        unsafe impl NoDeallocDrop for Q {}
        unsafe impl FbipClone for Q {}
        unsafe impl FipClone for Q {}

        #[verifier::fip]
        pub fn one(q: &Q) -> (r: Q) {
            q.clone()
        }

        #[verifier::fip(strict)]
        pub fn one_strict(q: &Q) -> (r: Q) {
            q.clone()
        }
    } => Err(err) => assert_any_vir_error_msg(err, "fip(strict)")
}

// A field whose type has no `Clone` marker: the derived `clone` has no bound, as before.
test_verify_one_file_with_options! {
    #[test] fip_derived_fieldwise_clone_unbounded ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        pub struct H { pub x: u32 }

        impl Clone for H {
            fn clone(&self) -> (r: H)
                allocates
                    1,
            {
                let b = Box::new(1u8);
                H { x: self.x }
            }
        }

        #[verifier::allow(autoderive_clone_without_spec)]
        #[derive(Clone)]
        pub struct D { pub x: u32, pub h: H }

        pub fn one(d: &D) -> (r: D)
            allocates
                0,
        {
            d.clone()
        }
    } => Err(err) => assert_vir_error_msg(err, "has no `allocates` specification")
}

test_verify_one_file_with_options! {
    #[test] fip_derived_fieldwise_clone_marker_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        // (a type parameter without a `Clone` marker in the type's own bounds)
        #[verifier::allow(autoderive_clone_without_spec)]
        #[derive(Clone)]
        pub struct E<T> { pub x: T }

        unsafe impl<T: AllocFreeDrop> AllocFreeDrop for E<T> {}
        unsafe impl<T: FbipClone> FbipClone for E<T> {}
    } => Err(err) => assert_vir_error_msg(err, "must be checked by Verus and bounded by `allocates 0`")
}

// Without -V alloc-check, a derived `clone` is as before.
test_verify_one_file_with_options! {
    #[test] derived_copy_clone_without_alloc_check ["vstd"] => verus_code! {
        use vstd::prelude::*;

        #[derive(Clone, Copy)]
        pub struct D { pub x: u32 }

        pub fn one(d: &D) -> (r: D)
            ensures
                r == *d,
        {
            d.clone()
        }
    } => Ok(())
}

// `deallocates_when` on a trait method declaration: a contract of every implementation (a
// verified one must be fip), which a generic call checks
test_verify_one_file_with_options! {
    #[test] fip_trait_decl_deallocates_when ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use std::alloc::{Allocator, AllocError, Layout};
        use std::ptr::NonNull;

        pub trait Pool {
            fn take(&mut self, n: u64) -> (r: u64)
                allocates 0int deallocates deallocates_when(1int, n > 10);
        }

        pub struct P;

        impl Pool for P {
            #[verifier::fip]
            fn take(&mut self, n: u64) -> (r: u64) {
                n
            }
        }

        #[verifier::fip]
        fn use_generic<T: Pool>(t: &mut T) -> (r: u64) {
            t.take(3)
        }

        #[verifier::fip]
        fn use_p(p: &mut P) -> (r: u64) {
            p.take(20)
        }

        // an allocator's `allocate` never deallocates, also through a generic `A: Allocator`
        #[verifier::fip(strict)]
        fn alloc_generic<A: Allocator>(a: &A, l: Layout) -> (r: Result<NonNull<[u8]>, AllocError>)
            allocates 1
        {
            a.allocate(l)
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fip_trait_decl_deallocates_when_generic_call_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        pub trait Pool {
            fn take(&mut self, n: u64) -> (r: u64)
                allocates 0int deallocates deallocates_when(1int, n > 10);
        }

        #[verifier::fip]
        fn use_generic<T: Pool>(t: &mut T) -> (r: u64) {
            t.take(20)
        }
    } => Err(err) => assert_vir_error_msg(err, "the `deallocates_when` condition of")
}

test_verify_one_file_with_options! {
    // (an implementation that is not fip is counted against the declaration's bound)
    #[test] fip_trait_decl_deallocates_when_impl_not_fip ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        pub trait Pool {
            fn take(&mut self, n: u64) -> (r: u64)
                allocates 0 deallocates deallocates_when(1int, n > 10);
        }

        pub struct P;

        impl Pool for P {
            fn take(&mut self, n: u64) -> (r: u64)
                allocates 0
            {
                n
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // (a default body is counted against the bound, as any verified body)
    #[test] fip_trait_decl_deallocates_when_default_body ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        pub trait Pool {
            fn take(&mut self, n: u64) -> (r: u64)
                allocates 0 deallocates deallocates_when(1int, n > 10)
            {
                n
            }
        }
    } => Ok(())
}

// `f.allocations(args)` / `f.deallocates(args)` (`call_allocations`, `call_deallocates`): a
// specification that forwards to another function can pass on its bound and its deallocation
// condition, also a conditional one
test_verify_one_file_with_options! {
    #[test] fip_call_deallocates_forwarding ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        #[verifier::fip]
        fn inner(x: u64) -> (r: u64) {
            x
        }

        #[verifier::external_body]
        fn shrink_if_big(x: u64) -> (r: u64)
            allocates 0int deallocates deallocates_when(1int, x > 5)
        {
            x
        }

        #[verifier::external_body]
        fn outer(x: u64) -> (r: u64)
            allocates inner.allocations(x) deallocates deallocates_when(inner.deallocations(x), inner.deallocates(x))
        {
            inner(x)
        }

        #[verifier::external_body]
        fn outer2(x: u64) -> (r: u64)
            allocates shrink_if_big.allocations(x) deallocates deallocates_when(shrink_if_big.deallocations(x), shrink_if_big.deallocates(x))
        {
            shrink_if_big(x)
        }

        #[verifier::fip]
        fn use_outer(x: u64) -> (r: u64) {
            outer(x)
        }

        #[verifier::fip]
        fn use_outer2_small() -> (r: u64) {
            outer2(3)
        }

        // the builtins themselves, as the sugar rewrites to
        proof fn facts(x: u64) {
            assert(call_deallocates(inner, (x,)) == false);
            assert(call_allocations(inner, (x,)) == 0);
            assert(shrink_if_big.deallocates(x) == (x > 5));
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fip_call_deallocates_forwarding_condition_holds ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        #[verifier::external_body]
        fn shrink_if_big(x: u64) -> (r: u64)
            allocates 0int deallocates deallocates_when(1int, x > 5)
        {
            x
        }

        #[verifier::external_body]
        fn outer2(x: u64) -> (r: u64)
            allocates shrink_if_big.allocations(x) deallocates deallocates_when(shrink_if_big.deallocations(x), shrink_if_big.deallocates(x))
        {
            shrink_if_big(x)
        }

        #[verifier::fip]
        fn use_outer2_big() -> (r: u64) {
            outer2(10)
        }
    } => Err(err) => assert_vir_error_msg(err, "the `deallocates_when` condition of")
}

test_verify_one_file_with_options! {
    // a trait declaration's condition is an upper bound for every implementation
    #[test] fip_call_deallocates_trait_decl ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        pub trait Pool {
            fn peek(&self, n: u64) -> (r: u64)
                allocates 0int deallocates deallocates_when(1int, n > 10);
        }

        proof fn decl_bound<T: Pool>(t: &T, n: u64)
            requires n <= 10,
        {
            assert(!call_deallocates(T::peek, (t, n)));
            assert(!T::peek.deallocates(t, n));
        }
    } => Ok(())
}

// `#[verifier::fip]` closures: their bodies are checked as fip, `call_deallocates` of them is
// `false`, and a fip function may call a function value whose `deallocates` it shows false
test_verify_one_file_with_options! {
    #[test] fip_closures ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        #[verifier::fip]
        fn apply<F: Fn(u64) -> u64>(f: &F, x: u64) -> (r: u64)
            requires
                f.requires((x,)),
                !(*f).deallocates(x),
            allocates
                (*f).allocations(x),
        {
            f(x)
        }

        #[verifier::fip]
        fn compose<F: Fn(u64) -> u64, G: Fn(u64) -> u64>(f: &F, g: &G, x: u64) -> (r: u64)
            requires
                f.requires((x,)),
                forall|y: u64| g.requires((y,)),
                !(*f).deallocates(x),
                forall|y: u64| !(*g).deallocates(y),
                forall|y: u64| (*g).allocations(y) == 0,
            allocates
                (*f).allocations(x),
        {
            let y = f(x);
            g(y)
        }

        #[verifier::fip]
        fn use_them() -> (r: u64) {
            let half = #[verifier::fip] |y: u64| -> (r: u64) { y / 2 };
            let inc = #[verifier::fip] |y: u64| -> (r: u64) { y.wrapping_add(1) };
            let a = apply(&half, 7);
            let b = compose(&half, &inc, 8);
            let c = half(4);
            a.wrapping_add(b).wrapping_add(c)
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fip_closure_not_fip_call_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        #[verifier::fip]
        fn use_it() -> (r: u64) {
            let half = |y: u64| -> (r: u64) allocates 0 { y / 2 };
            half(4)
        }
    } => Err(err) => assert_vir_error_msg(err, "the `deallocates_when` condition of")
}

test_verify_one_file_with_options! {
    #[test] fip_closure_body_checked ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        fn make() -> (r: u64) {
            let f = #[verifier::fip] |b: Box<u64>| -> (r: u64) { *b };
            f(Box::new(3))
        }
    } => Err(err) => assert_vir_error_msg(err, "is dropped here")
}

test_verify_one_file_with_options! {
    // a strict function may call a strict closure it knows (a generic one's stack is not known)
    #[test] fip_strict_closure_call ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        #[verifier::fip(strict)]
        fn use_it() -> (r: u64) {
            let half = #[verifier::fip(strict)] |y: u64| -> (r: u64) { y / 2 };
            half(4)
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fip_strict_closure_not_strict_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        #[verifier::fip(strict)]
        fn use_it() -> (r: u64) {
            let half = #[verifier::fip] |y: u64| -> (r: u64) { y / 2 };
            half(4)
        }
    } => Err(err) => assert_vir_error_msg(err, "is not `#[verifier::fip(strict)]`")
}

test_verify_one_file_with_options! {
    #[test] fip_closure_strict_mode_rejected ["vstd", "-V alloc-check-strict"] => verus_code! {
        use vstd::prelude::*;

        fn f() -> (r: u64)
            no_unwind
            allocates 0
        {
            let half = #[verifier::fip] |y: u64| -> (r: u64) { y / 2 };
            half(4)
        }
    } => Err(err) => assert_vir_error_msg(err, "a `#[verifier::fip]` closure must be `no_unwind`")
}

test_verify_one_file_with_options! {
    #[test] fip_closure_strict_mode_no_unwind ["vstd", "-V alloc-check-strict"] => verus_code! {
        use vstd::prelude::*;

        fn f() -> (r: u64)
            no_unwind
            allocates 0
        {
            let half = #[verifier::fip] |y: u64| -> (r: u64) no_unwind { y / 2 };
            half(4)
        }
    } => Ok(())
}

// `encapsulates alloc(a, d)`: a function that encapsulates an allocator of its own API (a pool,
// a slab): each call counts as `a` allocations and may deallocate where `d > 0`; its body is the
// runtime's
test_verify_one_file_with_options! {
    #[test] encapsulates_alloc_calls ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        pub struct Pool { pub n: u64 }

        impl Pool {
            fn alloc(&mut self) -> (r: u64) encapsulates alloc(1, 0) {
                self.n = self.n.wrapping_add(1);
                self.n
            }
            fn free(&mut self, x: u64) encapsulates alloc(0, 1) { }
            // (the body is the runtime's: what it allocates is not counted)
            fn refill(&mut self) encapsulates alloc(0, 0) { let _b = Box::new(3u8); }
            fn grow(&mut self) encapsulates alloc(1, 1) { }
            fn two(&mut self) encapsulates alloc(2, 0) { }
            fn cond(&mut self, k: u64) encapsulates alloc(0, if k > 10 { 1 } else { 0 }) { }
        }

        fn many(p: &mut Pool) -> (r: u64) allocates 2 { p.alloc(); p.alloc() }
        fn with_two(p: &mut Pool) allocates 3 { p.two(); p.grow(); }
        #[verifier::fip] fn fip_alloc(p: &mut Pool) -> (r: u64) allocates 1 { p.alloc() }
        #[verifier::fip] fn fip_cond(p: &mut Pool) { p.cond(3) }
        #[verifier::fip] fn fip_refill(p: &mut Pool) { p.refill() }
        #[verifier::fip(strict)] fn strict_alloc(p: &mut Pool) -> (r: u64) allocates 1 { p.alloc() }

        proof fn t() {
            assert(forall|p: &mut Pool| #[trigger] Pool::two.allocations(p) == 2);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] encapsulates_alloc_calls_fail ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        pub struct Pool { pub n: u64 }

        impl Pool {
            fn alloc(&mut self) -> (r: u64) encapsulates alloc(1, 0) { self.n }
            fn free(&mut self, x: u64) encapsulates alloc(0, 1) { }
            fn grow(&mut self) encapsulates alloc(1, 1) { }
            fn cond(&mut self, k: u64) encapsulates alloc(0, if k > 10 { 1 } else { 0 }) { }
        }

        fn too_many(p: &mut Pool) allocates 1 { p.alloc(); p.alloc(); } // FAILS
        #[verifier::fip] fn fip_free(p: &mut Pool) { p.free(3) } // FAILS
        #[verifier::fip] fn fip_grow(p: &mut Pool) allocates 1 { p.grow() } // FAILS
        #[verifier::fip] fn fip_cond_bad(p: &mut Pool) { p.cond(30) } // FAILS

        fn after() {}
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file_with_options! {
    #[test] encapsulates_alloc_assume_specification ["vstd", "-V alloc-check"] => code! {
        use vstd::prelude::*;
        pub fn ext_alloc() -> u64 { 0 }
        pub fn ext_free(x: u64) { }
        verus! {
            pub assume_specification[ ext_alloc ]() -> u64 encapsulates alloc(1, 0);
            pub assume_specification[ ext_free ](x: u64) encapsulates alloc(0, 1);
            fn g() allocates 2 { ext_alloc(); ext_alloc(); }
            #[verifier::fip] fn h() allocates 1 { ext_alloc(); }
            #[verifier::fip] fn bad() { ext_free(1); } // FAILS
        }
    } => Err(err) => assert_vir_error_msg(err, "the `deallocates_when` condition of")
}

test_verify_one_file_with_options! {
    #[test] encapsulates_alloc_counts_are_nat ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        fn f(x: i64) encapsulates alloc(x, 0) { }
    } => Err(err) => assert_rust_error_msg(err, "mismatched types")
}

test_verify_one_file_with_options! {
    #[test] encapsulates_alloc_not_with_allocates ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        fn f() allocates 1 encapsulates alloc(1, 0) { }
    } => Err(err) => assert_vir_error_msg(err, "cannot also have `allocates`")
}

test_verify_one_file_with_options! {
    #[test] encapsulates_alloc_not_fip ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::fip] fn f() encapsulates alloc(1, 0) { }
    } => Err(err) => assert_vir_error_msg(err, "cannot be `#[verifier::fip]`")
}

test_verify_one_file_with_options! {
    #[test] encapsulates_alloc_form ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        fn f() encapsulates foo(1, 0) { }
    } => Err(err) => assert_vir_error_msg(err, "encapsulates takes `alloc(a, d)`")
}

test_verify_one_file_with_options! {
    #[test] encapsulates_alloc_not_on_trait_decl ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        trait T { fn m(&self) encapsulates alloc(1, 0); }
    } => Err(err) => assert_vir_error_msg(err, "cannot be used on a trait method declaration")
}

test_verify_one_file_with_options! {
    #[test] encapsulates_alloc_impls ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        trait T {
            fn m(&self) allocates 1;
            fn n(&self, k: u64) allocates 0int deallocates deallocates_when(1int, k > 5);
        }
        struct S;
        impl T for S {
            fn m(&self) encapsulates alloc(1, 0) { }
            fn n(&self, k: u64) encapsulates alloc(0, if k > 7 { 1 } else { 0 }) { }
        }
        fn g<X: T>(x: &X) allocates 1 { x.m() }
        #[verifier::fip] fn h<X: T>(x: &X) { x.n(3) }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] encapsulates_alloc_impl_exceeds_bound ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        trait T { fn m(&self) allocates 1; }
        struct S;
        impl T for S { fn m(&self) encapsulates alloc(2, 0) { } }
    } => Err(err) => assert_vir_error_msg(err, "may count more allocations than the trait method's")
}

test_verify_one_file_with_options! {
    #[test] encapsulates_alloc_impl_exceeds_condition ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        trait T { fn n(&self, k: u64) allocates 0int deallocates deallocates_when(1int, k > 5); }
        struct S;
        impl T for S { fn n(&self, k: u64) encapsulates alloc(0, if k > 2 { 1 } else { 0 }) { } }
    // (the declaration's bound is 0 where `k <= 5`, so the count check reports it as well)
    } => Err(err) => assert_vir_error_msgs(err, &[
        "may deallocate where the trait method may not",
        "may count more deallocations than the trait method's",
    ])
}

// across crates: the clause is in the `.vir`, and a strict function may call such a function as a
// leaf
#[test]
fn encapsulates_alloc_across_crates() {
    let tempdir = tempfile::TempDir::new().expect("temp dir");
    let dir = tempdir.path();
    let pre = format!("{}\nuse vstd::prelude::*;\n", FEATURE_PRELUDE);
    std::fs::write(
        dir.join("pool.rs"),
        format!(
            "{pre}verus!{{ pub struct Pool {{ pub n: u64 }} impl Pool {{ pub fn alloc(&mut self) -> (r: u64) encapsulates alloc(1, 0) {{ let _b = Box::new(1u8); self.n }} }} }}\n"
        ),
    )
    .expect("write");
    let pool = run_verus_raw(
        &[
            "--crate-type=lib",
            "--crate-name",
            "pool",
            "-V",
            "alloc-check",
            "--export",
            "pool.vir",
            "--compile",
            "pool.rs",
            "-o",
            "libpool.rlib",
        ],
        dir,
    );
    assert!(pool.status.success(), "pool failed:\n{}", String::from_utf8_lossy(&pool.stderr));
    let user = |name: &str, code: &str| {
        std::fs::write(dir.join(name), format!("{pre}verus!{{ {code} }}\n")).expect("write");
        run_verus_raw(
            &[
                "--crate-type=lib",
                name,
                "-V",
                "alloc-check",
                "--import",
                "pool=pool.vir",
                "--extern",
                "pool=libpool.rlib",
            ],
            dir,
        )
    };
    let pos = user(
        "pos.rs",
        "#[verifier::fip(strict)] fn s(p: &mut pool::Pool) -> (r: u64) allocates 1 { p.alloc() }",
    );
    assert!(pos.status.success(), "pos failed:\n{}", String::from_utf8_lossy(&pos.stderr));
    let neg = user("neg.rs", "fn s(p: &mut pool::Pool) allocates 1 { p.alloc(); p.alloc(); }");
    let stderr = String::from_utf8_lossy(&neg.stderr);
    assert!(!neg.status.success(), "neg should be rejected:\n{}", stderr);
    assert!(stderr.contains("postcondition not satisfied"), "unexpected:\n{}", stderr);
}

// `fip_mir` learns which functions encapsulate an allocator from VIR (the clause in their
// specification), not from an attribute the program could write: a hand-written internal
// attribute used to make a recursive function a leaf for a strict caller (portable-fip,
// 2026-11-19)
test_verify_one_file_with_options! {
    #[test] encapsulates_alloc_internal_attr_not_trusted ["vstd", "-V alloc-check", "--no-cheating"] => verus_code! {
        use vstd::prelude::*;

        #[verifier::fip]
        #[verus::internal(encapsulates_alloc)]
        pub fn deep(n: u64) -> (r: u64) decreases n { if n == 0 { 0 } else { deep(n - 1) } }

        #[verifier::fip(strict)]
        pub fn s(n: u64) -> (r: u64) { deep(n) }
    } => Err(err) => assert_any_vir_error_msg(err, "unrecognized internal attribute")
}

test_verify_one_file_with_options! {
    #[test] encapsulates_alloc_strict_leaf_recursive_body ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        pub struct Pool { pub n: u64 }

        impl Pool {
            // (the body is the runtime's: its recursion is not the strict caller's)
            pub fn refill(&mut self, k: u64) decreases k encapsulates alloc(0, 0) {
                if k > 0 { self.refill(k - 1) }
            }
        }

        #[verifier::fip(strict)]
        pub fn s(p: &mut Pool) { p.refill(3) }
    } => Ok(())
}

// `fip_mir` runs on the compile that erases ghost code, whose `DefId`s differ from the verified
// one's (ghost items are gone): the functions VIR names are looked up by path there, without the
// `DefId` cache of the verified compile, or a function next to an `encapsulates` one could be
// taken for it
test_verify_one_file_with_options! {
    #[test] encapsulates_alloc_lookup_after_ghost_items ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        pub open spec fn s1(x: u64) -> u64 { x }
        pub open spec fn s2(x: u64) -> u64 { x }
        pub proof fn p1() { }
        pub proof fn p2() { }

        #[verifier::fip]
        pub fn deep(n: u64) -> (r: u64) decreases n { if n == 0 { 0 } else { deep(n - 1) } }
        pub fn enc() encapsulates alloc(0, 0) { }
        #[verifier::fip]
        pub fn deep2(n: u64) -> (r: u64) decreases n { if n == 0 { 0 } else { deep2(n - 1) } }

        #[verifier::fip(strict)]
        pub fn s(n: u64) -> (r: u64) { enc(); deep(n) }
    } => Err(err) => assert_vir_error_msg(err, "which is not `#[verifier::fip(strict)]`")
}
