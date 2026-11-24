#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// The compiled program must give exec code the types that Verus verified (see
// rust_verify/src/exec_types.rs): Verus verifies the code with its ghost code and compiles it with
// the ghost code erased, so ghost code must not be the only thing that fixes an exec type.

const TYPE_DIFFERS: &str = "in the compiled program, but";

test_verify_one_file_with_options! {
    #[test] literal_typed_by_proof_block_selects_impl ["vstd"] => verus_code! {
        pub trait Mk { fn mk(self) -> (r: Option<u8>); }
        impl Mk for u64 { fn mk(self) -> (r: Option<u8>) ensures r.is_none() { None } }
        impl Mk for i32 { fn mk(self) -> (r: Option<u8>) { Some(1u8) } }

        pub fn f() -> (r: Option<u8>)
            ensures r.is_none(),
        {
            let n = 1;
            proof { let g: u64 = n; }
            n.mk()
        }
    } => Err(err) => assert_vir_error_msg(err, "has type `i32` in the compiled program, but `u64` in the verified program")
}

test_verify_one_file_with_options! {
    #[test] literal_typed_in_exec_code ["vstd"] => verus_code! {
        pub trait Mk { fn mk(self) -> (r: Option<u8>); }
        impl Mk for u64 { fn mk(self) -> (r: Option<u8>) ensures r.is_none() { None } }
        impl Mk for i32 { fn mk(self) -> (r: Option<u8>) { Some(1u8) } }

        pub fn f() -> (r: Option<u8>)
            ensures r.is_none(),
        {
            let n: u64 = 1;
            proof { let g: u64 = n; }
            n.mk()
        }

        pub fn g() -> (r: Option<u8>)
            ensures r.is_none(),
        {
            let n = 1;
            proof { let g: u64 = n; }
            let m: u64 = n;
            m.mk()
        }

        pub fn h() -> (r: Option<u8>)
            ensures r.is_none(),
        {
            1u64.mk()
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] literal_typed_by_let_ghost ["vstd"] => verus_code! {
        fn f() -> (r: u64) ensures r == 4_000_000_000 {
            let a = 2_000_000_000;
            let ghost g: u64 = a;
            (a + a) as u64
        }
    } => Err(err) => assert_vir_error_msg(err, TYPE_DIFFERS)
}

test_verify_one_file_with_options! {
    #[test] literal_typed_by_ghost_argument ["vstd"] => verus_code! {
        fn take_ghost(Ghost(x): Ghost<u64>) {}
        fn f() -> (r: u64) ensures r == 4_000_000_000 {
            let a = 2_000_000_000;
            take_ghost(Ghost(a));
            (a + a) as u64
        }
    } => Err(err) => assert_vir_error_msg(err, TYPE_DIFFERS)
}

test_verify_one_file_with_options! {
    #[test] loop_counter_typed_by_invariant ["vstd"] => verus_code! {
        spec fn ok(x: u64) -> bool { x <= 2_000_000_000 && x % 1_000_000_000 == 0 }
        fn f() -> (r: u64) ensures r == 4_000_000_000 {
            let mut i = 0;
            while i < 2_000_000_000
                invariant ok(i),
                decreases 2_000_000_000 - i,
            {
                i = i + 1_000_000_000;
            }
            (i + i) as u64
        }
    } => Err(err) => assert_vir_error_msg(err, TYPE_DIFFERS)
}

test_verify_one_file_with_options! {
    #[test] float_literal_typed_by_ghost ["vstd"] => verus_code! {
        pub trait Width { spec fn w() -> u64; fn width(&self) -> (r: u64) ensures r == Self::w(); }
        impl Width for f32 { open spec fn w() -> u64 { 32 } fn width(&self) -> (r: u64) { 32 } }
        impl Width for f64 { open spec fn w() -> u64 { 64 } fn width(&self) -> (r: u64) { 64 } }
        fn f() -> (r: u64) ensures r == 32 {
            let a = 0.5;
            let ghost g: f32 = a;
            a.width()
        }
    } => Err(err) => assert_vir_error_msg(err, "has type `f64` in the compiled program, but `f32` in the verified program")
}

test_verify_one_file_with_options! {
    #[test] never_type_fallback_typed_by_ghost ["vstd"] => verus_code! {
        use vstd::layout::*;
        broadcast use layout_of_primitives;
        fn sz<T>(_o: Option<T>) -> (r: usize) ensures r == size_of::<T>() {
            core::mem::size_of::<T>()
        }
        fn f(b: bool) -> (r: usize) ensures r == 8 {
            let o = if b { None } else { let x = return 8; Some(x) };
            proof { let g: Option<u64> = o; }
            sz(o)
        }
    } => Err(err) => assert_vir_error_msg(err, TYPE_DIFFERS)
}

test_verify_one_file_with_options! {
    #[test] literal_typed_by_ghost_in_exec_const ["vstd"] => verus_code! {
        exec const C: u32
            ensures C == 0
        {
            let a = 255;
            proof {
                let b: u8 = a;
                assert(!b == 0) by (bit_vector) requires b == 255u8;
            }
            (!a) as u32
        }
    } => Err(err) => assert_vir_error_msg(err, TYPE_DIFFERS)
}

test_verify_one_file_with_options! {
    #[test] literal_typed_by_ghost_in_verus_spec_with ["vstd"] => code! {
        use vstd::prelude::*;
        #[verus_verify]
        pub trait Mk: Sized {
            fn mk(self) -> Option<u8>;
        }
        #[verus_verify]
        impl Mk for u64 {
            #[verus_spec(r => ensures r.is_none())]
            fn mk(self) -> Option<u8> { None }
        }
        #[verus_verify]
        impl Mk for i32 {
            fn mk(self) -> Option<u8> { Some(1u8) }
        }

        #[verus_spec(r =>
            with Ghost(k): Ghost<u64>
            ensures r.is_none()
        )]
        pub fn f() -> Option<u8> {
            let n = 1;
            proof!{ let g: u64 = n; }
            n.mk()
        }
    } => Err(err) => assert_vir_error_msg(err, TYPE_DIFFERS)
}

test_verify_one_file_with_options! {
    #[test] literal_typed_by_proof_macro_attribute_syntax ["vstd"] => code! {
        use vstd::prelude::*;

        #[verus_verify]
        pub trait Mk: Sized {
            fn mk(self) -> Option<u8>;
        }
        #[verus_verify]
        impl Mk for u64 {
            #[verus_spec(r => ensures r.is_none())]
            fn mk(self) -> Option<u8> { None }
        }
        #[verus_verify]
        impl Mk for i32 {
            fn mk(self) -> Option<u8> { Some(1u8) }
        }

        #[verus_spec(r => ensures r.is_none())]
        pub fn f() -> Option<u8> {
            let n = 1;
            proof! { let g: u64 = n; }
            n.mk()
        }
    } => Err(err) => assert_vir_error_msg(err, TYPE_DIFFERS)
}

test_verify_one_file_with_options! {
    #[test] closure_return_typed_by_verus_spec ["vstd"] => code! {
        use vstd::prelude::*;
        #[verus_spec(r => ensures r == 0)]
        fn f() -> u64 {
            let c = #[verus_spec(r: u8 => ensures r == 255u8)]
            || 255;
            let v = c();
            proof!{ assert(!v == 0) by (bit_vector) requires v == 255u8; }
            (!v) as u64
        }
    } => Err(err) => assert_vir_error_msg(err, TYPE_DIFFERS)
}

test_verify_one_file_with_options! {
    #[test] ghost_code_with_exec_types_unchanged ["vstd"] => verus_code! {
        // ghost code, and code that Verus's macros generate differently for the two runs, with
        // exec types that exec code fixes
        fn take(Ghost(x): Ghost<u64>, Tracked(t): Tracked<&u64>) {}

        fn sum(n: u64, v: &Vec<u8>) -> (r: u64)
            requires n < 10,
        {
            let mut s: u64 = 0;
            for i in 0..n
                invariant s <= 10 * i, n < 10,
            {
                s = s + 10;
                proof { let g: int = i as int; }
            }
            let mut m: u64 = 0;
            for x in it: v.iter()
                invariant m <= 255,
            {
                m = *x as u64;
            }
            let mut k = 0;
            while k < 3
                invariant k <= 3,
                decreases 3 - k,
            {
                k += 1;
            }
            let y = 2;
            let s2 = s;
            take(Ghost(s), Tracked(&s2));
            let c = |a: u64| -> (b: u64) ensures b == a { a };
            c(s) + y + k + m
        }

        fn opt(a: Option<u64>) -> Option<u64> {
            let b = a?;
            let ghost g = b + 1;
            Some(b)
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] verus_spec_with_calls_unchanged ["vstd"] => code! {
        use vstd::prelude::*;
        #[verus_spec(ret =>
            with Ghost(w): Ghost<u32>
            requires x < 100,
            ensures ret == x,
        )]
        fn id(x: u32) -> u32 {
            x
        }

        #[verus_spec]
        fn call() -> u32 {
            let a = 7;
            let r = {
                proof_with!{Ghost(0)}
                id(a)
            };
            r
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] literal_typed_by_ghost_in_macro_rules ["vstd"] => code! {
        use vstd::prelude::*;
        verus! {
        pub trait Mk { fn mk(self) -> (r: Option<u8>); }
        impl Mk for u64 { fn mk(self) -> (r: Option<u8>) ensures r.is_none() { None } }
        impl Mk for i32 { fn mk(self) -> (r: Option<u8>) { Some(1u8) } }
        }
        // (the function's tokens are all in the macro's definition)
        macro_rules! def_f {
            () => {
                verus! {
                pub fn f() -> (r: Option<u8>)
                    ensures r.is_none(),
                {
                    let n = 1;
                    proof { let g: u64 = n; }
                    n.mk()
                }
                }
            };
        }
        def_f!();
    } => Err(err) => assert_vir_error_msg(err, TYPE_DIFFERS)
}

test_verify_one_file_with_options! {
    #[test] literal_typed_by_ghost_in_enum_discriminant ["vstd"] => verus_code! {
        #[repr(u16)]
        pub enum E {
            A = {
                let a = 255;
                proof { let b: u8 = a; }
                let c = (!a) as u16;
                c
            },
        }
        pub fn disc() -> (r: u16)
            ensures r == 0,
        {
            E::A as u16
        }
    } => Err(err) => assert_vir_error_msg(err, TYPE_DIFFERS)
}

test_verify_one_file_with_options! {
    #[test] type_argument_fixed_by_ghost_argument ["vstd"] => verus_code! {
        use vstd::layout::*;
        broadcast use layout_of_primitives;
        fn sz<T>(Ghost(_g): Ghost<T>) -> (r: usize)
            ensures r == size_of::<T>(),
        {
            core::mem::size_of::<T>()
        }
        fn f() -> (r: usize)
            ensures r == 8,
        {
            sz(Ghost(0u64))
        }
    } => Err(err) => assert_vir_error_msg(err, "has type `fn sz::<!>` in the compiled program, but `fn sz::<u64>` in the verified program")
}

test_verify_one_file_with_options! {
    #[test] same_tokens_twice_in_one_body ["vstd"] => code! {
        use vstd::prelude::*;
        verus! {
        pub trait Width { spec fn w() -> u64; fn width(&self) -> (r: u64) ensures r == Self::w(); }
        impl Width for u64 { open spec fn w() -> u64 { 64 } fn width(&self) -> (r: u64) { 64 } }
        impl Width for i32 { open spec fn w() -> u64 { 32 } fn width(&self) -> (r: u64) { 32 } }
        pub open spec fn tie<T>(a: T, b: T) -> bool { true }
        }
        // (the user's tokens twice in one body, with `n` of another type in each copy)
        macro_rules! probe_both {
            ($g:ident => { $($body:tt)* }) => {
                verus! {
                pub fn probe() -> (r: u64)
                    ensures r == 64,
                {
                    let _other = { let $g: i32 = 0; $($body)* };
                    let a = { let $g: u64 = 0; $($body)* };
                    a
                }
                }
            };
        }
        probe_both!(g => {
            let n = 1;
            proof { assert(tie(n, g)); }
            n.width()
        });
    } => Err(err) => assert_vir_error_msg(err, TYPE_DIFFERS)
}

test_verify_one_file_with_options! {
    #[test] exec_types_unchanged_around_closures_and_ghost_type_arguments ["vstd"] => verus_code! {
        use vstd::seq::*;
        fn take(g: Ghost<u64>) {}
        fn note<A>(Ghost(a): Ghost<A>) {}

        // (an item nested in a closure, after a closure that only the compiled program has)
        fn f() -> u64 {
            take(Ghost(0u64));
            let c = || { struct P(u64); P(1) };
            let p = c();
            p.0
        }

        // (an item nested in a closure, after a closure that only the verified program has)
        fn g() -> (r: u64)
            ensures r == 1,
        {
            let c = || -> (q: u64)
                ensures q == 1,
            {
                struct P(u64);
                let p = P(1);
                p.0
            };
            c()
        }

        // (a type argument that only a ghost argument fixes, given in the exec code)
        fn h() {
            let ghost s: Seq<u8> = Seq::empty();
            note::<Seq<u8>>(Ghost(s));
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] type_argument_only_ghost_argument_fixes ["vstd"] => verus_code! {
        use vstd::seq::*;
        fn note<A>(Ghost(a): Ghost<A>) {}
        fn h() {
            let ghost s: Seq<u8> = Seq::empty();
            note(Ghost(s));
        }
    } => Err(err) => assert_vir_error_msg(err, "`f::<u64>(..)`")
}
