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
