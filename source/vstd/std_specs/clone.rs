use super::super::prelude::*;
use core::clone::Clone;

verus! {

#[verifier::external_trait_specification]
pub trait ExClone: Sized {
    type ExternalTraitSpecificationFor: core::clone::Clone;

    fn clone(&self) -> Self;
}

#[verifier::external_trait_specification]
pub trait ExCopy: Clone {
    type ExternalTraitSpecificationFor: core::marker::Copy;
}

/*
#[verifier::external_fn_specification]
pub fn ex_clone_clone_from<T: Clone>(a: &mut T, b: &T)
{
    a.clone_from(b)
}
*/

/// Sum of the `allocates` bounds of cloning the first `n` elements (for `-V alloc-check`)
pub open spec fn seq_clone_allocates<T: Clone>(s: Seq<T>, n: nat) -> int
    decreases n,
{
    if n == 0 {
        0
    } else {
        seq_clone_allocates(s, (n - 1) as nat) + call_allocations(T::clone, (&s[n - 1],))
    }
}

/// Cloning elements that each allocate nothing allocates nothing in total
pub broadcast proof fn lemma_seq_clone_allocates_zero<T: Clone>(s: Seq<T>, n: nat)
    ensures
        (forall|i: int| 0 <= i < n ==> #[trigger] call_allocations(T::clone, (&s[i],)) == 0)
            ==> #[trigger] seq_clone_allocates(s, n) == 0,
    decreases n,
{
    if n > 0 {
        lemma_seq_clone_allocates_zero(s, (n - 1) as nat);
    }
}

/// Sum of the `deallocates` bounds of cloning the first `n` elements (for `-V alloc-check`)
pub open spec fn seq_clone_deallocations<T: Clone>(s: Seq<T>, n: nat) -> int
    decreases n,
{
    if n == 0 {
        0
    } else {
        seq_clone_deallocations(s, (n - 1) as nat) + call_deallocations(T::clone, (&s[n - 1],))
    }
}

/// Cloning elements that each deallocate nothing deallocates nothing in total
pub broadcast proof fn lemma_seq_clone_deallocations_zero<T: Clone>(s: Seq<T>, n: nat)
    ensures
        (forall|i: int| 0 <= i < n ==> #[trigger] call_deallocations(T::clone, (&s[i],)) == 0)
            ==> #[trigger] seq_clone_deallocations(s, n) == 0,
    decreases n,
{
    if n > 0 {
        lemma_seq_clone_deallocations_zero(s, (n - 1) as nat);
    }
}

pub assume_specification[ <bool as Clone>::clone ](b: &bool) -> (res: bool)
    returns
        b,
    allocates
        0int,
    deallocates
        0,
;

pub assume_specification[ <char as Clone>::clone ](c: &char) -> (res: char)
    returns
        c,
    allocates
        0int,
    deallocates
        0,
;

#[allow(suspicious_double_ref_op)]
pub assume_specification<'b, T: core::marker::PointeeSized, 'a>[ <&'b T as Clone>::clone ](
    b: &'a &'b T,
) -> (res: &'b T)
    ensures
        res == b,
    allocates
        0int,
    deallocates
        0,
;

pub assume_specification<T: Clone, const N: usize>[ <[T; N] as Clone>::clone ](a: &[T; N]) -> (res:
    [T; N])
    ensures
        forall|i| #![all_triggers] 0 <= i < N ==> cloned::<T>(a@[i], res@[i]),
        a@ =~= res@ ==> a@ == res@,
    allocates
        seq_clone_allocates(a@, N as nat),
    deallocates
        deallocates_when(
            seq_clone_deallocations(a@, N as nat),
            !super::super::alloc_check::clone_is_fip::<T>(),
        ),
;

/*
#[verifier::external_fn_specification]
pub fn ex_bool_clone_from(dest: &mut bool, source: &bool)
    ensures *dest == source,
{
    dest.clone_from(source)
}
*/

// Cloning a Tracked copies the underlying ghost T
pub assume_specification<T: Copy>[ <Tracked<T> as Clone>::clone ](b: &Tracked<T>) -> (res: Tracked<
    T,
>)
    ensures
        res == b,
    allocates
        0,
    deallocates
        0,
;

pub assume_specification<T>[ <Ghost<T> as Clone>::clone ](b: &Ghost<T>) -> (res: Ghost<T>)
    ensures
        res == b,
    allocates
        0,
    deallocates
        0,
;

} // verus!
