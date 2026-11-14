use super::super::laws_cmp::obeys_cmp;
use super::super::prelude::*;
use super::super::view::View;
use super::cmp::{PartialOrdIs, PartialOrdSpec};
use super::iter::{IteratorSpec, StepSpec, StepSpecImpl};
use core::ops::{
    Bound, Range, RangeBounds, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive,
};

use super::iter::{iter_next_back_cost, iter_next_cost};
verus! {

#[verifier::external_type_specification]
#[verifier::reject_recursive_types_in_ground_variants(Idx)]
pub struct ExRange<Idx>(Range<Idx>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types_in_ground_variants(Idx)]
pub struct ExRangeInclusive<Idx>(RangeInclusive<Idx>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExIpv4Addr(core::net::Ipv4Addr);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExIpv6Addr(core::net::Ipv6Addr);

pub struct RangeInclusiveView<Idx> {
    pub start: Idx,
    pub end: Idx,
    /// Whether iteration has marked the range as finished.
    pub exhausted: bool,
}

pub open spec fn spec_range_inclusive_is_empty<Idx>(r: &RangeInclusive<Idx>) -> bool {
    r@.exhausted || spec_range_inclusive_out_of_order(r)
}

/// Uninterpreted because `RangeBounds` methods have no
/// `PartialOrd` bound. Defined by [`axiom_range_inclusive_out_of_order`].
pub uninterp spec fn spec_range_inclusive_out_of_order<Idx>(r: &RangeInclusive<Idx>) -> bool;

pub broadcast axiom fn axiom_range_inclusive_out_of_order<Idx: PartialOrd<Idx>>(
    r: &RangeInclusive<Idx>,
)
    ensures
        Idx::obeys_partial_cmp_spec() ==> (#[trigger] spec_range_inclusive_out_of_order(r)
            <==> !r@.start.is_le(&r@.end)),
;

// Results std leaves unspecified for empty ranges.
pub uninterp spec fn spec_range_inclusive_unspecified_contains<Idx, U: ?Sized>(
    r: &RangeInclusive<Idx>,
    item: &U,
) -> bool;

pub uninterp spec fn spec_range_inclusive_unspecified_bounds<T>(r: &RangeInclusive<T>) -> (
    Bound<&T>,
    Bound<&T>,
);

pub uninterp spec fn spec_range_inclusive_unspecified_ref_bounds<'a, T>(
    r: &RangeInclusive<&'a T>,
) -> (Bound<&'a T>, Bound<&'a T>);

pub trait ContainsSpec<Idx, U> where Idx: PartialOrd<U>, U: ?Sized + PartialOrd<Idx> {
    spec fn obeys_contains() -> bool;

    spec fn contains_spec(&self, i: &U) -> bool;
}

impl<Idx, U> ContainsSpec<Idx, U> for RangeInclusive<Idx> where
    Idx: PartialOrd<U>,
    U: ?Sized + PartialOrd<Idx>,
 {
    open spec fn obeys_contains() -> bool {
        (U::obeys_partial_cmp_spec() && <Idx as PartialOrdSpec<U>>::obeys_partial_cmp_spec())
    }

    open spec fn contains_spec(&self, i: &U) -> bool {
        if spec_range_inclusive_is_empty(self) {
            spec_range_inclusive_unspecified_contains(self, i)
        } else {
            self@.start.is_le(&i) && i.is_le(&self@.end)
        }
    }
}

/// An empty range contains nothing when `Idx` is totally ordered.
pub broadcast axiom fn axiom_range_inclusive_empty_contains<Idx: Ord>(
    r: &RangeInclusive<Idx>,
    item: &Idx,
)
    requires
        obeys_cmp::<Idx>(),
        spec_range_inclusive_is_empty(r),
    ensures
        !#[trigger] r.contains_spec(item),
;

impl<Idx, U> ContainsSpec<Idx, U> for Range<Idx> where
    Idx: PartialOrd<U>,
    U: ?Sized + PartialOrd<Idx>,
 {
    open spec fn obeys_contains() -> bool {
        (U::obeys_partial_cmp_spec() && <Idx as PartialOrdSpec<U>>::obeys_partial_cmp_spec())
    }

    open spec fn contains_spec(&self, i: &U) -> bool {
        self.start.is_le(&i) && i.is_lt(&self.end)
    }
}

impl<Idx> View for RangeInclusive<Idx> {
    type V = RangeInclusiveView<Idx>;

    uninterp spec fn view(&self) -> Self::V;
}

pub uninterp spec fn spec_range_next<A>(a: Range<A>) -> (Range<A>, Option<A>);

/// Whether `A`'s executable stepping, comparison, and cloning obey the model
/// used by range iterators. The axioms below establish this for primitive
/// integers only; implementing `StepSpecImpl` alone does not establish it.
pub uninterp spec fn obeys_range_step_spec<A>() -> bool;

/// -V alloc-check: `A` is a std `Step` type (the primitive integers, `char`), whose `Step`,
/// `PartialOrd` and `Clone` methods allocate nothing
pub uninterp spec fn std_step_alloc_free<A>() -> bool;

/// Range::contains method is valid and safe to use only when cmp operations are implemented to satisfy
/// obeys_partial_cmp_spec. Specifically, the comparison must be deterministic, and `lt` (less than)
/// and `le` (less than or equal to) must define total orders.
/// If using Range::contains with types that do not satisfy obeys_partial_cmp_spec, no spec is provided.
#[verifier::alloc_check_skip_drops]
pub assume_specification<Idx: PartialOrd<Idx>, U>[ Range::<Idx>::contains ](
    r: &Range<Idx>,
    i: &U,
) -> (ret: bool) where Idx: PartialOrd<U>, U: ?Sized + PartialOrd<Idx>
    ensures
        <Range::<Idx> as ContainsSpec<Idx, U>>::obeys_contains() ==> ret == r.contains_spec(
            i,
        ),
// rustc 1.99.1 `RangeBounds::contains`: `start <= item && item < end`

    allocates
        deallocates_when(
            call_allocates(<Idx as PartialOrd<U>>::le, (&r.start, i)) + call_allocates(
                <U as PartialOrd<Idx>>::lt,
                (i, &r.end),
            ),
            !(crate::alloc_check::partial_ord_is_fip::<Idx, U>()
                && crate::alloc_check::partial_ord_is_fip::<U, Idx>()),
        ),
;

#[verifier::alloc_check_skip_drops]
pub assume_specification<Idx: PartialOrd<Idx>, U>[ RangeInclusive::<Idx>::contains ](
    r: &RangeInclusive<Idx>,
    i: &U,
) -> (ret: bool) where Idx: PartialOrd<U>, U: ?Sized + PartialOrd<Idx>
    ensures
        <RangeInclusive::<Idx> as ContainsSpec<Idx, U>>::obeys_contains() ==> ret
            == r.contains_spec(
            i,
        ),
// rustc 1.99.1 `RangeBounds::contains` with `RangeInclusive::end_bound`:
// `start <= item && (if exhausted { item < start } else { item <= end })`

    allocates
        deallocates_when(
            call_allocates(<Idx as PartialOrd<U>>::le, (&r@.start, i)) + if r@.exhausted {
                call_allocates(<U as PartialOrd<Idx>>::lt, (i, &r@.start))
            } else {
                call_allocates(<U as PartialOrd<Idx>>::le, (i, &r@.end))
            },
            !(crate::alloc_check::partial_ord_is_fip::<Idx, U>()
                && crate::alloc_check::partial_ord_is_fip::<U, Idx>()),
        ),
;

pub assume_specification<Idx: PartialOrd<Idx>>[ RangeInclusive::<Idx>::is_empty ](
    r: &RangeInclusive<Idx>,
) -> (res: bool) where Idx: PartialOrd<Idx>
    ensures
        <Idx as PartialOrdSpec<Idx>>::obeys_partial_cmp_spec() ==> res
            == spec_range_inclusive_is_empty(
            r,
        ),
// `self.exhausted || !(self.start <= self.end)`

    allocates
        call_allocates(<Idx as PartialOrd<Idx>>::le, (&r@.start, &r@.end)),
;

pub assume_specification<Idx>[ RangeInclusive::<Idx>::new ](start: Idx, end: Idx) -> (ret:
    core::ops::RangeInclusive<Idx>)
    ensures
        ret@ == (RangeInclusiveView { start, end, exhausted: false }),
    allocates
        0,
;

// `Range::next` runs `A`'s `PartialOrd::lt`, `Clone::clone` and `Step::forward_unchecked`;
// they allocate nothing for the std `Step` types (the primitive integers), which is what
// `obeys_range_step_spec` establishes (a user `Step` type, possible with `step_trait`, may
// allocate in them).
pub broadcast axiom fn axiom_next_cost_range<A: core::iter::Step>(i: &Range<A>)
    requires
        std_step_alloc_free::<A>(),
    ensures
        #[trigger] iter_next_cost(i) == 0,
;

/// std's other `Iterator` methods for this type (`nth`, `find`, `try_fold`, ...) allocate nothing
pub broadcast axiom fn axiom_aux_alloc_free_range<A: core::iter::Step>()
    requires
        std_step_alloc_free::<A>(),
    ensures
        #[trigger] super::iter::iter_aux_alloc_free::<Range<A>>(),
;

impl<A: core::iter::Step> super::iter::IteratorSpecImpl for Range<A> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        obeys_range_step_spec::<A>()
    }

    open spec fn remaining(&self) -> Seq<Self::Item> {
        let steps = self.start.spec_steps_between_int(self.end);
        let len = if steps > 0 {
            steps
        } else {
            0
        };
        Seq::new(len as nat, |i: int| self.start.spec_forward_checked_int(i).unwrap())
    }

    #[verifier::prophetic]
    open spec fn produces(&self) -> Seq<bool> {
        Seq::new(IteratorSpec::remaining(self).len(), |i: int| true)
    }

    open spec fn decrease(&self) -> Option<nat> {
        Some(self.start.spec_steps_between_int(self.end) as nat)
    }

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        //Some(self.start.spec_forward_checked_int(index).unwrap())
        if 0 <= index <= self.start.spec_steps_between_int(self.end) {
            Some(self.start.spec_forward_checked_int(index).unwrap())
        } else {
            None
        }
    }
}

/// Number of elements left in an inclusive range: zero once it is exhausted or if `start > end`.
pub open spec fn spec_range_inclusive_len<A: core::iter::Step>(r: &RangeInclusive<A>) -> nat {
    let steps = r@.start.spec_steps_between_int(r@.end);
    if steps >= 0 && !r@.exhausted {
        (steps + 1) as nat
    } else {
        0
    }
}

pub broadcast axiom fn axiom_next_cost_range_inclusive<A: core::iter::Step>(i: &RangeInclusive<A>)
    requires
        std_step_alloc_free::<A>(),
    ensures
        #[trigger] iter_next_cost(i) == 0,
;

/// std's other `Iterator` methods for this type (`nth`, `find`, `try_fold`, ...) allocate nothing
pub broadcast axiom fn axiom_aux_alloc_free_range_inclusive<A: core::iter::Step>()
    requires
        std_step_alloc_free::<A>(),
    ensures
        #[trigger] super::iter::iter_aux_alloc_free::<RangeInclusive<A>>(),
;

impl<A: core::iter::Step> super::iter::IteratorSpecImpl for RangeInclusive<A> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        obeys_range_step_spec::<A>()
    }

    open spec fn remaining(&self) -> Seq<Self::Item> {
        Seq::new(
            spec_range_inclusive_len(self),
            |i: int| self@.start.spec_forward_checked_int(i).unwrap(),
        )
    }

    #[verifier::prophetic]
    open spec fn produces(&self) -> Seq<bool> {
        Seq::new(IteratorSpec::remaining(self).len(), |i: int| true)
    }

    open spec fn decrease(&self) -> Option<nat> {
        Some(spec_range_inclusive_len(self))
    }

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        if 0 <= index <= spec_range_inclusive_len(self) {
            Some(self@.start.spec_forward_checked_int(index).unwrap())
        } else {
            None
        }
    }
}

pub assume_specification<A: core::iter::Step>[ <Range<A> as Iterator>::next ](
    range: &mut Range<A>,
) -> (r: Option<A>)
    ensures
        obeys_range_step_spec::<A>() ==> (*final(range), r) == spec_range_next(
            *old(range),
        ),
// (its cost is the trait method's `iter_next_cost(range)`, which is 0 for the std `Step` types
// by `axiom_next_cost_range`)

;

#[verifier::external_type_specification]
pub struct ExBound<T>(Bound<T>);

#[verifier::external_type_specification]
pub struct ExRangeFull(RangeFull);

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(Idx)]
pub struct ExRangeFrom<Idx>(RangeFrom<Idx>);

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(Idx)]
pub struct ExRangeTo<Idx>(RangeTo<Idx>);

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(Idx)]
pub struct ExRangeToInclusive<Idx>(RangeToInclusive<Idx>);

pub open spec fn bound_as_ref<T>(b: &Bound<T>) -> Bound<&T> {
    match b {
        Bound::Included(start) => Bound::Included(start),
        Bound::Excluded(start) => Bound::Excluded(start),
        Bound::Unbounded => Bound::Unbounded,
    }
}

// Per-type specifications for `RangeBounds::start_bound`/`end_bound`. Each spec
// agrees with the corresponding `RangeBoundsSpecImpl`, and so with the
// `ExRangeBounds` ensures below.
pub assume_specification<'s, T>[ <Range<T> as RangeBounds<T>>::start_bound ](
    range: &'s Range<T>,
) -> (result: Bound<&'s T>)
    ensures
        result == Bound::Included(&range.start),
    allocates
        0,
;

pub assume_specification<'s, T>[ <Range<T> as RangeBounds<T>>::end_bound ](
    range: &'s Range<T>,
) -> (result: Bound<&'s T>)
    ensures
        result == Bound::Excluded(&range.end),
    allocates
        0,
;

pub assume_specification<'s, T: ?Sized>[ <RangeFull as RangeBounds<T>>::start_bound ](
    range: &'s RangeFull,
) -> (result: Bound<&'s T>)
    ensures
        result == Bound::Unbounded,
    allocates
        0,
;

pub assume_specification<'s, T: ?Sized>[ <RangeFull as RangeBounds<T>>::end_bound ](
    range: &'s RangeFull,
) -> (result: Bound<&'s T>)
    ensures
        result == Bound::Unbounded,
    allocates
        0,
;

pub assume_specification<'s, T>[ <RangeFrom<T> as RangeBounds<T>>::start_bound ](
    range: &'s RangeFrom<T>,
) -> (result: Bound<&'s T>)
    ensures
        result == Bound::Included(&range.start),
    allocates
        0,
;

pub assume_specification<'s, T>[ <RangeFrom<T> as RangeBounds<T>>::end_bound ](
    range: &'s RangeFrom<T>,
) -> (result: Bound<&'s T>)
    ensures
        result == Bound::Unbounded,
    allocates
        0,
;

pub assume_specification<'s, T>[ <RangeTo<T> as RangeBounds<T>>::start_bound ](
    range: &'s RangeTo<T>,
) -> (result: Bound<&'s T>)
    ensures
        result == Bound::Unbounded,
    allocates
        0,
;

pub assume_specification<'s, T>[ <RangeTo<T> as RangeBounds<T>>::end_bound ](
    range: &'s RangeTo<T>,
) -> (result: Bound<&'s T>)
    ensures
        result == Bound::Excluded(&range.end),
    allocates
        0,
;

// Shared by `start_bound()`/`end_bound()` and their `RangeBoundsSpec` models.
pub open spec fn spec_range_inclusive_start_bound<T>(r: &RangeInclusive<T>) -> Bound<&T> {
    if spec_range_inclusive_is_empty(r) {
        spec_range_inclusive_unspecified_bounds(r).0
    } else {
        Bound::Included(&r@.start)
    }
}

pub open spec fn spec_range_inclusive_end_bound<T>(r: &RangeInclusive<T>) -> Bound<&T> {
    if spec_range_inclusive_is_empty(r) {
        spec_range_inclusive_unspecified_bounds(r).1
    } else {
        Bound::Included(&r@.end)
    }
}

pub assume_specification<'s, T>[ <RangeInclusive<T> as RangeBounds<T>>::start_bound ](
    range: &'s RangeInclusive<T>,
) -> (result: Bound<&'s T>)
    ensures
        result == spec_range_inclusive_start_bound(range),
    allocates
        0,
;

pub assume_specification<'s, T>[ <RangeInclusive<T> as RangeBounds<T>>::end_bound ](
    range: &'s RangeInclusive<T>,
) -> (result: Bound<&'s T>)
    ensures
        result == spec_range_inclusive_end_bound(range),
    allocates
        0,
;

pub assume_specification<'s, T>[ <RangeToInclusive<T> as RangeBounds<T>>::start_bound ](
    range: &'s RangeToInclusive<T>,
) -> (result: Bound<&'s T>)
    ensures
        result == Bound::Unbounded,
    allocates
        0,
;

pub assume_specification<'s, T>[ <RangeToInclusive<T> as RangeBounds<T>>::end_bound ](
    range: &'s RangeToInclusive<T>,
) -> (result: Bound<&'s T>)
    ensures
        result == Bound::Included(&range.end),
    allocates
        0,
;

pub assume_specification<'s, T>[ <(Bound<T>, Bound<T>) as RangeBounds<T>>::start_bound ](
    range: &'s (Bound<T>, Bound<T>),
) -> (result: Bound<&'s T>)
    ensures
        result == bound_as_ref(&range.0),
    allocates
        0,
;

pub assume_specification<'s, T>[ <(Bound<T>, Bound<T>) as RangeBounds<T>>::end_bound ](
    range: &'s (Bound<T>, Bound<T>),
) -> (result: Bound<&'s T>)
    ensures
        result == bound_as_ref(&range.1),
    allocates
        0,
;

/// Specification for [`core::ops::RangeBounds`], exposing spec-mode models
/// [`spec_start_bound`](RangeBoundsSpec::spec_start_bound) and
/// [`spec_end_bound`](RangeBoundsSpec::spec_end_bound) of the trait's
/// `start_bound`/`end_bound` methods. This mirrors std's normalization of an
/// arbitrary range into a pair of bounds and is the model used by
/// `<[T]>::copy_within` (see `vstd::std_specs::slice`). Implementations must
/// return these spec bounds from `start_bound`/`end_bound`, since std's
/// `copy_within` calls those methods.
#[verifier::external_trait_specification]
#[verifier::external_trait_extension(RangeBoundsSpec via RangeBoundsSpecImpl)]
pub trait ExRangeBounds<T: ?Sized> {
    type ExternalTraitSpecificationFor: RangeBounds<T>;

    spec fn spec_start_bound(&self) -> Bound<&T>;

    spec fn spec_end_bound(&self) -> Bound<&T>;

    fn start_bound(&self) -> (r: Bound<&T>)
        ensures
            r == self.spec_start_bound(),
    ;

    fn end_bound(&self) -> (r: Bound<&T>)
        ensures
            r == self.spec_end_bound(),
    ;
}

impl<T> RangeBoundsSpecImpl<T> for Range<T> {
    open spec fn spec_start_bound(&self) -> Bound<&T> {
        Bound::Included(&self.start)
    }

    open spec fn spec_end_bound(&self) -> Bound<&T> {
        Bound::Excluded(&self.end)
    }
}

impl<T: ?Sized> RangeBoundsSpecImpl<T> for RangeFull {
    open spec fn spec_start_bound(&self) -> Bound<&T> {
        Bound::Unbounded
    }

    open spec fn spec_end_bound(&self) -> Bound<&T> {
        Bound::Unbounded
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeFrom<T> {
    open spec fn spec_start_bound(&self) -> Bound<&T> {
        Bound::Included(&self.start)
    }

    open spec fn spec_end_bound(&self) -> Bound<&T> {
        Bound::Unbounded
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeTo<T> {
    open spec fn spec_start_bound(&self) -> Bound<&T> {
        Bound::Unbounded
    }

    open spec fn spec_end_bound(&self) -> Bound<&T> {
        Bound::Excluded(&self.end)
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeInclusive<T> {
    open spec fn spec_start_bound(&self) -> Bound<&T> {
        spec_range_inclusive_start_bound(self)
    }

    open spec fn spec_end_bound(&self) -> Bound<&T> {
        spec_range_inclusive_end_bound(self)
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeToInclusive<T> {
    open spec fn spec_start_bound(&self) -> Bound<&T> {
        Bound::Unbounded
    }

    open spec fn spec_end_bound(&self) -> Bound<&T> {
        Bound::Included(&self.end)
    }
}

impl<T> RangeBoundsSpecImpl<T> for (Bound<T>, Bound<T>) {
    open spec fn spec_start_bound(&self) -> Bound<&T> {
        bound_as_ref(&self.0)
    }

    open spec fn spec_end_bound(&self) -> Bound<&T> {
        bound_as_ref(&self.1)
    }
}

impl<'a, T: ?Sized + 'a> RangeBoundsSpecImpl<T> for (Bound<&'a T>, Bound<&'a T>) {
    open spec fn spec_start_bound(&self) -> Bound<&T> {
        self.0
    }

    open spec fn spec_end_bound(&self) -> Bound<&T> {
        self.1
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeFrom<&T> {
    open spec fn spec_start_bound(&self) -> Bound<&T> {
        Bound::Included(self.start)
    }

    open spec fn spec_end_bound(&self) -> Bound<&T> {
        Bound::Unbounded
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeTo<&T> {
    open spec fn spec_start_bound(&self) -> Bound<&T> {
        Bound::Unbounded
    }

    open spec fn spec_end_bound(&self) -> Bound<&T> {
        Bound::Excluded(self.end)
    }
}

impl<T> RangeBoundsSpecImpl<T> for Range<&T> {
    open spec fn spec_start_bound(&self) -> Bound<&T> {
        Bound::Included(self.start)
    }

    open spec fn spec_end_bound(&self) -> Bound<&T> {
        Bound::Excluded(self.end)
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeInclusive<&T> {
    open spec fn spec_start_bound(&self) -> Bound<&T> {
        if spec_range_inclusive_is_empty(self) {
            spec_range_inclusive_unspecified_ref_bounds(self).0
        } else {
            Bound::Included(self@.start)
        }
    }

    open spec fn spec_end_bound(&self) -> Bound<&T> {
        if spec_range_inclusive_is_empty(self) {
            spec_range_inclusive_unspecified_ref_bounds(self).1
        } else {
            Bound::Included(self@.end)
        }
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeToInclusive<&T> {
    open spec fn spec_start_bound(&self) -> Bound<&T> {
        Bound::Unbounded
    }

    open spec fn spec_end_bound(&self) -> Bound<&T> {
        Bound::Included(self.end)
    }
}

/// Normalized (inclusive) start index of `range`, matching std's
/// `core::slice::range`: an inclusive bound `i` stays `i`, an exclusive bound
/// `i` becomes `i + 1`, and an unbounded start is `0`.
pub open spec fn slice_range_start<R: RangeBoundsSpec<usize>>(range: &R) -> int {
    match range.spec_start_bound() {
        Bound::Included(i) => *i as int,
        Bound::Excluded(i) => (*i as int) + 1,
        Bound::Unbounded => 0,
    }
}

/// Normalized (exclusive) end index of a range over a sequence of length `len`,
/// matching std's `core::slice::range`: an inclusive bound `i` becomes `i + 1`,
/// an exclusive bound `i` stays `i`, and an unbounded end is `len`.
pub open spec fn slice_range_end<R: RangeBoundsSpec<usize>>(range: &R, len: nat) -> int {
    match range.spec_end_bound() {
        Bound::Included(i) => (*i as int) + 1,
        Bound::Excluded(i) => *i as int,
        Bound::Unbounded => len as int,
    }
}

/// Whether a range normalizes to `start <= end <= len`, i.e. the condition
/// under which std's `core::slice::range` does not panic.
pub open spec fn slice_range_valid<R: RangeBoundsSpec<usize>>(range: &R, len: nat) -> bool {
    slice_range_start(range) <= slice_range_end(range, len) <= len
}

} // verus!
macro_rules! step_specs {
    ($t: ty, $axiom: ident, $step_axiom: ident) => {
        verus! {
        impl StepSpecImpl for $t {
            open spec fn spec_is_lt(self, other: Self) -> bool {
                self < other
            }
            open spec fn spec_steps_between(self, end: Self) -> Option<usize> {
                let n = end - self;
                if usize::MIN <= n <= usize::MAX {
                    Some(n as usize)
                } else {
                    None
                }
            }
            open spec fn spec_steps_between_int(self, end: Self) -> int {
                end - self
            }
            open spec fn spec_forward_checked(self, count: usize) -> Option<Self> {
                StepSpec::spec_forward_checked_int(self, count as int)
            }
            open spec fn spec_forward_checked_int(self, count: int) -> Option<Self> {
                if self + count <= $t::MAX {
                    Some((self + count) as $t)
                } else {
                    None
                }
            }
            open spec fn spec_backward_checked(self, count: usize) -> Option<Self> {
                StepSpec::spec_backward_checked_int(self, count as int)
            }
            open spec fn spec_backward_checked_int(self, count: int) -> Option<Self> {
                if self - count >= $t::MIN {
                    Some((self - count) as $t)
                } else {
                    None
                }
            }
        }
        pub broadcast proof fn $step_axiom()
            ensures
                #[trigger] obeys_range_step_spec::<$t>(),
        {
            admit();
        }

        // TODO: we might be able to make this generic over A: StepSpec
        // once we settle on a way to connect std traits like Step with spec traits like StepSpec.
        pub broadcast proof fn $axiom(range: Range<$t>)
            ensures
                StepSpec::spec_is_lt(range.start, range.end) ==>
                    // TODO (not important): use new "matches ==>" syntax here
                    (if let Some(n) = StepSpec::spec_forward_checked(range.start, 1) {
                        spec_range_next(range) == (Range { start: n, ..range }, Some(range.start))
                    } else {
                        true
                    }),
                !StepSpec::spec_is_lt(range.start, range.end) ==>
                    #[trigger] spec_range_next(range) == (range, None::<$t>),
        {
            admit();
        }
        } // verus!
    };
}

step_specs!(u8, axiom_spec_range_next_u8, axiom_u8_obeys_range_step_spec);
step_specs!(u16, axiom_spec_range_next_u16, axiom_u16_obeys_range_step_spec);
step_specs!(u32, axiom_spec_range_next_u32, axiom_u32_obeys_range_step_spec);
step_specs!(u64, axiom_spec_range_next_u64, axiom_u64_obeys_range_step_spec);
step_specs!(u128, axiom_spec_range_next_u128, axiom_u128_obeys_range_step_spec);
step_specs!(usize, axiom_spec_range_next_usize, axiom_usize_obeys_range_step_spec);
step_specs!(i8, axiom_spec_range_next_i8, axiom_i8_obeys_range_step_spec);
step_specs!(i16, axiom_spec_range_next_i16, axiom_i16_obeys_range_step_spec);
step_specs!(i32, axiom_spec_range_next_i32, axiom_i32_obeys_range_step_spec);
step_specs!(i64, axiom_spec_range_next_i64, axiom_i64_obeys_range_step_spec);
step_specs!(i128, axiom_spec_range_next_i128, axiom_i128_obeys_range_step_spec);
step_specs!(isize, axiom_spec_range_next_isize, axiom_isize_obeys_range_step_spec);

macro_rules! std_step_alloc_free {
    ($t: ty, $axiom: ident) => {
        verus! {
        pub broadcast axiom fn $axiom()
            ensures
                #[trigger] std_step_alloc_free::<$t>(),
        ;
        }
    };
}

std_step_alloc_free!(u8, axiom_std_step_alloc_free_u8);
std_step_alloc_free!(u16, axiom_std_step_alloc_free_u16);
std_step_alloc_free!(u32, axiom_std_step_alloc_free_u32);
std_step_alloc_free!(u64, axiom_std_step_alloc_free_u64);
std_step_alloc_free!(u128, axiom_std_step_alloc_free_u128);
std_step_alloc_free!(usize, axiom_std_step_alloc_free_usize);
std_step_alloc_free!(i8, axiom_std_step_alloc_free_i8);
std_step_alloc_free!(i16, axiom_std_step_alloc_free_i16);
std_step_alloc_free!(i32, axiom_std_step_alloc_free_i32);
std_step_alloc_free!(i64, axiom_std_step_alloc_free_i64);
std_step_alloc_free!(i128, axiom_std_step_alloc_free_i128);
std_step_alloc_free!(isize, axiom_std_step_alloc_free_isize);
std_step_alloc_free!(char, axiom_std_step_alloc_free_char);
// (their `Step` is arithmetic on the address as `u32`/`u128`)
std_step_alloc_free!(core::net::Ipv4Addr, axiom_std_step_alloc_free_ipv4addr);
std_step_alloc_free!(core::net::Ipv6Addr, axiom_std_step_alloc_free_ipv6addr);

verus! {

pub broadcast group group_range_axioms {
    axiom_next_cost_range_inclusive,
    axiom_aux_alloc_free_range_inclusive,
    axiom_next_cost_range,
    axiom_aux_alloc_free_range,
    axiom_range_inclusive_out_of_order,
    axiom_range_inclusive_empty_contains,
    axiom_u8_obeys_range_step_spec,
    axiom_u16_obeys_range_step_spec,
    axiom_u32_obeys_range_step_spec,
    axiom_u64_obeys_range_step_spec,
    axiom_u128_obeys_range_step_spec,
    axiom_usize_obeys_range_step_spec,
    axiom_i8_obeys_range_step_spec,
    axiom_i16_obeys_range_step_spec,
    axiom_i32_obeys_range_step_spec,
    axiom_i64_obeys_range_step_spec,
    axiom_i128_obeys_range_step_spec,
    axiom_isize_obeys_range_step_spec,
    axiom_spec_range_next_u8,
    axiom_spec_range_next_u16,
    axiom_spec_range_next_u32,
    axiom_spec_range_next_u64,
    axiom_spec_range_next_u128,
    axiom_spec_range_next_usize,
    axiom_spec_range_next_i8,
    axiom_spec_range_next_i16,
    axiom_spec_range_next_i32,
    axiom_spec_range_next_i64,
    axiom_spec_range_next_i128,
    axiom_spec_range_next_isize,
    axiom_std_step_alloc_free_u8,
    axiom_std_step_alloc_free_u16,
    axiom_std_step_alloc_free_u32,
    axiom_std_step_alloc_free_u64,
    axiom_std_step_alloc_free_u128,
    axiom_std_step_alloc_free_usize,
    axiom_std_step_alloc_free_i8,
    axiom_std_step_alloc_free_i16,
    axiom_std_step_alloc_free_i32,
    axiom_std_step_alloc_free_i64,
    axiom_std_step_alloc_free_i128,
    axiom_std_step_alloc_free_isize,
    axiom_std_step_alloc_free_char,
    axiom_std_step_alloc_free_ipv4addr,
    axiom_std_step_alloc_free_ipv6addr,
}

} // verus!
