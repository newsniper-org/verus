#[cfg(verus_keep_ghost)]
use super::super::super::modes::tracked_swap;
use super::super::super::prelude::*;
use super::super::Loc;
use super::super::algebra::ResourceAlgebra;
use super::super::pcm::{PCM, Resource};
#[cfg(verus_keep_ghost)]
use super::super::relations::frame_preserving_update;

verus! {

/// A preorder `le` ("`other` is at least as good as `self`")
pub trait Preorder: Sized {
    spec fn le(self, other: Self) -> bool;

    proof fn le_refl(a: Self)
        ensures
            a.le(a),
    ;

    proof fn le_trans(a: Self, b: Self, c: Self)
        requires
            a.le(b),
            b.le(c),
        ensures
            a.le(c),
    ;
}

/// The carrier of the authoritative-state-with-a-lower-bound resource: an authoritative state `a`
/// and one (exclusive) fragment `s` with `s.le(a)`. See [`PreorderAuth`].
pub enum PreorderAuthCarrier<S> {
    Unit,
    Auth(S),
    Frag(S),
    Both(S, S),
    Invalid,
}

impl<S: Preorder> ResourceAlgebra for PreorderAuthCarrier<S> {
    open spec fn valid(self) -> bool {
        match self {
            PreorderAuthCarrier::Invalid => false,
            PreorderAuthCarrier::Both(a, s) => s.le(a),
            _ => true,
        }
    }

    open spec fn op(a: Self, b: Self) -> Self {
        match (a, b) {
            (PreorderAuthCarrier::Unit, x) => x,
            (x, PreorderAuthCarrier::Unit) => x,
            (
                PreorderAuthCarrier::Auth(a),
                PreorderAuthCarrier::Frag(s),
            ) => PreorderAuthCarrier::Both(a, s),
            (
                PreorderAuthCarrier::Frag(s),
                PreorderAuthCarrier::Auth(a),
            ) => PreorderAuthCarrier::Both(a, s),
            _ => PreorderAuthCarrier::Invalid,
        }
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn valid_op(a: Self, b: Self) {
    }
}

impl<S: Preorder> PCM for PreorderAuthCarrier<S> {
    open spec fn unit() -> Self {
        PreorderAuthCarrier::Unit
    }

    proof fn op_unit(self) {
    }

    proof fn unit_valid() {
    }
}

/// `PreorderAuth<S>` is one half of a pair of tokens, the other being [`PreorderFrag<S>`]. The
/// fragment is a lower bound of the authoritative state (in the preorder `S::le`), and there is
/// one fragment per authoritative state.
///
/// - The authoritative state alone can be raised (`raise`): the fragment, wherever it is, stays a
///   lower bound.
/// - Both can be moved together (`step`) to any new pair where the fragment is a lower bound,
///   in particular down.
///
/// `-V alloc-check` uses this for allocators with a state: the implementation keeps the
/// authoritative state, the callers' ghost heap the fragment (see `vstd::alloc_check`).
pub tracked struct PreorderAuth<S: Preorder> {
    r: Resource<PreorderAuthCarrier<S>>,
}

/// The (unique) lower bound of the authoritative state of a [`PreorderAuth<S>`]
pub tracked struct PreorderFrag<S: Preorder> {
    r: Resource<PreorderAuthCarrier<S>>,
}

impl<S: Preorder> PreorderAuth<S> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        self.r.value() is Auth
    }

    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn view(self) -> S {
        self.r.value()->Auth_0
    }

    pub proof fn new(s: S) -> (tracked out: (PreorderAuth<S>, PreorderFrag<S>))
        ensures
            out.0.id() == out.1.id(),
            out.0@ == s,
            out.1@ == s,
    {
        S::le_refl(s);
        let tracked r = Resource::alloc(PreorderAuthCarrier::Both(s, s));
        let tracked (a, f) = r.split(PreorderAuthCarrier::Auth(s), PreorderAuthCarrier::Frag(s));
        (PreorderAuth { r: a }, PreorderFrag { r: f })
    }

    /// The fragment is a lower bound of the authoritative state
    pub proof fn lower_bound(tracked &mut self, tracked frag: &PreorderFrag<S>)
        requires
            old(self).id() == frag.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@,
            frag@.le(old(self)@),
    {
        use_type_invariant(&*self);
        use_type_invariant(frag);
        self.r.validate_2(&frag.r);
    }

    /// Raise the authoritative state alone (the fragment, wherever it is, stays a lower bound)
    pub proof fn raise(tracked &mut self, new_state: S)
        requires
            old(self)@.le(new_state),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == new_state,
    {
        use_type_invariant(&*self);
        let a = self.r.value();
        let b = PreorderAuthCarrier::Auth(new_state);
        assert(frame_preserving_update(a, b)) by {
            assert forall|c|
                #![trigger PreorderAuthCarrier::op(a, c), PreorderAuthCarrier::op(b, c)]
                PreorderAuthCarrier::op(a, c).valid() implies PreorderAuthCarrier::op(
                b,
                c,
            ).valid() by {
                if let PreorderAuthCarrier::Frag(s) = c {
                    S::le_trans(s, self@, new_state);
                }
            }
        }
        let tracked mut old_self = Self::new(new_state).0;
        tracked_swap(self, &mut old_self);
        let tracked PreorderAuth { r } = old_self;
        let tracked mut new_self = PreorderAuth { r: r.update(b) };
        tracked_swap(self, &mut new_self);
    }

    /// Move the authoritative state and its fragment together
    pub proof fn step(
        tracked &mut self,
        tracked frag: &mut PreorderFrag<S>,
        new_auth: S,
        new_frag: S,
    )
        requires
            old(self).id() == old(frag).id(),
            new_frag.le(new_auth),
        ensures
            final(self).id() == old(self).id(),
            final(frag).id() == old(frag).id(),
            final(self)@ == new_auth,
            final(frag)@ == new_frag,
    {
        use_type_invariant(&*self);
        use_type_invariant(&*frag);
        let tracked (mut old_self, mut old_frag) = Self::new(new_auth);
        tracked_swap(self, &mut old_self);
        tracked_swap(frag, &mut old_frag);
        let tracked PreorderAuth { r: ra } = old_self;
        let tracked PreorderFrag { r: rf } = old_frag;
        let tracked r = ra.join(rf);
        let b = PreorderAuthCarrier::Both(new_auth, new_frag);
        let tracked r = r.update(b);
        let tracked (a, f) = r.split(
            PreorderAuthCarrier::Auth(new_auth),
            PreorderAuthCarrier::Frag(new_frag),
        );
        let tracked mut new_self = PreorderAuth { r: a };
        let tracked mut new_frag_tok = PreorderFrag { r: f };
        tracked_swap(self, &mut new_self);
        tracked_swap(frag, &mut new_frag_tok);
    }
}

impl<S: Preorder> PreorderFrag<S> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        self.r.value() is Frag
    }

    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn view(self) -> S {
        self.r.value()->Frag_0
    }
}

} // verus!
