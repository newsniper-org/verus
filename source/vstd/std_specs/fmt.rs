use super::super::prelude::*;
use core::fmt::{Arguments, Error, Formatter};

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExError(Error);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExFormatter<'a>(Formatter<'a>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExArguments<'a>(Arguments<'a>);

// Rust has a specially handled private module core::fmt::rt,
// for which we can't directly declare specifications because it is private.
// To work around this, declare our own rt module,
// which Verus specially recognizes as a stand-in for core::fmt::rt:
#[verifier::external]
mod rt {
    #[verusfmt::skip]
    #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument")]
    pub struct Argument<'a>(&'a ());

    impl<'a> Argument<'a> {
        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_binary")]
        pub fn new_binary<'b, T: core::fmt::Binary>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_debug")]
        pub fn new_debug<'b, T: core::fmt::Debug>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_debug_noop")]
        pub fn new_debug_noop<'b, T: core::fmt::Debug>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_display")]
        pub fn new_display<'b, T: core::fmt::Display>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_lower_exp")]
        pub fn new_lower_exp<'b, T: core::fmt::LowerExp>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_lower_hex")]
        pub fn new_lower_hex<'b, T: core::fmt::LowerHex>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_octal")]
        pub fn new_octal<'b, T: core::fmt::Octal>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_pointer")]
        pub fn new_pointer<'b, T: core::fmt::Pointer>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_upper_exp")]
        pub fn new_upper_exp<'b, T: core::fmt::UpperExp>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_upper_hex")]
        pub fn new_upper_hex<'b, T: core::fmt::UpperHex>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::from_usize")]
        pub fn from_usize<'b>(x: &'b usize) -> Argument<'b> {
            unimplemented!()
        }
    }

}

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExArgument<'a>(rt::Argument<'a>);

// -V alloc-check: allocations performed by the user `fmt` callbacks that formatting `args` runs.
// Allocations of the output sink (such as a growing `String`) are charged to the sink's owner, not
// here; `alloc::fmt::format` has no bound because the number of times its `String` grows depends
// on the length of the output.
// For `Arguments::new`, Verus decodes rustc's template bytes (how many times each argument is
// formatted) and assumes `fmt_allocates(args) == sum_i count_i * fmt_arg_allocates_at(&arr, i)`.
pub uninterp spec fn fmt_allocates(args: Arguments<'_>) -> nat;

/// How many times the output `String` grows while `x` is formatted into it. The count depends on
/// the length of the output, which Verus does not model, so this is an opaque term: finite for
/// every `x`, but not bounded by a constant.
pub uninterp spec fn sink_growth<T: ?Sized>(x: &T) -> int;

/// The same for formatting `args` into a new `String`
pub uninterp spec fn format_growth(args: Arguments<'_>) -> int;

pub broadcast axiom fn axiom_sink_growth_nonneg<T: ?Sized>(x: &T)
    ensures
        #[trigger] sink_growth(x) >= 0,
;

pub broadcast axiom fn axiom_format_growth_nonneg(args: Arguments<'_>)
    ensures
        #[trigger] format_growth(args) >= 0,
;

/// The allocations of one call to the `fmt` method an `Argument` was made for.
pub uninterp spec fn fmt_arg_allocates(arg: rt::Argument<'_>) -> nat;

#[doc(hidden)]
pub uninterp spec fn fmt_witness_formatter<'f>() -> &'f mut Formatter<'f>;

#[doc(hidden)]
pub open spec fn fmt_arg_allocates_at<'a, const M: usize>(
    args: &[rt::Argument<'a>; M],
    i: int,
) -> nat {
    fmt_arg_allocates(args[i])
}

macro_rules! def_fmt_trait {
    ($trait:path, $extrait: ident, $spec_trait:ident, $impl_trait:ident, $new:ident) => {
        $crate::vstd::prelude::verus! {
            #[verifier::external_trait_specification]
            #[verifier::external_trait_extension($spec_trait via $impl_trait)]
            pub trait $extrait: core::marker::PointeeSized {
                type ExternalTraitSpecificationFor: $trait;

                spec fn fmt_req(&self, f: &Formatter<'_>) -> bool;

                fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>
                    requires
                        self.fmt_req(f);
            }

            // The `fmt` allocation bound of a type does not depend on the `Formatter` (checked by
            // -V alloc-check), so any formatter serves as the witness.
            #[doc(hidden)]
            pub assume_specification<'a, 'b, T: $trait>[ rt::Argument::<'a>::$new ](x: &'b T) -> (arg: rt::Argument<'b>)
                requires
                    forall|f: &Formatter<'a>| x.fmt_req(f),
                ensures
                    fmt_arg_allocates(arg) == call_allocates(<T as $trait>::fmt, (x, fmt_witness_formatter())),
                allocates 0
            ;
        }
};
}

def_fmt_trait!(core::fmt::Binary, ExBinary, BinarySpec, BinarySpecImpl, new_binary);

def_fmt_trait!(core::fmt::Debug, ExDebug, DebugSpec, DebugSpecImpl, new_debug);

def_fmt_trait!(core::fmt::Display, ExDisplay, DisplaySpec, DisplaySpecImpl, new_display);

def_fmt_trait!(core::fmt::LowerExp, ExLowerExp, LowerExpSpec, LowerExpSpecImpl, new_lower_exp);

def_fmt_trait!(core::fmt::LowerHex, ExLowerHex, LowerHexSpec, LowerHexSpecImpl, new_lower_hex);

def_fmt_trait!(core::fmt::Octal, ExOctal, OctalSpec, OctalSpecImpl, new_octal);

def_fmt_trait!(core::fmt::Pointer, ExPointer, PointerSpec, PointerSpecImpl, new_pointer);

def_fmt_trait!(core::fmt::UpperExp, ExUpperExp, UpperExpSpec, UpperExpSpecImpl, new_upper_exp);

def_fmt_trait!(core::fmt::UpperHex, ExUpperHex, UpperHexSpec, UpperHexSpecImpl, new_upper_hex);

#[doc(hidden)]
pub assume_specification<'a, 'b, T: core::fmt::Debug>[ rt::Argument::<'a>::new_debug_noop ](
    x: &'b T,
) -> (arg: rt::Argument<'b>)
    requires
        forall|f: &Formatter<'a>| x.fmt_req(f),
    ensures
        fmt_arg_allocates(arg) == call_allocates(
            <T as core::fmt::Debug>::fmt,
            (x, fmt_witness_formatter()),
        ),
    allocates
        0,
;

#[doc(hidden)]
// Only read as a width or precision (`as_u16`), never formatted.
pub assume_specification<'a, 'b>[ rt::Argument::<'a>::from_usize ](x: &'b usize) -> (arg:
    rt::Argument<'b>)
    requires
        *x <= u16::MAX,
    ensures
        fmt_arg_allocates(arg) == 0,
    allocates
        0,
;

pub assume_specification<'a>[ Arguments::<'a>::from_str ](s: &'static str) -> (args: Arguments<'a>)
    ensures
        fmt_allocates(args) == 0,
    allocates
        0,
;

pub assume_specification<'a>[ Arguments::<'a>::from_str_nonconst ](s: &'static str) -> (args:
    Arguments<'a>)
    ensures
        fmt_allocates(args) == 0,
    allocates
        0,
;

// Specially handled stand-in for Arguments::new (because it uses the private Argument type)
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::Arguments::new")]
#[verifier::external]
#[doc(hidden)]
pub fn arguments_new<'a, const N: usize, const M: usize>(
    template: &'a [u8; N],
    args: &'a [rt::Argument<'a>; M],
) -> Arguments<'a> {
    unimplemented!()
}

#[doc(hidden)]
pub assume_specification<'a, const N: usize, const M: usize>[ arguments_new ](
    template: &'a [u8; N],
    args: &'a [rt::Argument<'a>; M],
) -> Arguments<'a>
    ensures
// (Restates the definition; keeps `fmt_arg_allocates_at` available to the assumption
// -V alloc-check adds after this call.)

        forall|i: int|
            0 <= i < M ==> #[trigger] fmt_arg_allocates_at(args, i) == fmt_arg_allocates(args[i]),
    allocates
        0,
;

// The sink's own allocations are charged to whoever owns the sink.
pub assume_specification<'a>[ Formatter::<'a>::write_fmt ](
    f: &mut Formatter<'a>,
    args: Arguments<'_>,
) -> Result<(), Error>
    allocates
        fmt_allocates(args),
;

pub assume_specification<'a>[ Formatter::<'a>::write_str ](
    f: &mut Formatter<'a>,
    data: &str,
) -> Result<(), Error>
    allocates
        0,
;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub assume_specification[ alloc::fmt::format ](
    args: Arguments<'_>,
) -> alloc::string::String
// the `fmt` callbacks, and the growth of the new `String`

    allocates
        fmt_allocates(args) + format_growth(args),
;

pub uninterp spec fn fmt_req_all<A: ?Sized>() -> bool;

macro_rules! def_type_axiom {
    ($ty:ty, $name: ident) => {
        $crate::vstd::prelude::verus! {
            pub broadcast axiom fn $name()
                ensures
                    #[trigger] fmt_req_all::<$ty>();
        }
};
}

def_type_axiom!(u8, axiom_fmt_req_all_u8);

def_type_axiom!(u16, axiom_fmt_req_all_u16);

def_type_axiom!(u32, axiom_fmt_req_all_u32);

def_type_axiom!(u64, axiom_fmt_req_all_u64);

def_type_axiom!(u128, axiom_fmt_req_all_u128);

def_type_axiom!(usize, axiom_fmt_req_all_usize);

def_type_axiom!(i8, axiom_fmt_req_all_i8);

def_type_axiom!(i16, axiom_fmt_req_all_i16);

def_type_axiom!(i32, axiom_fmt_req_all_i32);

def_type_axiom!(i64, axiom_fmt_req_all_i64);

def_type_axiom!(i128, axiom_fmt_req_all_i128);

def_type_axiom!(isize, axiom_fmt_req_all_isize);

def_type_axiom!(f32, axiom_fmt_req_all_f32);

def_type_axiom!(f64, axiom_fmt_req_all_f64);

def_type_axiom!(bool, axiom_fmt_req_all_bool);

def_type_axiom!(char, axiom_fmt_req_all_char);

def_type_axiom!(str, axiom_fmt_req_all_str_slice);

def_type_axiom!(&str, axiom_fmt_req_all_str);

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
def_type_axiom!(alloc::string::String, axiom_fmt_req_all_string);

pub broadcast axiom fn axiom_fmt_req_all_ref<A>()
    requires
        fmt_req_all::<A>(),
    ensures
        #[trigger] fmt_req_all::<&A>(),
;

macro_rules! def_trait_axiom {
    ($trait:path, $name: ident) => {
        $crate::vstd::prelude::verus! {
            pub broadcast axiom fn $name<A: $trait + ?Sized>(a: &A, f: &Formatter)
                requires
                    fmt_req_all::<A>(),
                ensures
                    #[trigger] a.fmt_req(f);
        }
};
}

def_trait_axiom!(core::fmt::Binary, axiom_fmt_req_all_binary);

def_trait_axiom!(core::fmt::Debug, axiom_fmt_req_all_debug);

def_trait_axiom!(core::fmt::Display, axiom_fmt_req_all_display);

def_trait_axiom!(core::fmt::LowerExp, axiom_fmt_req_all_lower_exp);

def_trait_axiom!(core::fmt::LowerHex, axiom_fmt_req_all_lower_hex);

def_trait_axiom!(core::fmt::Octal, axiom_fmt_req_all_octal);

def_trait_axiom!(core::fmt::Pointer, axiom_fmt_req_all_pointer);

def_trait_axiom!(core::fmt::UpperExp, axiom_fmt_req_all_upper_exp);

def_trait_axiom!(core::fmt::UpperHex, axiom_fmt_req_all_upper_hex);

// -V alloc-check: no `fmt` bound depends on its `Formatter` (Verus rejects one that does, except
// for passing it on to another `fmt`), so the cost at any formatter equals the cost at the witness.
macro_rules! def_fmt_alloc_axiom {
    ($trait:path, $name: ident) => {
        $crate::vstd::prelude::verus! {
            pub broadcast axiom fn $name<A: $trait + ?Sized>(a: &A, f: &mut Formatter<'_>)
                ensures
                    #[trigger] call_allocates(<A as $trait>::fmt, (a, f))
                        == call_allocates(<A as $trait>::fmt, (a, fmt_witness_formatter())),
            ;
        }
};
}

def_fmt_alloc_axiom!(core::fmt::Binary, axiom_fmt_allocates_binary);

def_fmt_alloc_axiom!(core::fmt::Debug, axiom_fmt_allocates_debug);

def_fmt_alloc_axiom!(core::fmt::Display, axiom_fmt_allocates_display);

def_fmt_alloc_axiom!(core::fmt::LowerExp, axiom_fmt_allocates_lower_exp);

def_fmt_alloc_axiom!(core::fmt::LowerHex, axiom_fmt_allocates_lower_hex);

def_fmt_alloc_axiom!(core::fmt::Octal, axiom_fmt_allocates_octal);

def_fmt_alloc_axiom!(core::fmt::Pointer, axiom_fmt_allocates_pointer);

def_fmt_alloc_axiom!(core::fmt::UpperExp, axiom_fmt_allocates_upper_exp);

def_fmt_alloc_axiom!(core::fmt::UpperHex, axiom_fmt_allocates_upper_hex);

// -V alloc-check: formatting a primitive into a `Formatter` allocates nothing itself (the output
// sink's growth is charged to the sink's owner).
macro_rules! def_fmt_prim_alloc {
    ($ty:ty, $($trait:path),+) => {
        $(
            $crate::vstd::prelude::verus! {
                pub assume_specification[ <$ty as $trait>::fmt ](x: &$ty, f: &mut Formatter<'_>) -> Result<(), Error>
                    allocates 0
                ;
            }
        )+
};
}

def_fmt_prim_alloc!(u8, core::fmt::Display, core::fmt::Debug, core::fmt::Binary, core::fmt::Octal, core::fmt::LowerHex, core::fmt::UpperHex, core::fmt::LowerExp, core::fmt::UpperExp);

def_fmt_prim_alloc!(u16, core::fmt::Display, core::fmt::Debug, core::fmt::Binary, core::fmt::Octal, core::fmt::LowerHex, core::fmt::UpperHex, core::fmt::LowerExp, core::fmt::UpperExp);

def_fmt_prim_alloc!(u32, core::fmt::Display, core::fmt::Debug, core::fmt::Binary, core::fmt::Octal, core::fmt::LowerHex, core::fmt::UpperHex, core::fmt::LowerExp, core::fmt::UpperExp);

def_fmt_prim_alloc!(u64, core::fmt::Display, core::fmt::Debug, core::fmt::Binary, core::fmt::Octal, core::fmt::LowerHex, core::fmt::UpperHex, core::fmt::LowerExp, core::fmt::UpperExp);

def_fmt_prim_alloc!(u128, core::fmt::Display, core::fmt::Debug, core::fmt::Binary, core::fmt::Octal, core::fmt::LowerHex, core::fmt::UpperHex, core::fmt::LowerExp, core::fmt::UpperExp);

def_fmt_prim_alloc!(usize, core::fmt::Display, core::fmt::Debug, core::fmt::Binary, core::fmt::Octal, core::fmt::LowerHex, core::fmt::UpperHex, core::fmt::LowerExp, core::fmt::UpperExp);

def_fmt_prim_alloc!(i8, core::fmt::Display, core::fmt::Debug, core::fmt::Binary, core::fmt::Octal, core::fmt::LowerHex, core::fmt::UpperHex, core::fmt::LowerExp, core::fmt::UpperExp);

def_fmt_prim_alloc!(i16, core::fmt::Display, core::fmt::Debug, core::fmt::Binary, core::fmt::Octal, core::fmt::LowerHex, core::fmt::UpperHex, core::fmt::LowerExp, core::fmt::UpperExp);

def_fmt_prim_alloc!(i32, core::fmt::Display, core::fmt::Debug, core::fmt::Binary, core::fmt::Octal, core::fmt::LowerHex, core::fmt::UpperHex, core::fmt::LowerExp, core::fmt::UpperExp);

def_fmt_prim_alloc!(i64, core::fmt::Display, core::fmt::Debug, core::fmt::Binary, core::fmt::Octal, core::fmt::LowerHex, core::fmt::UpperHex, core::fmt::LowerExp, core::fmt::UpperExp);

def_fmt_prim_alloc!(i128, core::fmt::Display, core::fmt::Debug, core::fmt::Binary, core::fmt::Octal, core::fmt::LowerHex, core::fmt::UpperHex, core::fmt::LowerExp, core::fmt::UpperExp);

def_fmt_prim_alloc!(isize, core::fmt::Display, core::fmt::Debug, core::fmt::Binary, core::fmt::Octal, core::fmt::LowerHex, core::fmt::UpperHex, core::fmt::LowerExp, core::fmt::UpperExp);

def_fmt_prim_alloc!(f32, core::fmt::Display, core::fmt::Debug, core::fmt::LowerExp, core::fmt::UpperExp);

def_fmt_prim_alloc!(f64, core::fmt::Display, core::fmt::Debug, core::fmt::LowerExp, core::fmt::UpperExp);

def_fmt_prim_alloc!(bool, core::fmt::Display, core::fmt::Debug);

def_fmt_prim_alloc!(char, core::fmt::Display, core::fmt::Debug);

def_fmt_prim_alloc!(str, core::fmt::Display, core::fmt::Debug);

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
def_fmt_prim_alloc!(alloc::string::String, core::fmt::Display, core::fmt::Debug);

pub broadcast group group_fmt_axioms {
    axiom_sink_growth_nonneg,
    axiom_format_growth_nonneg,
    // types
    axiom_fmt_req_all_u8,
    axiom_fmt_req_all_u16,
    axiom_fmt_req_all_u32,
    axiom_fmt_req_all_u64,
    axiom_fmt_req_all_u128,
    axiom_fmt_req_all_usize,
    axiom_fmt_req_all_i8,
    axiom_fmt_req_all_i16,
    axiom_fmt_req_all_i32,
    axiom_fmt_req_all_i64,
    axiom_fmt_req_all_i128,
    axiom_fmt_req_all_isize,
    axiom_fmt_req_all_f32,
    axiom_fmt_req_all_f64,
    axiom_fmt_req_all_bool,
    axiom_fmt_req_all_char,
    axiom_fmt_req_all_str_slice,
    axiom_fmt_req_all_str,
    #[cfg(all(feature = "alloc", not(verus_verify_core)))]
    axiom_fmt_req_all_string,
    axiom_fmt_req_all_ref,
    // traits
    axiom_fmt_req_all_binary,
    axiom_fmt_req_all_debug,
    axiom_fmt_req_all_display,
    axiom_fmt_req_all_lower_exp,
    axiom_fmt_req_all_lower_hex,
    axiom_fmt_req_all_octal,
    axiom_fmt_req_all_pointer,
    axiom_fmt_req_all_upper_exp,
    axiom_fmt_req_all_upper_hex,
    // allocation bounds
    axiom_fmt_allocates_binary,
    axiom_fmt_allocates_debug,
    axiom_fmt_allocates_display,
    axiom_fmt_allocates_lower_exp,
    axiom_fmt_allocates_lower_hex,
    axiom_fmt_allocates_octal,
    axiom_fmt_allocates_pointer,
    axiom_fmt_allocates_upper_exp,
    axiom_fmt_allocates_upper_hex,
}

} // verus!
