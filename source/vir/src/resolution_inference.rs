/*!
This is the algorithm for computing the "resolution points" for mutable references,
i.e., the points where we resolve the prophecy ("future") variable in a mutable reference
to equal the "current" value.

The first important thing to understand about resolution is that it has nothing to do with
the *lifetimes*. Resolution is safe for any value *as long as that value will never be
mutated again*. In fact, it is crucial that this can happen before the end of a lifetime.
Consider:

```
fn example<'a>(pair: &'a mut (u64, u64) -> &'a mut u64 {
    &mut (*pair).0
}
```

Note that the lifetime clearly extends beyond the end of the function, but we will
always resolve `pair` at the end of the function. This might be surprising because
we are returning a mutable reference that is derived (via reborrow) from the input reference.
However, it remains the case that this is a different owned value. The input reference `pair`
is still resolved at the end of the function.

We effectively elaborate this example to look like this:

```
fn example<'a>(pair: &'a mut (u64, u64) -> &'a mut u64 {
    let return_value = &mut (*pair).0;    // mutates `pair`
    // resolve `pair` here
    return return_value;                  // moves `return_value`
}
```

We can resolve `pair` at line 2 because `pair` is never moved or mutated after that point.
This is necessary if we want to prove a postcondition like
`ensures mut_ref_future(return_value) == mut_ref_future(pair).0`.
The `return_value` however, IS moved at the end, so we don't resolve that one.

So again: we can determine the resolve points of a given owned value by looking at
that value in isolation, without considering global lifetime analysis.

### The analysis

The analysis operates over "places", e.g., `x` (where `x` is a local variable),
or projections from locals, e.g., `x.field.0`. This is necessary because Rust's ownership analysis
operates at this granular level, where a struct's fields can be moved independently.

For a given place P, it is safe to "resolve" it at any program point Q if:

 (i) It is "initialized" at Q (i.e., it has been assigned to and not subsequently moved from)

 (ii) It will never be moved from Q nor mutated until it is dropped.

Note that "resolution" here just means inserting an 'assume' statement into the code.
Resolution is thus idempotent, so there isn't any issue with "resolving" something more
than once. Also note that resolving p.x and p.y is the same as resolving p
(if x and y are the fields of p).

Obviously, we don't want to insert these assumptions more than necessary to avoid cluttering
the AIR code.  In general, it's best to insert the resolution as early as possible,
since that's most convenient for the user. This also guarantees that the resolution occurs
before the lifetime ends (assuming that our analysis is at least as precise as Rust's).

Also note that this method, in principle, works for any place, no matter what type it is,
even if it doesn't contains a mutable reference. Of course, if the place doesn't contain
a mutable reference, then resolution is a "trivial" operation.

Our algorithm then is roughly as follows:

 1. Turn the vir::ast::Expr into a control flow graph (CFG) with place-based operations relevant
    to the analysis (moves, mutations).

 2. Compute (i) with a forward dataflow analysis pass

 3. Compute (ii) with a backwards dataflow analysis pass

 4. Combine this information to determine, for each place P, where it's safe to
    insert Assume(HasResolved(p)). Perform an insertion at any point P where this is "useful"
    (i.e., it wasn't also safe at the previous program point(s)).

### Places behind mutable references

If `x: &mut T` is a place, then the dereference `*x` of type `T` is also a place, so we need
to consider the resolution of `*x` (e.g., in the case of nested mutable references).

However, the resolution of place `x` does NOT imply the resolution of place `*x`.
This is because of the value `*x` lives on in whatever place it was originally borrowed from.
However, there are cases where we might want to resolve `*x`, namely, when assigning to it:

```
*x = t;
```

This causes the old value of `*x` to be dropped, so we need to resolve that value here.

Thus, we need to treat the resolution of `x` independently of the resolution of `*x`.
This is in contrast with fields, where resolving `x` is equivalent to resolving all the
fields of `x`.

### Working with enums

In order to resolve the field of an enum (e.g., `opt->Some_0` for a varible `opt: Option<T>`),
the resolution needs to be conditional on the variant:

```
assume(opt is Some ==> has_resolved(opt->Some_0))
```

Since resolution is explicitly conditional, we don't need to account for variants
in the initialization analysis; when an enum place is initialized, we then consider all
fields of the enum to be initialized (until they are subsequently moved from).

More formally, we can define a notion of "conditional initialization": a place is
conditionally initialized if "parents being in the correct variant ==> place is initialized".

Example:

```
let x: Result<A, B> = Ok(foo);
```

There are two fields of interest, `x->Ok_0` and `x->Err_0`. In the above statement, *both*
of these fields are considered "conditionally initialized"

 * Ok_0 is "conditionally initialized" because it's "really" initialized
 * Err_0 is "conditionally initialized" in a vacuous sense because `x` is not in the Err state

Thus, we can compute the "conditionally initialized" places with a straightforward
analysis that treats enums like normal structs.

### Working with arrays

For an array of some known (i.e., non-generic) size `k`, we can treat it as a struct
with `k` fields for the purposes of this analysis.

There is a big difference between fields and indices:
you can move out of a field by with a field expression `a.f`,
but you can't move out of an array with an index expression `a[0]`.
The only situation where Rust allows a "partial move" from an array
is via an array pattern:

```rust
let [x, _] = a; // moves from a[0] but not from a[1]
```

And again, this requires a known, non-generic array size. Therefore:

 * When processing an index expressions `a[e]`, we don't need to construct a place
   more granular than `a`.
 * When processing an array pattern, we need to split the place `a` into its subplaces
   and analyze each individually, like for structs.

One snag here is that, while structs are generally limited to a reasonable size,
an array could be arbitrarily large, which could cause the analysis to hang.
Fortunately, this issue is ameliorated by the fact that we only split the array
when an array pattern appears, and the array pattern length is limited by the length
of the source code.

However, when we support `..` in array patterns, we will need to revisit this
and optimize the analysis.


### Notes about scopes

For the most part, we ignore the concept of a scope entirely in our CFG, so we don't
include specific instructions for 'dropping' a place at the ends of its scope.
Our analysis will simply detect that a given place isn't modified outside the scope.

For each loop, we always insert all possible resolution assumptions
at the beginning of each loop, since the structure of our AIR queries wouldn't otherwise contain
that information, at least not when loop_isolation=true. When inserting an assumption
into the expression, we always check that the local variable it refers to is actually
in scope, so, e.g., we won't end up resolving any variables declared inside a loop from
outside the loop. In all other cases, this check shouldn't matter.

### Working with temporaries

Sometimes we need to work with unnamed "temporary places", given by the PlaceX::Temporary
place, e.g., we might take a mutable reference of a computed expression:

```rust
let x = &mut foo(); // equivalent to `let mut tmp = foo(); let x = &mut tmp;`
```

or we might update a mutable reference returned by some function without assigning it

```rust
*func() = y; // equivalent to `let mut tmp = func(); *tmp = y;`
```

Furthermore, these temporary places might need resolving (just like any other place).
For example, suppose `pair()` returns `(&mut A, &mut A)`. If we write:

```rust
let x = pair().0;
```

Then `pair().1` goes unused and requires immediate resolution. (This last example
also illustrates that temporaries are nontrivial even when they are not mutated.)

In our analysis, we assign a TempId to each PlaceX::Temporary node, and in the
main part of the analysis, we treat these places just like any other places.
After we compute the set of resolutions to add, we find all temporary nodes that
are mentioned in the set. We then replace those temporaries with named Local nodes.

Specifically, we can replace the place node `Temporary(expr)` with
`WithExpr({ tmp = expr; }, Local("tmp"))` for a fresh `tmp` variable.
We place the declaration `let tmp;` at a larger scope.

### Closures

A closure is its own function, so its gets its own CFG. However, we still have to deal
with captured variables.

(Verus doesn't support capturing variables by mut-ref at the time of writing,
which makes things a bit easier for the time being.)

Note that our job is a *bit* simpler than having to compute the exact same set of
moves/references as rustc would for its MIR representation. For example,
if we consider something like:

```rust
let x = ...;
let foo = move || {
    let y = &x;
}
```

Technically, this moves `x` into the closure (since the closure is marked `move`) but because
the interior only uses an immutable reference to `x`, we can ignore the move when doing
analysis on the containing function.

In a similar vein, if we have a closure that only pulls in one field:

```rust
let x = ...;
let foo = move || {
    let y = x.0;
}
```

Rust might move the entirety of `x` instead of just `x.0` (this depends on the edition),
but the point it is doesn't matter: either way, for the sake of our analysis, we can say
that only `x.0` is getting moved (the semantics don't matter either way).
(In Rust, the difference only matters for computing where the drops go.)

Therefore, to determine what moves/mutations should represent the construction of the closure
in our analysis, we only need to look at what moves/mutations happen *inside* the closure.
(Though again, mutations of captured variables are currently disallowed.)

### Assignments

Typically when we do an assignment `x.f = 5;`,
we want to resolve the (overwritten) value of `x.f` from before the mutation.
For most places, this is already handled by our analysis, which marks `x.f` as
safe-to-resolve right before the assignment. We can't do this analysis for array/slice places
however, so we need to handle the case `x[i] = 5;` separately.
While building the CFG, we find all such cases (`assigns_to_resolve`) and update the
Expr appropriately (by setting the `resolve` field on the assignment nodes).

### User-defined type invariants

We handle type-invariants here, inserting nodes that will lower to assertions about type-invariants.
The analysis is pretty weak right now but could be improved.

*/

use crate::ast::{
    Arm, ArrayKind, BoundsCheck, ByRef, CtorUpdateTail, Datatype, Dt, Expr, ExprX, FieldOpr, Fun,
    FunWithVis, Function, Ident, Krate, Label, Mode, ModeWrapperMode, Params, Path, Pattern,
    PatternBinding, PatternX, Place, PlaceX, Primitive, ReadKind, SpannedTyped, Stmt, StmtX, Typ,
    TypDecoration, TypX, UnaryOpr, UnfinalizedReadKind, VarBinders, VarIdent, VarIdentDisambiguate,
    VariantCheck, VirErr,
};
use crate::ast_to_sst::Maybe;
use crate::ast_util::{
    bool_typ, mk_bool, mk_int_lit_from_usize, typ_to_diagnostic_str, undecorate_typ, unit_typ,
};
use crate::ast_visitor::VisitorScopeMap;
use crate::def::Spanned;
use crate::messages::error;
use crate::messages::{AstId, Span};
use crate::modes::ReadKindFinals;
use crate::patterns::pattern_has_mut;
use crate::resolution_types::ResolutionTypes;
use crate::sst_util::subst_typ_for_datatype;
use air::ast_util::str_ident;
use air::scope_map::ScopeMap;
use std::collections::HashSet;
use std::collections::{HashMap, VecDeque};
use std::sync::Arc;

/// Some inputs needed for the resolution analysis
pub struct ResolutionInfo {
    pub(crate) read_kind_finals: ReadKindFinals,
    pub(crate) typ_inv_info: crate::modes::TypeInvInfo,
    pub(crate) var_modes: HashMap<VarIdent, Mode>,
    pub(crate) temporary_modes: HashMap<AstId, Mode>,
    pub(crate) dual_mode: bool,
}

/// -V alloc-check: does the function count its deallocations (and so its implicit drops)?
/// (The same functions as those that get a deallocation counter in ast_to_sst_func.rs.)
pub fn function_counts_deallocations(
    function: &Function,
    functions: &HashMap<Fun, Function>,
    alloc_check: bool,
    check_api_safety: bool,
) -> bool {
    if !alloc_check
        || function.x.mode != Mode::Exec
        || check_api_safety
        || function.x.attrs.allocator_runtime
        || function.x.attrs.fip
    {
        return false;
    }
    if function.x.deallocations.is_some() {
        return true;
    }
    match &function.x.kind {
        crate::ast::FunctionKind::TraitMethodImpl { method, .. } => {
            functions.get(method).map(|m| m.x.deallocations.is_some()).unwrap_or(false)
        }
        _ => false,
    }
}

/// -V alloc-check: for each function that counts its implicit drops, the drops it charges (see
/// DropCounting): (the span of the local's binding or temporary's expression, the drop site,
/// whether the local is a parameter (whose span covers its type too))
pub type DropSites = HashMap<Fun, Vec<(Span, Span, bool)>>;

pub fn krate_infer_resolution(
    krate: &Krate,
    infos: &HashMap<Fun, Arc<ResolutionInfo>>,
    alloc_check: bool,
    check_api_safety: bool,
) -> Result<(Krate, DropSites), Vec<VirErr>> {
    let mut datatypes = HashMap::new();
    for datatype in krate.datatypes.iter() {
        let Dt::Path(path) = datatype.x.name.clone() else {
            return Err(vec![crate::messages::internal_error(
                &datatype.span,
                "Dt::Tuple in datatypes before `ast_simplify`",
            )]);
        };
        datatypes.insert(path, datatype.clone());
    }
    let mut functions = HashMap::new();
    for function in krate.functions.iter() {
        functions.insert(function.x.name.clone(), function.clone());
    }
    let rtypes = ResolutionTypes::new(&datatypes);

    let mut krate = krate.clone();
    let mut errors = vec![];
    let mut drop_sites = HashMap::new();
    for function in &mut Arc::make_mut(&mut krate).functions {
        if let Some(res_info) = infos.get(&function.x.name) {
            let count_drops = !res_info.dual_mode
                && function_counts_deallocations(
                    function,
                    &functions,
                    alloc_check,
                    check_api_safety,
                );
            let new_body = infer_resolution(
                &function.x.params,
                &function.x.body.as_ref().unwrap(),
                res_info,
                &datatypes,
                &functions,
                function.x.owning_module.as_ref().unwrap(),
                &rtypes,
                count_drops,
            );
            match new_body {
                Ok((new_body, sites)) => {
                    if let Some(sites) = sites {
                        drop_sites.insert(function.x.name.clone(), sites);
                    }
                    Arc::make_mut(function).x.body = Some(new_body);
                }
                Err(err) => {
                    errors.push(err);
                }
            }
        }
    }
    if errors.len() > 0 { Err(errors) } else { Ok((krate, drop_sites)) }
}

/// Updates the given function body to include assume(has_resolved(...)) nodes
/// at the appropriate places.
/// On the side, also handles some work related to user_defined_type_invariants.
///
/// This relies on the AstIds of the given Expr being unique, but it also destroys this property
/// in the transformation, returning an Expr that may have duplicate AstIds.
fn infer_resolution(
    params: &Params,
    body: &Expr,
    info: &ResolutionInfo,
    datatypes: &HashMap<Path, Datatype>,
    functions: &HashMap<Fun, Function>,
    module: &Path,
    rtypes: &ResolutionTypes,
    count_drops: bool,
) -> Result<(Expr, Option<Vec<(Span, Span, bool)>>), VirErr> {
    let (
        cfg,
        assigns_to_resolve,
        typ_inv_obligations,
        asserts,
        loops_with_no_back_edges,
        drop_counting,
    ) = new_cfg(
        params,
        body,
        &info.read_kind_finals,
        datatypes,
        functions,
        &info.var_modes,
        &info.temporary_modes,
        count_drops,
    )?;
    //println!("{:}", pretty_cfg(&cfg));
    let resolutions = if info.dual_mode { vec![] } else { get_resolutions(&cfg, rtypes, asserts) };
    let drops = match &drop_counting {
        Some(dc) => Some(drop_insertions(&cfg, dc)?),
        None => None,
    };
    let sites = drops.as_ref().map(|d| d.sites.clone());
    let e = apply_resolutions(
        &cfg,
        params,
        body,
        resolutions,
        assigns_to_resolve,
        typ_inv_obligations,
        &info.typ_inv_info,
        loops_with_no_back_edges,
        module,
        drops.unwrap_or_default(),
    )?;
    Ok((e, sites))
}

/// Represents the tree structure of "places" under consideration.
#[derive(Debug, Clone)]
enum PlaceTree {
    Leaf(Typ),
    /// We have 1 child for every non-ghost field. Use None in place of the ghost fields.
    /// Outer vec corresponds to variants, inner vec to fields of that variant.
    /// Use the same ordering as on the datatype.
    Struct(Typ, Dt, Vec<Vec<Option<PlaceTree>>>),
    MutRef(Typ, Box<PlaceTree>),
    /// We only handle arrays of known fixed length (i.e., non-generic length)
    Array(Typ, Vec<PlaceTree>),
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
struct TempId(u64);

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
enum LocalName {
    Named(VarIdent),
    /// AST ID of the PlaceX::Temporary
    Temporary(AstId, TempId),
}

/// A local var in the function, represents the base of any place.
/// The PlaceTree is expanded to represent the total amount of detail we need about this place,
/// which depends on how it is manipulated by the program.
///
/// For example, if we have a local variable `x: (T, T, T)`, and the programs assigns to `x.0`,
/// we would expand the tree to include [x.0, x.1, x.2]. If the program also assigns to `x.0.0`,
/// we expand it further, [[x.0.0, x.0.1] x.1, x.2]
///
/// Only non-ghost places should be represented.
#[derive(Debug)]
struct Local {
    name: LocalName,
    tree: PlaceTree,
}

/// Collection of all the locals in the program.
struct LocalCollection<'a> {
    locals: Vec<Local>,
    /// Map LocalName to index within the 'locals' vec
    ident_to_idx: HashMap<LocalName, usize>,

    /// Map AstId to temp id
    ast_id_to_temp_id: HashMap<AstId, TempId>,
    next_temp_id: u64,

    datatypes: &'a HashMap<Path, Datatype>,
    functions: &'a HashMap<Fun, Function>,
    var_modes: HashMap<VarIdent, Mode>,
    temporary_modes: &'a HashMap<AstId, Mode>,

    /// The locals whose trees are split below a `Box` (a part of the box's contents is a place
    /// of its own): -V alloc-check does not count their drops yet
    box_split: HashSet<usize>,
    /// -V alloc-check: the closures (`TypX::AnonymousClosure` ids) created in the function that
    /// move nothing into themselves, which have no drop glue (if Rust captures something by value
    /// after all, the MIR cross-check finds the drop uncharged)
    no_drop_closures: HashSet<usize>,
}

/// A projection that maps a place to a subplace
#[derive(Clone, Debug)]
pub(crate) enum ProjectionTyped {
    StructField(FieldOpr, Typ),
    DerefMut(Typ),
    Index(usize, Typ),
}

/// "Flattened" form of the vir::ast::Place type.
/// Only represents places based on locals, not temporaries.
#[derive(Clone, Debug)]
struct FlattenedPlaceTyped {
    pub local: LocalName,
    pub typ: Typ,
    pub projections: Vec<ProjectionTyped>,
}

/// Untyped version of the ProjectionTyped. The indices are used to walk the PlaceTree.
#[derive(Clone, Copy, PartialEq, Eq, Debug, PartialOrd, Ord)]
enum Projection {
    StructField((usize, usize)),
    DerefMut,
    Index(usize),
}

// note: sort_and_remove_redundant relies on sorting order
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct FlattenedPlace {
    local: usize,
    projections: Vec<Projection>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum TypInv {
    Yes,
    No,
    PatternError,
}

/// Represents a position in the vir::ast::Expr where an AssumeResolved can be inserted.
#[derive(Clone, Copy, Debug)]
enum AstPosition {
    /// Right before an Expr or Stmt with the given ID
    Before(AstId),
    /// Right after an Expr or Stmt with the given ID
    After(AstId),
    /// For an ExprX::Call node, right after evaluation of the arguments but before the call itself
    AfterArguments(AstId),
    /// Immediately after a call in the 'unwinding' case.
    /// (Currently this is place is not representable in VIR so we do nothing with these.)
    OnUnwind(#[allow(dead_code)] AstId),
    /// After the given bool-typed Expr, only when that expression evaluates to the given bool
    AfterBool(AstId, bool),
    /// For a PlaceX::Temporary node, this is right after assignment to that temporary.
    AfterTempAssignment(AstId),
    /// Extra place generated during Match that doesn't go anywhere nice
    MatchIntermediate,
    /// For an ExprX::Assign node, after the evaluation of the right-hand side, before the
    /// write (where the old value is dropped)
    BeforeAssignWrite(AstId),
}

struct Instruction {
    kind: InstructionKind,
    /// Position in the Expr that corresponds to the point right *after* the execution of
    /// this instruction.
    post_instruction_position: AstPosition,
}

enum InstructionKind {
    /// Move from the place; must previously be initialized, becomes uninitialized.
    MoveFrom(FlattenedPlace),
    /// Overwrite the place; it previously may be initialized, uninitialized,
    /// or partially initialized. Whatever was there before gets dropped.
    /// The place is subsequently initialized.
    Overwrite(FlattenedPlace),
    /// Mutate the value at the place, which must previously be initialized and remains initialized
    Mutate(FlattenedPlace),
    /// Drop whatever is here; the place may previously be initialized, uninitialized,
    /// or partially initialized. Whatever was there before gets dropped.
    /// The place is subsequently uninitialized.
    DropFrom(FlattenedPlace),
    /// -V alloc-check: a drop of the program (`DropCounting::drops[i]`), counted for a function
    /// with a `deallocates` bound. The analyses for resolution ignore it.
    ChargedDrop(usize),
}

type BBIndex = usize;
struct BasicBlock {
    instructions: Vec<Instruction>,
    /// Basic blocks that might jump to this one
    predecessors: Vec<BBIndex>,
    /// Basic blocks that we might jump to after the end
    successors: Vec<BBIndex>,
    /// Can we enter here?
    /// (Should be one entry for the whole function, and one entry for every closure)
    is_entry: bool,
    /// Is it possible to return from the function at the end of this basic block
    /// (i.e., as opposed to jumping to another basic block)
    is_exit: bool,

    /// Do we always want to add resolutions for all possibly relevant places at the beginning
    /// of this basic block? (This is used for loops, see the explanation above.)
    always_add_resolution_at_start: bool,

    /// Position in the Expr that corresponds to the start of the basic block
    position_of_start: AstPosition,
}

struct CFG<'a> {
    basic_blocks: Vec<BasicBlock>,
    locals: LocalCollection<'a>,
}

#[derive(Debug)]
struct ResolutionToInsert {
    place: FlattenedPlace,
    position: AstPosition,
}

////// CFG builder

struct Builder<'a> {
    basic_blocks: Vec<BasicBlock>,
    locals: LocalCollection<'a>,
    assigns_to_resolve: Vec<AstId>,
    typ_inv_obligations: Vec<(AstId, FunWithVis)>,
    asserts: Vec<((BBIndex, usize), Expr)>,
    loops_with_no_back_edges: HashSet<AstId>,
    errors: Vec<VirErr>,

    /// Loop stack, outermost to innermost
    loops: Vec<LoopEntry>,
    /// First element is the outermost fn, followed by closure stack, outermost to innermost
    fns: Vec<FnScope>,

    read_kind_finals: &'a ReadKindFinals,

    /// -V alloc-check: the implicit drops of a function with a `deallocates` bound
    drop_counting: Option<DropCounting>,
}

/// -V alloc-check, `deallocates d`: the function's implicit drops, which are charged to its
/// deallocation counter (`ExprX::ChargeDeallocations`).
///
/// The drop points are those of rustc's MIR (before drop elaboration): a local is dropped at the
/// end of its scope (a block for a `let`, an arm for the bindings of a match arm, the body for a
/// parameter), on every path that leaves the scope (the end of the scope, `return`, `break`,
/// `continue`); a temporary at the end of its statement; an overwritten place before an
/// assignment writes it. At a drop point we charge `drop_deallocations` of each leaf of the place
/// that may be initialized there (as drop elaboration drops the initialized parts): a leaf that
/// is initialized on some paths only is charged under a ghost drop flag. The closures inside the
/// function are not part of it (they cannot have a bound of their own yet).
///
/// The erase compile checks, on the MIR after drop elaboration, that each drop that may
/// deallocate is one charged here (the same local and drop site, `drop_sites`); this analysis
/// is not otherwise trusted to agree with rustc's.
struct DropCounting {
    /// The drop scopes of the outermost function, parallel to its `ScopeMap`'s scopes
    scopes: Vec<DropScope>,
    /// For each enclosing loop (parallel to `Builder::loops`): the numbers of drop scopes and of
    /// statements around it
    loop_depths: Vec<(usize, usize)>,
    /// The spans of the enclosing blocks (the drop site of their `let` bindings)
    block_spans: Vec<Span>,
    /// The statements being built (innermost last), with the temporaries created in each
    stmts: Vec<(Span, Vec<usize>)>,
    /// Temporaries outside of any statement (dropped at the end of the body)
    body_temps: Vec<usize>,
    /// The function body (whose end also drops the parameters)
    body_id: AstId,
    body_span: Span,
    /// The drop points (`InstructionKind::ChargedDrop`)
    drops: Vec<DropPoint>,
    /// The span of each local's binding or temporary's expression (for the MIR cross-check)
    local_spans: HashMap<LocalName, Span>,
    /// The parameters (whose spans cover their types too)
    params: HashSet<VarIdent>,
}

struct DropScope {
    /// The exec-mode variables bound by value in the scope
    vars: Vec<VarIdent>,
    /// The span whose end is the drop site of the variables
    site: Option<Span>,
}

struct DropPoint {
    kind: DropKind,
    /// The drop site (the span of the scope or statement that ends, or of the assigned place)
    site: Span,
    /// Where the instruction is in the CFG (block, index)
    loc: (BBIndex, usize),
    position: AstPosition,
}

enum DropKind {
    /// The place goes out of scope: its initialized leaves are dropped (and it is then
    /// uninitialized)
    ScopeEnd(FlattenedPlace),
    /// An assignment overwrites the place: its initialized leaves are dropped
    Assign(FlattenedPlace),
    /// An assignment overwrites a place behind a mutable reference (always initialized): its
    /// whole old value is dropped
    AssignWhole(FlattenedPlace),
    /// An assignment overwrites a place that is not tracked (an element of an array, a field of
    /// a type with a `Drop` impl): its whole old value is dropped. (The tracked place that
    /// contains it.)
    AssignUntracked(FlattenedPlace),
}

#[derive(Clone)]
struct LoopEntry {
    label: Label,
    /// BB to jump to on 'break'
    break_bb: BBIndex,
    /// BB to jump to on 'continue'
    continue_bb: BBIndex,
    /// Have we encountered a 'continue' for this loop?
    continue_taken: bool,
}

/// Represents the scope for either the top-level fn or for any closure inside it
/// Tracks the "upvars", i.e., vars captured by the closure
/// (any var declared outside the closure but referenced from within it)
#[derive(Debug)]
struct FnScope {
    scope_map: ScopeMap<VarIdent, ()>,
    upvars_mutated: Vec<FlattenedPlace>,
    upvars_moved: Vec<FlattenedPlace>,
}

#[derive(Clone, Debug)]
enum ComputedPlaceTyped {
    /// Subfield of some local
    Exact(FlattenedPlaceTyped),
    /// Exec-mode subplace of some local, at a granularity that we don't track
    /// The place given here is the most-specific non-spec place that we might do analysis over.
    /// Note that we don't track indices, and we don't track fields of datatypes with Drop impls.
    /// Examples:
    ///  * If the place is like `x.g[i].f` then we'd return Partial(x.g).
    ///  * if the place is like `w.f` where `w` has a Drop impl, then we'd return Partial(w).
    Partial(FlattenedPlaceTyped),
    /// Spec-mode place.
    /// The field is the most specific non-spec-mode place that we can track,
    /// or None if the local itself is ghost.
    /// Examples:
    ///   * If the user writes x.foo.bar, and `x.foo` is proof-mode but `x.foo.bar`
    ///     is spec-mode, then return the place `x.foo`.
    ///   * If the user writes x.foo.bar and `x` is spec-mode, then None.
    ///   * If the user writes `x.foo[i].y` where `x.foo` is exec/proof and
    ///     `y` is a ghost place then return `x.foo`
    Ghost(Option<FlattenedPlaceTyped>),
}

#[derive(Debug)]
enum ComputedPlace {
    Exact(FlattenedPlace),
    Partial(FlattenedPlace),
    Ghost(Option<FlattenedPlace>),
}

/// Compute the CFG for the given expression.
fn new_cfg<'a>(
    params: &Params,
    body: &Expr,
    read_kind_finals: &'a ReadKindFinals,
    datatypes: &'a HashMap<Path, Datatype>,
    functions: &'a HashMap<Fun, Function>,
    var_modes: &'a HashMap<VarIdent, Mode>,
    temporary_modes: &'a HashMap<AstId, Mode>,
    count_drops: bool,
) -> Result<
    (
        CFG<'a>,
        Vec<AstId>,
        Vec<(AstId, FunWithVis)>,
        Vec<((BBIndex, usize), Expr)>,
        HashSet<AstId>,
        Option<DropCounting>,
    ),
    VirErr,
> {
    let mut var_modes = var_modes.clone();
    for p in params.iter() {
        var_modes.insert(p.x.name.clone(), p.x.mode);
    }

    let mut builder = Builder {
        basic_blocks: vec![],
        loops: vec![],
        fns: vec![],
        assigns_to_resolve: vec![],
        typ_inv_obligations: vec![],
        loops_with_no_back_edges: HashSet::new(),
        asserts: vec![],
        errors: vec![],
        locals: LocalCollection {
            locals: vec![],
            ident_to_idx: HashMap::new(),
            ast_id_to_temp_id: HashMap::new(),
            next_temp_id: 0,
            datatypes,
            functions,
            var_modes,
            temporary_modes,
            box_split: HashSet::new(),
            no_drop_closures: HashSet::new(),
        },
        read_kind_finals,
        drop_counting: if count_drops {
            Some(DropCounting {
                scopes: vec![],
                loop_depths: vec![],
                block_spans: vec![],
                stmts: vec![],
                body_temps: vec![],
                body_id: body.span.id,
                body_span: body.span.clone(),
                drops: vec![],
                local_spans: HashMap::new(),
                params: params.iter().map(|p| p.x.name.clone()).collect(),
            })
        } else {
            None
        },
    };
    let start_bb = builder.new_bb(AstPosition::Before(body.span.id), true);
    builder.basic_blocks[start_bb].is_entry = true;

    builder.push_fn();
    builder.push_scope();
    if builder.counting_drops() {
        // (the parameters are dropped at the end of the body)
        let vars = params
            .iter()
            .filter(|p| p.x.mode == Mode::Exec)
            .map(|p| p.x.name.clone())
            .collect::<Vec<_>>();
        let dc = builder.drop_counting.as_mut().unwrap();
        for param in params.iter() {
            dc.local_spans.insert(LocalName::Named(param.x.name.clone()), param.span.clone());
        }
        let scope = dc.scopes.last_mut().unwrap();
        scope.vars = vars;
        scope.site = Some(body.span.clone());
    }

    for param in params.iter() {
        builder.scope_insert(&param.x.name);
        if param.x.mode != Mode::Spec {
            let local = FlattenedPlaceTyped {
                local: LocalName::Named(param.x.name.clone()),
                typ: param.x.typ.clone(),
                projections: vec![],
            };
            let local_place = builder.locals.add_place(&local);
            builder.push_instruction_raw(
                start_bb,
                AstPosition::Before(body.span.id),
                InstructionKind::Overwrite(local_place),
            );
        }
    }

    let end_bb = builder.build(body, start_bb);
    if let (Maybe::Some(end_bb), true) = (&end_bb, builder.counting_drops()) {
        let end_bb = *end_bb;
        if !matches!(&body.x, ExprX::Block(..)) {
            // (a body that is a block drops them at its end, see ExprX::Block)
            builder.drop_scopes_and_temps(end_bb, AstPosition::After(body.span.id), 0, 0, true);
        }
    }
    builder.optionally_exit(end_bb);

    builder.pop_scope();
    builder.pop_fn();
    assert!(builder.fns.len() == 0);

    builder.compute_predecessors();

    if builder.errors.len() > 0 {
        return Err(builder.errors[0].clone());
    }

    let cfg = CFG { basic_blocks: builder.basic_blocks, locals: builder.locals };
    Ok((
        cfg,
        builder.assigns_to_resolve,
        builder.typ_inv_obligations,
        builder.asserts,
        builder.loops_with_no_back_edges,
        builder.drop_counting,
    ))
}

macro_rules! unwrap {
    ($e:expr) => {
        match $e {
            Maybe::Some(e) => e,
            Maybe::Never => {
                return Maybe::Never;
            }
        }
    };
}

impl<'a> Builder<'a> {
    fn compute_predecessors(&mut self) {
        for bb1 in 0..self.basic_blocks.len() {
            for j in 0..self.basic_blocks[bb1].successors.len() {
                let bb2 = self.basic_blocks[bb1].successors[j];
                self.basic_blocks[bb2].predecessors.push(bb1);
            }
        }
    }

    /// Initialize a new empty basic block
    fn new_bb(
        &mut self,
        start_position: AstPosition,
        always_add_resolution_at_start: bool,
    ) -> BBIndex {
        self.basic_blocks.push(BasicBlock {
            instructions: vec![],
            predecessors: vec![],
            successors: vec![],
            is_entry: false,
            is_exit: false,
            always_add_resolution_at_start,
            position_of_start: start_position,
        });
        self.basic_blocks.len() - 1
    }

    fn optionally_exit(&mut self, bb: Maybe<BBIndex>) {
        match bb {
            Maybe::Some(bb) => {
                self.basic_blocks[bb].is_exit = true;
            }
            _ => {}
        }
    }

    fn optionally_push_successor(&mut self, bb: Maybe<BBIndex>, successor: BBIndex) {
        match bb {
            Maybe::Some(bb) => {
                self.basic_blocks[bb].successors.push(successor);
            }
            _ => {}
        }
    }

    /// Push the instruction and update the recorded upvars if necessary
    fn push_instruction_propagate(
        &mut self,
        bb: BBIndex,
        post_instruction_position: AstPosition,
        instr: InstructionKind,
    ) {
        match &instr {
            InstructionKind::Overwrite(fp) | InstructionKind::Mutate(fp) => {
                if self.place_is_upvar(fp) {
                    self.fns.last_mut().unwrap().upvars_mutated.push(fp.clone());
                }
            }
            InstructionKind::MoveFrom(fp) => {
                if self.place_is_upvar(fp) {
                    self.fns.last_mut().unwrap().upvars_moved.push(fp.clone());
                }
            }
            InstructionKind::DropFrom(_) | InstructionKind::ChargedDrop(_) => {}
        }
        self.push_instruction_raw(bb, post_instruction_position, instr);
    }

    /// Just push the instruction
    /// Usually use `push_instruction_propagate` instead of this; only use raw at
    /// function/closure boundaries.
    fn push_instruction_raw(
        &mut self,
        bb: BBIndex,
        post_instruction_position: AstPosition,
        instr: InstructionKind,
    ) {
        self.basic_blocks[bb]
            .instructions
            .push(Instruction { kind: instr, post_instruction_position });
    }

    fn push_drops(
        &mut self,
        bb: BBIndex,
        post_instruction_position: AstPosition,
        drops: &[FlattenedPlace],
    ) {
        for fp in drops.iter() {
            self.push_instruction_propagate(
                bb,
                post_instruction_position,
                InstructionKind::DropFrom(fp.clone()),
            );
        }
    }

    fn get_loop<'b>(loops: &'b mut Vec<LoopEntry>, loop_label: &Label) -> &'b mut LoopEntry {
        for l in loops.iter_mut().rev() {
            if &l.label == loop_label {
                return l;
            }
        }
        panic!("Could not find label {:?}", loop_label);
    }

    /// Process the given expression for building the CFG. Return the basic block
    /// corresponds to the end of the expression's execution, or Maybe::Never if
    /// execution never reachs the end of the expression.
    fn build(&mut self, expr: &Expr, bb: BBIndex) -> Maybe<BBIndex> {
        let span_id = expr.span.id;
        let mut bb = bb;
        match &expr.x {
            ExprX::Const(_)
            | ExprX::Var(_)
            | ExprX::VarAt(..)
            | ExprX::ConstVar(..)
            | ExprX::StaticVar(_)
            | ExprX::Quant(..)
            | ExprX::Closure(..)
            | ExprX::ExecFnByName(..)
            | ExprX::Choose { .. }
            | ExprX::WithTriggers { .. }
            | ExprX::Fuel(..)
            | ExprX::RevealString(_)
            | ExprX::RevealByteString(_)
            | ExprX::Header(_)
            | ExprX::ProofInSpec(..)
            | ExprX::AirStmt(..)
            | ExprX::Old(..)
            | ExprX::Nondeterministic => Maybe::Some(bb),

            ExprX::AssertAssume { .. }
            | ExprX::AssertBy { .. }
            | ExprX::AssertQuery { .. }
            | ExprX::AssertCompute(..) => {
                let idx = self.basic_blocks[bb].instructions.len();
                self.asserts.push(((bb, idx), expr.clone()));
                Maybe::Some(bb)
            }

            ExprX::AssertAssumeUserDefinedTypeInvariant { is_assume: _, expr, fun: _ } => {
                bb = unwrap!(self.build(expr, bb));

                let idx = self.basic_blocks[bb].instructions.len();
                self.asserts.push(((bb, idx), expr.clone()));
                Maybe::Some(bb)
            }

            ExprX::Call { target: call_target, args: es, post_args, body } => {
                assert!(post_args.is_none());

                // Can skip the expression in CallTarget because
                // it can only be for FnSpec which is always a pure spec expression

                let mut two_phase_delayed_mutations = vec![];

                for e in es.iter() {
                    match &e.x {
                        ExprX::TwoPhaseBorrowMut(p) => {
                            let (p, bb1) = unwrap!(self.build_place_and_intern(p, bb, TypInv::Yes));
                            bb = bb1;
                            if let Some(p) = p.get_place_for_mutation() {
                                two_phase_delayed_mutations.push(p);
                            }
                        }
                        _ => {
                            bb = unwrap!(self.build(e, bb));
                        }
                    }
                }

                for p in two_phase_delayed_mutations.into_iter() {
                    // The point we mark here is after the arguments execute,
                    // but before the call executes.
                    self.push_instruction_propagate(
                        bb,
                        AstPosition::AfterArguments(span_id),
                        InstructionKind::Mutate(p),
                    );
                }

                if let Some(e) = body {
                    bb = unwrap!(self.build(e, bb));
                }

                if crate::ast_util::call_no_unwind(call_target, &self.locals.functions) {
                    Maybe::Some(bb)
                } else {
                    // Create an extra edge that ends immediately to represent unwinding
                    let unwind_bb = self.new_bb(AstPosition::OnUnwind(expr.span.id), false);
                    let main_bb = self.new_bb(AstPosition::After(expr.span.id), false);
                    self.basic_blocks[bb].successors.push(unwind_bb);
                    self.basic_blocks[bb].successors.push(main_bb);
                    self.basic_blocks[unwind_bb].is_exit = true;
                    Maybe::Some(main_bb)
                }
            }
            ExprX::Ctor(_dt, _id, binders, Some(CtorUpdateTail { place, taken_fields })) => {
                // CtorUpdateTail can only happen for braces-style ctor, so we don't need
                // to account for TwoPhaseBorrows. (If this ever changes we'll just get a panic
                // later about unhandled TwoPhaseBorrowMut node)

                for b in binders.iter() {
                    let e = &b.a;
                    bb = unwrap!(self.build(e, bb));
                }

                let (p, bb1) = unwrap!(self.build_place_typed(place, bb, TypInv::No));
                bb = bb1;

                for (field_name, unfinal_read_kind) in taken_fields.iter() {
                    if self.is_move(unfinal_read_kind) {
                        if !matches!(p, ComputedPlaceTyped::Exact(..)) {
                            self.emit_bad_move_err(&p, &place.span);
                            break;
                        }
                        if let Some(mut p) = p.clone().get_place_for_move() {
                            p.projections.push(ProjectionTyped::struct_field(
                                &place.typ,
                                field_name,
                                &self.locals.datatypes,
                            ));
                            let p = self.locals.add_place(&p);
                            self.push_instruction_propagate(
                                bb,
                                AstPosition::After(place.span.id),
                                InstructionKind::MoveFrom(p),
                            );
                        }
                    }
                }

                Maybe::Some(bb)
            }
            ExprX::Ctor(_dt, _id, binders, None) => {
                let mut two_phase_delayed_mutations = vec![];

                for b in binders.iter() {
                    let e = &b.a;
                    match &e.x {
                        ExprX::TwoPhaseBorrowMut(p) => {
                            let (p, bb1) = unwrap!(self.build_place_and_intern(p, bb, TypInv::Yes));
                            bb = bb1;
                            if let Some(p) = p.get_place_for_mutation() {
                                two_phase_delayed_mutations.push(p);
                            }
                        }
                        _ => {
                            bb = unwrap!(self.build(e, bb));
                        }
                    }
                }

                for p in two_phase_delayed_mutations.into_iter() {
                    // Conveniently, we can just put these mutations after the Ctor call itself
                    // since the Ctor is a trivial operation, i.e., we don't need a special
                    // place for the "post_args" like we do with calls.
                    self.push_instruction_propagate(
                        bb,
                        AstPosition::After(span_id),
                        InstructionKind::Mutate(p),
                    );
                }

                Maybe::Some(bb)
            }
            ExprX::Logical(_op, e1, e2) => {
                bb = unwrap!(self.build(e1, bb));

                let snd_block = self.new_bb(AstPosition::Before(e2.span.id), false);
                self.basic_blocks[bb].successors.push(snd_block);

                let snd_bb_end = self.build(e2, snd_block);

                let join_block = self.new_bb(AstPosition::After(span_id), false);
                self.basic_blocks[bb].successors.push(join_block);
                self.optionally_push_successor(snd_bb_end, join_block);
                Maybe::Some(join_block)
            }
            ExprX::If(cond, thn, els) => {
                // TODO(new_mut_ref): (completeness) if the condition has conditional short-circuiting,
                // we could make a more precise CFG. Is this needed to match Rustc's analysis?

                let thn_position = AstPosition::Before(thn.span.id);
                let els_position = match els {
                    Some(els) => AstPosition::Before(els.span.id),
                    None => AstPosition::AfterBool(cond.span.id, false),
                };
                let join_position = AstPosition::After(span_id);

                bb = unwrap!(self.build(cond, bb));

                let thn_block = self.new_bb(thn_position, false);
                let els_block = self.new_bb(els_position, false);
                self.basic_blocks[bb].successors.push(thn_block);
                self.basic_blocks[bb].successors.push(els_block);

                let thn_bb_end = self.build(thn, thn_block);

                let els_bb_end = match els {
                    Some(els) => self.build(els, els_block),
                    None => Maybe::Some(els_block),
                };

                if !thn_bb_end.is_never() || !els_bb_end.is_never() {
                    let join_block = self.new_bb(join_position, false);
                    self.optionally_push_successor(thn_bb_end, join_block);
                    self.optionally_push_successor(els_bb_end, join_block);
                    Maybe::Some(join_block)
                } else {
                    Maybe::Never
                }
            }
            ExprX::NullaryOpr(_) => Maybe::Some(bb),
            ExprX::Unary(_, e) | ExprX::UnaryOpr(_, e) => {
                bb = unwrap!(self.build(e, bb));
                Maybe::Some(bb)
            }
            ExprX::Binary(_, e1, e2) | ExprX::BinaryOpr(_, e1, e2) => {
                bb = unwrap!(self.build(e1, bb));
                bb = unwrap!(self.build(e2, bb));
                Maybe::Some(bb)
            }
            ExprX::Multi(_, es) => {
                for e in es.iter() {
                    bb = unwrap!(self.build(e, bb));
                }
                Maybe::Some(bb)
            }
            ExprX::NonSpecClosure {
                params,
                proof_fn_modes,
                body,
                requires: _,
                ensures: _,
                mask_spec: _,
                allocates: _,
                deallocations: _,
                fip: _,
                unwind_spec: _,
                ret: _,
                external_spec: _,
            } => {
                // Build the closure interior as a disconnected part of the CFG
                let fn_scope = self.build_closure(&expr.span, params, proof_fn_modes, body);
                if fn_scope.upvars_moved.is_empty() {
                    if let TypX::AnonymousClosure(_, _, _, id) =
                        &**undecorate_box_trk_shr_decorations(&expr.typ)
                    {
                        self.locals.no_drop_closures.insert(*id);
                    }
                }

                // Emit instructions in the parent function that correspond to the
                // construction of the closure.
                for fp in fn_scope.upvars_moved.into_iter() {
                    self.push_instruction_propagate(
                        bb,
                        AstPosition::After(expr.span.id),
                        InstructionKind::MoveFrom(fp),
                    );
                }

                Maybe::Some(bb)
            }
            ExprX::ArrayLiteral(es) => {
                for e in es.iter() {
                    bb = unwrap!(self.build(e, bb));
                }
                Maybe::Some(bb)
            }
            ExprX::Match(..) => self.build_match(expr, bb),
            ExprX::Loop {
                loop_isolation: _,
                allow_complex_invariants: _,
                // for-loops have already been de-sugared by this point, so they don't
                // need special handling
                is_for_loop: _,
                assume_termination: _,
                label,
                cond,
                body,
                invs: _,
                decrease: _,
                atomic_call: _,
                known_no_back_edge: _,
                source: _,
            } => {
                let outer_body_bb_pos = match cond {
                    Some(cond) => AstPosition::Before(cond.span.id),
                    None => AstPosition::Before(body.span.id),
                };

                let outer_body_bb = self.new_bb(outer_body_bb_pos, true);
                let post_bb = self.new_bb(AstPosition::After(expr.span.id), true);

                self.loops.push(LoopEntry {
                    label: label.clone(),
                    break_bb: post_bb,
                    continue_bb: outer_body_bb,
                    continue_taken: false,
                });
                if let Some(dc) = &mut self.drop_counting {
                    // (kept parallel to `loops`, also inside closures)
                    dc.loop_depths.push((dc.scopes.len(), dc.stmts.len()));
                }

                self.basic_blocks[bb].successors.push(outer_body_bb);

                let inner_body_bb = if let Some(cond) = cond {
                    // loop {
                    //   (outer body)
                    //   if cond {
                    //       (pre_break_bb)
                    //       break;
                    //   }
                    //   (inner body)
                    // }
                    //
                    // outer_body_bb -> {cond} -> cond_end_bb -[on true]-> inner_body_bb
                    //                             |
                    //                             ---[on false]-> pre_break_bb -> post_bb
                    //
                    // The reason for going through 'pre_break_bb' rather than going straight to
                    // post_bb is that we can put assumes in pre_break_bb that can be helpful
                    // to prove the invariants.

                    let cond_end_bb = self.build(cond, outer_body_bb);
                    let Maybe::Some(cond_end_bb) = cond_end_bb else {
                        self.loops.pop().unwrap();
                        if let Some(dc) = &mut self.drop_counting {
                            dc.loop_depths.pop().unwrap();
                        }
                        return Maybe::Some(post_bb);
                    };

                    let pre_break_bb =
                        self.new_bb(AstPosition::AfterBool(cond.span.id, false), false);
                    let inner_body_bb = self.new_bb(AstPosition::Before(body.span.id), false);

                    self.basic_blocks[cond_end_bb].successors.push(pre_break_bb);
                    self.basic_blocks[cond_end_bb].successors.push(inner_body_bb);

                    self.basic_blocks[pre_break_bb].successors.push(post_bb);

                    inner_body_bb
                } else {
                    outer_body_bb
                };

                let end_bb = self.build(body, inner_body_bb);

                let loop_entry = self.loops.pop().unwrap();
                if let Some(dc) = &mut self.drop_counting {
                    dc.loop_depths.pop().unwrap();
                }

                match end_bb {
                    Maybe::Never => {
                        if !loop_entry.continue_taken {
                            self.loops_with_no_back_edges.insert(expr.span.id);
                        }
                    }
                    Maybe::Some(end_bb) => {
                        self.basic_blocks[end_bb].successors.push(outer_body_bb);
                    }
                }

                Maybe::Some(post_bb)
            }
            ExprX::OpenInvariant(arg, binder, body, _)
            | ExprX::TryOpenAtomicUpdate(arg, binder, body) => {
                bb = unwrap!(self.build(arg, bb));

                let local = FlattenedPlaceTyped {
                    local: LocalName::Named(binder.name.clone()),
                    typ: binder.a.clone(),
                    projections: vec![],
                };
                let fp = self.locals.add_place(&local);

                self.push_scope();
                self.scope_insert(&binder.name);

                self.push_instruction_propagate(
                    bb,
                    AstPosition::Before(body.span.id),
                    InstructionKind::Overwrite(fp.clone()),
                );
                bb = match self.build(body, bb) {
                    Maybe::Some(bb) => bb,
                    Maybe::Never => {
                        self.pop_scope();
                        return Maybe::Never;
                    }
                };
                self.push_instruction_propagate(
                    bb,
                    AstPosition::After(body.span.id),
                    InstructionKind::MoveFrom(fp),
                );
                self.pop_scope();

                Maybe::Some(bb)
            }
            ExprX::AtomicUpdateInitDummy => Maybe::Some(bb),
            ExprX::Atomically(_k, _v, e) => {
                bb = unwrap!(self.build(e, bb));
                Maybe::Some(bb)
            }
            ExprX::Update(e) => {
                bb = unwrap!(self.build(e, bb));
                Maybe::Some(bb)
            }
            ExprX::InvMask(_m) => Maybe::Some(bb),
            ExprX::Return(e_opt) => {
                if let Some(e) = e_opt {
                    bb = unwrap!(self.build(e, bb));
                }
                // (a return leaves every scope and statement of the function)
                let position = match e_opt {
                    Some(e) => AstPosition::After(e.span.id),
                    None => AstPosition::Before(span_id),
                };
                self.drop_scopes_and_temps(bb, position, 0, 0, true);
                self.basic_blocks[bb].is_exit = true;
                Maybe::Never
            }
            ExprX::BreakOrContinue { label, is_break, value } => {
                if let Some(value) = value {
                    bb = unwrap!(self.build(value, bb));
                }
                if self.counting_drops() {
                    // (leaves the scopes and statements inside the loop)
                    let i = self.loops.iter().rposition(|l| &l.label == label).unwrap();
                    let (scopes_from, stmts_from) =
                        self.drop_counting.as_ref().unwrap().loop_depths[i];
                    let position = match value {
                        Some(e) => AstPosition::After(e.span.id),
                        None => AstPosition::Before(span_id),
                    };
                    self.drop_scopes_and_temps(bb, position, scopes_from, stmts_from, false);
                }
                let entry = Self::get_loop(&mut self.loops, label);
                if *is_break {
                    self.basic_blocks[bb].successors.push(entry.break_bb);
                } else {
                    self.basic_blocks[bb].successors.push(entry.continue_bb);
                    entry.continue_taken = true;
                }
                Maybe::Never
            }
            ExprX::Ghost { alloc_wrapper: _, tracked: _, expr } => {
                bb = unwrap!(self.build(expr, bb));
                Maybe::Some(bb)
            }
            ExprX::NeverToAny(e) => {
                let _ = unwrap!(self.build(e, bb));
                Maybe::Never
            }
            ExprX::Assign { place, rhs, op, resolve, typ: _, charge_drop } => {
                assert!(!resolve);
                assert!(!charge_drop);
                // Right-hand side first!
                let bb = unwrap!(self.build(rhs, bb));
                let (p, bb) = unwrap!(self.build_place_and_intern(place, bb, TypInv::Yes));
                match &p {
                    ComputedPlace::Partial(_) => {
                        if op.is_none() {
                            self.assigns_to_resolve.push(expr.span.id);
                        }
                    }
                    ComputedPlace::Exact(_) | ComputedPlace::Ghost(_) => {
                        // Exact: resolution handled by main part of the analysis
                        // Ghost: unsound to resolve because this place is ghost
                    }
                }
                if op.is_none() {
                    // (the old value is dropped after the right-hand side, before the write)
                    self.drop_for_assign(bb, span_id, place, &p);
                }
                match p {
                    ComputedPlace::Exact(p) => {
                        self.push_instruction_propagate(
                            bb,
                            AstPosition::After(span_id),
                            if op.is_some() {
                                InstructionKind::Mutate(p)
                            } else {
                                InstructionKind::Overwrite(p)
                            },
                        );
                    }
                    ComputedPlace::Partial(p) | ComputedPlace::Ghost(Some(p)) => {
                        self.push_instruction_propagate(
                            bb,
                            AstPosition::After(span_id),
                            InstructionKind::Mutate(p),
                        );
                    }
                    ComputedPlace::Ghost(None) => {}
                }
                Maybe::Some(bb)
            }
            ExprX::TwoPhaseBorrowMut(_p) => {
                // These must be handled contextually, so the recursion should skip over
                // these nodes.
                panic!("Verus Internal Error: unhandled TwoPhaseBorrowMut node");
            }
            ExprX::BorrowMut(p) | ExprX::BorrowMutTracked(p) => {
                let (p, bb) = unwrap!(self.build_place_and_intern(p, bb, TypInv::Yes));
                if let Some(p) = p.get_place_for_mutation() {
                    self.push_instruction_propagate(
                        bb,
                        AstPosition::After(span_id),
                        InstructionKind::Mutate(p),
                    );
                }
                Maybe::Some(bb)
            }
            ExprX::ReadPlace(place, unfinal_read_kind) => {
                let (p, bb) = unwrap!(self.build_place_typed(place, bb, TypInv::No));
                if self.is_move(unfinal_read_kind) {
                    if !matches!(p, ComputedPlaceTyped::Exact(..)) {
                        self.emit_bad_move_err(&p, &place.span);
                    }
                    if let Some(p) = p.get_place_for_move() {
                        let p = self.locals.add_place(&p);
                        self.push_instruction_propagate(
                            bb,
                            AstPosition::After(span_id),
                            InstructionKind::MoveFrom(p),
                        );
                    }
                    Maybe::Some(bb)
                } else {
                    Maybe::Some(bb)
                }
            }
            ExprX::Block(stmts, e_opt) => {
                let counting = self.counting_drops();
                let scopes_before =
                    self.drop_counting.as_ref().map(|dc| dc.scopes.len()).unwrap_or(0);
                if counting {
                    self.drop_counting.as_mut().unwrap().block_spans.push(expr.span.clone());
                }
                let mut scope_count = 0;
                for s in stmts.iter() {
                    if counting {
                        self.drop_counting.as_mut().unwrap().stmts.push((s.span.clone(), vec![]));
                    }
                    bb = match self.build_stmt(s, bb) {
                        Maybe::Some(bb) => bb,
                        Maybe::Never => {
                            for _i in 0..scope_count {
                                self.pop_scope();
                            }
                            if counting {
                                let dc = self.drop_counting.as_mut().unwrap();
                                dc.stmts.pop().unwrap();
                                dc.block_spans.pop().unwrap();
                            }
                            return Maybe::Never;
                        }
                    };
                    if counting {
                        // (the statement's temporaries are dropped at its end)
                        let n = self.drop_counting.as_ref().unwrap().stmts.len();
                        let n_scopes = self.drop_counting.as_ref().unwrap().scopes.len();
                        let position = AstPosition::After(s.span.id);
                        self.drop_scopes_and_temps(bb, position, n_scopes, n - 1, false);
                        self.drop_counting.as_mut().unwrap().stmts.pop().unwrap();
                    }

                    if let StmtX::Decl { .. } = &s.x {
                        scope_count += 1;
                    }
                }
                if let Some(e) = e_opt {
                    bb = match self.build(e, bb) {
                        Maybe::Some(bb) => bb,
                        Maybe::Never => {
                            for _i in 0..scope_count {
                                self.pop_scope();
                            }
                            if counting {
                                self.drop_counting.as_mut().unwrap().block_spans.pop().unwrap();
                            }
                            return Maybe::Never;
                        }
                    };
                }
                if counting {
                    // The block's `let` bindings (and, for the body, the parameters and the
                    // temporaries outside of statements) are dropped at its end
                    let is_body = self.drop_counting.as_ref().unwrap().body_id == span_id;
                    let position = if let Some(e) = e_opt {
                        AstPosition::After(e.span.id)
                    } else if let Some(s) = stmts.last() {
                        AstPosition::After(s.span.id)
                    } else {
                        AstPosition::Before(span_id)
                    };
                    let n_stmts = self.drop_counting.as_ref().unwrap().stmts.len();
                    let scopes_from = if is_body { 0 } else { scopes_before };
                    self.drop_scopes_and_temps(bb, position, scopes_from, n_stmts, is_body);
                    self.drop_counting.as_mut().unwrap().block_spans.pop().unwrap();
                }
                for _i in 0..scope_count {
                    self.pop_scope();
                }
                Maybe::Some(bb)
            }
            ExprX::EvalAndResolve(..) => {
                panic!("EvalAndResolve shouldn't be created yet");
            }
            ExprX::ChargeDeallocations(..) => {
                panic!("ChargeDeallocations shouldn't be created yet");
            }
            ExprX::MatchGuardFreeze(..) => {
                panic!("MatchGuardFreeze shouldn't be created yet");
            }
            ExprX::ImplicitReborrowOrSpecRead(..) => {
                panic!("ImplicitReborrowOrSpecRead should have been removed");
            }
            ExprX::Await(e) => {
                bb = unwrap!(self.build(e, bb));
                let cancel_bb = self.new_bb(AstPosition::OnUnwind(expr.span.id), false);
                let main_bb = self.new_bb(AstPosition::After(expr.span.id), false);
                self.basic_blocks[bb].successors.push(cancel_bb);
                self.basic_blocks[bb].successors.push(main_bb);
                self.basic_blocks[cancel_bb].is_exit = true;
                Maybe::Some(main_bb)
            }
            ExprX::ShrRefStructWrap(e1, e2, _t1, _t2, _variant, _ident) => {
                bb = unwrap!(self.build(e1, bb));
                bb = unwrap!(self.build(e2, bb));
                Maybe::Some(bb)
            }
        }
    }

    fn build_stmt(&mut self, stmt: &Stmt, bb: BBIndex) -> Maybe<BBIndex> {
        match &stmt.x {
            StmtX::Expr(e) => self.build(e, bb),
            StmtX::Decl { pattern, mode: _, init: None, els: None, assert_irrefutable: _ } => {
                self.push_scope();
                self.scope_insert_pattern(pattern);
                if let Some(site) = self.drop_counting.as_ref().and_then(|dc| dc.block_spans.last())
                {
                    let site = site.clone();
                    self.set_drop_scope_pattern(pattern, &site);
                }

                // If declaring a variable without initializing it, then we "drop" it.
                // This probably isn't really necessary, but it
                // makes it easy to confirm that the usage of a variable in one loop
                // can't be confused with its value in the next iteration of the loop.
                if self.loops.len() > 0 {
                    let fps = self.pattern_flattened_places(pattern);
                    self.push_drops(bb, AstPosition::After(stmt.span.id), &fps);
                }

                Maybe::Some(bb)
            }
            StmtX::Decl { pattern, mode: _, init: Some(init), els, assert_irrefutable: _ } => {
                check_illegal_muts(pattern, &self.locals.datatypes, &mut self.errors);
                let tinv = if pattern_has_mut(pattern) { TypInv::PatternError } else { TypInv::No };
                let (cpt, bb) = unwrap!(self.build_place_typed(init, bb, tinv));

                let next_bb = match els {
                    Some(els) => {
                        let els_bb = self.new_bb(AstPosition::Before(els.span.id), false);
                        let next_bb = self.new_bb(AstPosition::After(stmt.span.id), false);
                        self.basic_blocks[bb].successors.push(els_bb);
                        self.basic_blocks[bb].successors.push(next_bb);
                        match self.build(els, els_bb) {
                            Maybe::Some(_) | Maybe::Never => {}
                        }
                        next_bb
                    }
                    None => bb,
                };

                self.append_instructions_for_pattern_moves_mutations(
                    pattern,
                    &cpt,
                    next_bb,
                    AstPosition::After(stmt.span.id),
                );

                self.push_scope();
                self.scope_insert_pattern(pattern);
                if let Some(site) = self.drop_counting.as_ref().and_then(|dc| dc.block_spans.last())
                {
                    let site = site.clone();
                    self.set_drop_scope_pattern(pattern, &site);
                }

                for bound_var in
                    pattern_all_bound_vars_with_ownership(pattern, &self.locals.var_modes)
                        .into_iter()
                {
                    let fpt = FlattenedPlaceTyped {
                        local: LocalName::Named(bound_var.name),
                        typ: bound_var.typ,
                        projections: vec![],
                    };
                    let fp = self.locals.add_place(&fpt);
                    self.push_instruction_propagate(
                        next_bb,
                        AstPosition::After(stmt.span.id),
                        InstructionKind::Overwrite(fp),
                    );
                }
                Maybe::Some(next_bb)
            }
            StmtX::Decl { pattern: _, mode: _, init: None, els: Some(_), .. } => {
                panic!("Unexpected let-else without an initializer");
            }
        }
    }

    fn build_place_and_intern(
        &mut self,
        place: &Place,
        bb: BBIndex,
        typ_invs: TypInv,
    ) -> Maybe<(ComputedPlace, BBIndex)> {
        let r = self.build_place_typed(place, bb, typ_invs);
        match r {
            Maybe::Some((p, bb)) => {
                let sp = self.locals.add_computed_place(p);
                Maybe::Some((sp, bb))
            }
            Maybe::Never => Maybe::Never,
        }
    }

    fn build_place_typed(
        &mut self,
        place: &Place,
        bb: BBIndex,
        typ_invs: TypInv,
    ) -> Maybe<(ComputedPlaceTyped, BBIndex)> {
        match &place.x {
            PlaceX::Field(field_opr, p) => {
                let (inner, bb) = unwrap!(self.build_place_typed(p, bb, typ_invs));
                if typ_invs != TypInv::No {
                    match &inner {
                        ComputedPlaceTyped::Exact(_) | ComputedPlaceTyped::Partial(_) => {
                            if let Some(typ_inv_fun) = self.get_typ_inv_fun(p) {
                                match typ_invs {
                                    TypInv::Yes => {
                                        self.typ_inv_obligations.push((p.span.id, typ_inv_fun));
                                    }
                                    TypInv::PatternError => {
                                        self.errors.push(error(&p.span, "Verus does not currently support using a pattern to take a mutable reference to a field of a datatype that has a declared type invariant"));
                                    }
                                    TypInv::No => unreachable!(),
                                }
                            }
                        }
                        ComputedPlaceTyped::Ghost(_) => {}
                    }
                }
                match inner {
                    ComputedPlaceTyped::Exact(mut fpt) => {
                        let (mode, dtor) = field_opr_to_mode(field_opr, &self.locals.datatypes);
                        if mode == Mode::Spec {
                            Maybe::Some((ComputedPlaceTyped::Ghost(Some(fpt)), bb))
                        } else if dtor {
                            Maybe::Some((ComputedPlaceTyped::Partial(fpt), bb))
                        } else {
                            fpt.projections.push(ProjectionTyped::StructField(
                                FieldOpr { check: VariantCheck::None, ..field_opr.clone() },
                                place.typ.clone(),
                            ));
                            Maybe::Some((ComputedPlaceTyped::Exact(fpt), bb))
                        }
                    }
                    ComputedPlaceTyped::Partial(fpt) => {
                        let (mode, _dtor) = field_opr_to_mode(field_opr, &self.locals.datatypes);
                        if mode == Mode::Spec {
                            Maybe::Some((ComputedPlaceTyped::Ghost(Some(fpt)), bb))
                        } else {
                            Maybe::Some((ComputedPlaceTyped::Partial(fpt), bb))
                        }
                    }
                    ComputedPlaceTyped::Ghost(opt_fpt) => {
                        Maybe::Some((ComputedPlaceTyped::Ghost(opt_fpt), bb))
                    }
                }
            }
            PlaceX::DerefMut(p) => {
                let (inner, bb) = unwrap!(self.build_place_typed(p, bb, typ_invs));
                match inner {
                    ComputedPlaceTyped::Exact(mut fpt) => {
                        fpt.projections.push(ProjectionTyped::DerefMut(place.typ.clone()));
                        Maybe::Some((ComputedPlaceTyped::Exact(fpt), bb))
                    }
                    ComputedPlaceTyped::Partial(fpt) => {
                        Maybe::Some((ComputedPlaceTyped::Partial(fpt), bb))
                    }
                    ComputedPlaceTyped::Ghost(opt_fpt) => {
                        Maybe::Some((ComputedPlaceTyped::Ghost(opt_fpt), bb))
                    }
                }
            }
            PlaceX::Local(var) => {
                let Some(mode) = self.locals.var_modes.get(var) else {
                    panic!("unkown mode for var {var:?}")
                };

                if *mode == Mode::Spec {
                    Maybe::Some((ComputedPlaceTyped::Ghost(None), bb))
                } else {
                    let fpt = FlattenedPlaceTyped {
                        local: LocalName::Named(var.clone()),
                        typ: place.typ.clone(),
                        projections: vec![],
                    };
                    Maybe::Some((ComputedPlaceTyped::Exact(fpt), bb))
                }
            }
            PlaceX::Temporary(e) => {
                let bb = unwrap!(self.build(e, bb));
                let Some(mode) = self.locals.temporary_modes.get(&place.span.id) else {
                    panic!("unknown mode for temporary place {:?}", place);
                };

                if *mode == Mode::Spec {
                    Maybe::Some((ComputedPlaceTyped::Ghost(None), bb))
                } else {
                    let temp_name = self.locals.new_temp_name(place.span.id);

                    let fpt = FlattenedPlaceTyped {
                        local: temp_name.clone(),
                        typ: place.typ.clone(),
                        projections: vec![],
                    };
                    let fp = self.locals.add_place(&fpt);
                    if *mode == Mode::Exec && self.counting_drops() {
                        // (dropped at the end of its statement)
                        let dc = self.drop_counting.as_mut().unwrap();
                        dc.local_spans.insert(temp_name, place.span.clone());
                        match dc.stmts.last_mut() {
                            Some((_, temps)) => temps.push(fp.local),
                            None => dc.body_temps.push(fp.local),
                        }
                    }
                    self.push_instruction_propagate(
                        bb,
                        AstPosition::AfterTempAssignment(place.span.id),
                        InstructionKind::Overwrite(fp),
                    );

                    Maybe::Some((ComputedPlaceTyped::Exact(fpt), bb))
                }
            }
            PlaceX::ModeUnwrap(p, ModeWrapperMode::Proof) => {
                // As usual we just ignore Tracked (kinda like Box)
                self.build_place_typed(p, bb, typ_invs)
            }
            PlaceX::ModeUnwrap(p, ModeWrapperMode::Spec) => {
                let (cpt, bb) = unwrap!(self.build_place_typed(p, bb, typ_invs));
                Maybe::Some((cpt.to_ghost(), bb))
            }
            PlaceX::WithExpr(..) => {
                panic!("Verus Internal Error: unexpected PlaceX::WithExpr");
            }
            PlaceX::UserDefinedTypInvariantObligation(..) => {
                panic!(
                    "Verus Internal Error: unexpected PlaceX::UserDefinedTypInvariantObligation"
                );
            }
            PlaceX::Index(p, idx, _kind, _needs_bounds_check) => {
                let (cpt, bb) = unwrap!(self.build_place_typed(p, bb, typ_invs));
                let bb = unwrap!(self.build(idx, bb));
                Maybe::Some((cpt.to_partial(), bb))
            }
        }
    }

    fn is_move(&self, unfinal_read_kind: &UnfinalizedReadKind) -> bool {
        match &unfinal_read_kind.preliminary_kind {
            ReadKind::Move => {
                matches!(self.read_kind_finals[&unfinal_read_kind.id], ReadKind::Move)
            }
            _ => false,
        }
    }

    /// Get the local vars from this pattern that should be dropped
    fn pattern_flattened_places(&mut self, pat: &Pattern) -> Vec<FlattenedPlace> {
        pattern_all_bound_vars_with_ownership(pat, &self.locals.var_modes)
            .iter()
            .map(|bv| {
                let fpt = FlattenedPlaceTyped {
                    local: LocalName::Named(bv.name.clone()),
                    typ: bv.typ.clone(),
                    projections: vec![],
                };
                self.locals.add_place(&fpt)
            })
            .collect()
    }

    fn append_instructions_for_pattern_moves_mutations(
        &mut self,
        pattern: &Pattern,
        cpt: &ComputedPlaceTyped,
        bb: BBIndex,
        position: AstPosition,
    ) {
        match cpt {
            ComputedPlaceTyped::Exact(fpt) => {
                let places =
                    self.moves_and_muts_for_place_being_matched_intern_and_sort(pattern, &fpt);
                for (fp, by_ref) in places.into_iter() {
                    self.push_instruction_propagate(
                        bb,
                        position,
                        match by_ref {
                            ByRef::No => InstructionKind::MoveFrom(fp),
                            ByRef::MutRef => InstructionKind::Mutate(fp),
                            ByRef::ImmutRef => unreachable!(),
                        },
                    );
                }
            }
            ComputedPlaceTyped::Partial(fpt) | ComputedPlaceTyped::Ghost(Some(fpt)) => {
                if pattern_has_mut(pattern) {
                    let fp = self.locals.add_place(fpt);
                    self.push_instruction_propagate(bb, position, InstructionKind::Mutate(fp));
                }
            }
            ComputedPlaceTyped::Ghost(None) => {
                if pattern_has_mut(pattern) {
                    // Mode-checking should disallow mutable references to ghost places
                    panic!("Verus Internal Error: mut refs found when matchee is ghost");
                }
            }
        }
    }

    /// When a place is matched against a pattern, it induces some moves,
    /// e.g.:
    ///
    /// ```
    /// let (x, _) = y;   // moves y.0
    /// let (x, _) = y.1; // moves y.1.0
    /// ```
    ///
    /// It may also induce mutations due to variables with MutRef binding mode.
    /// This function calculates all such moves and mutations.
    ///
    /// TODO(new_mut_ref): (completeness) when or-patterns are involved,
    /// moves may be over-approximated
    ///
    /// Note: We don't have to worry about or-patterns together with mutations, as we currently
    /// don't support this combination (see check in well_formed.rs)
    fn moves_and_muts_for_place_being_matched_intern_and_sort(
        &mut self,
        pattern: &Pattern,
        fpt: &FlattenedPlaceTyped,
    ) -> Vec<(FlattenedPlace, ByRef)> {
        let places = self.moves_and_muts_for_place_being_matched(pattern, fpt);
        let mut v = vec![];
        for (fpt, by_ref) in places.into_iter() {
            v.push((self.locals.add_place(&fpt), by_ref));
        }

        // If there was an or-pattern, we need to sort out any redundancies
        let has_or = crate::patterns::pattern_has_or(pattern);
        if has_or {
            let v = v
                .into_iter()
                .map(|(fp, by_ref)| {
                    assert!(by_ref == ByRef::No);
                    fp
                })
                .collect::<Vec<_>>();
            let v = sort_and_remove_redundant(v);
            v.into_iter().map(|fp| (fp, ByRef::No)).collect::<Vec<_>>()
        } else {
            v
        }
    }

    /// Get all moves and mutations for the given pattern, using `ByRef::No` for moves
    /// and `ByRef::MutRef` for mutations.
    ///
    /// Example:
    ///
    /// ```
    /// let (a, _, ref mut b) = x.1;
    /// ```
    ///
    /// Returns `[(x.1.0, ByRef::No), (x.1.2, ByRef::MutRef)]` if `x.1.0` is a non-Copy type.
    /// Otherwise just returns `[(x.1.2, ByRef::MutRef)]`.
    fn moves_and_muts_for_place_being_matched(
        &mut self,
        pattern: &Pattern,
        fpt: &FlattenedPlaceTyped,
    ) -> Vec<(FlattenedPlaceTyped, ByRef)> {
        let projs = moves_and_muts_for_pattern(
            pattern,
            &self.locals.datatypes,
            &self.locals.var_modes,
            &mut self.errors,
        );
        projs
            .into_iter()
            .map(|(mut projs, by_ref)| {
                let mut f = fpt.clone();
                f.projections.append(&mut projs);
                (f, by_ref)
            })
            .collect()
    }

    //// Match

    fn build_match(&mut self, expr: &Expr, bb: BBIndex) -> Maybe<BBIndex> {
        // TODO(new_mut_ref): (blocking) need more tests for guards
        // TODO(new_mut_ref): (blocking) need more tests for or-patterns

        let ExprX::Match(place, arms, _assert_irrefutable) = &expr.x else {
            unreachable!();
        };

        for arm in arms.iter() {
            check_illegal_muts(&arm.x.pattern, &self.locals.datatypes, &mut self.errors);
        }
        let tinv = if arms.iter().any(|arm| pattern_has_mut(&arm.x.pattern)) {
            TypInv::PatternError
        } else {
            TypInv::No
        };
        let (cpt, bb) = unwrap!(self.build_place_typed(place, bb, tinv));

        if arms.len() == 0 {
            return Maybe::Never;
        }

        let mut cur_bb = bb;
        let mut arm_bb_ends = vec![];

        for (i, arm) in arms.iter().enumerate() {
            // We treat the last arm as irrefutable. In principle, an irrefutable arm
            // could come earlier, but this would be a warning from Rust so it's probably
            // not worth optimizing that case.
            //
            // In the unlikely event that the final arm has a match guard,
            // then it must be the case that a prior arm was irrefutable, so it doesn't
            // really matter what we do.
            let is_irrefut = i == arms.len() - 1;

            if is_irrefut {
                let arm_bb = self.new_bb(AstPosition::Before(arm.x.body.span.id), false);
                self.basic_blocks[cur_bb].successors.push(arm_bb);
                let arm_bb_end = self.build_arm_after_checks(&cpt, arm, arm_bb);
                if let Maybe::Some(arm_bb_end) = arm_bb_end {
                    arm_bb_ends.push(arm_bb_end);
                }
                break;
            } else {
                let (continue_bb, arm_bb_end) = self.build_arm_before_checks(&cpt, arm, cur_bb);
                if let Maybe::Some(arm_bb_end) = arm_bb_end {
                    arm_bb_ends.push(arm_bb_end);
                }
                match continue_bb {
                    Maybe::Some(continue_bb) => {
                        let next_bb = self.new_bb(AstPosition::MatchIntermediate, false);
                        self.basic_blocks[continue_bb].successors.push(next_bb);
                        self.basic_blocks[cur_bb].successors.push(next_bb);
                        cur_bb = next_bb;
                    }
                    Maybe::Never => { /* leave cur_bb as it is */ }
                }
            }
        }

        if arm_bb_ends.len() > 0 {
            let join_position = AstPosition::After(expr.span.id);
            let join_block = self.new_bb(join_position, false);
            for arm_bb_end in arm_bb_ends {
                self.basic_blocks[arm_bb_end].successors.push(join_block);
            }
            Maybe::Some(join_block)
        } else {
            Maybe::Never
        }
    }

    /// Build the arm, starting from before any checks occur.
    /// Create a branch off of `cur_bb` to represent the pattern check passing;
    /// caller will handle failure and moving onto the next branch.
    ///
    /// Returns two BB positions:
    ///   - guard_fail_bb: After guard failure (when applicable)
    ///   - arm_end_bb: After arm completes
    fn build_arm_before_checks(
        &mut self,
        cpt: &ComputedPlaceTyped,
        arm: &Arm,
        cur_bb: BBIndex,
    ) -> (Maybe<BBIndex>, Maybe<BBIndex>) {
        if arm.x.has_guard() {
            // Note that because we currently disallow match guards together with or-patterns,
            // we don't have to worry about the match guard running more than once
            //
            //           pattern succeeds
            // cur_bb           --->        guard_bb --> (guard body) --> guard_success_bb
            //   |                                            |                   |
            //   |                                            |                   |
            //   |                                            |               (arm body)
            //   |                                            |                   |
            //   |                                            v                   v
            //   |                                      guard_fail_bb          arm_end_bb
            //   |                                            |
            //   |                                            |
            //   v                                            /
            // next_bb  <-------------------------------------

            let guard_bb = self.new_bb(AstPosition::Before(arm.x.guard.span.id), false);
            self.basic_blocks[cur_bb].successors.push(guard_bb);

            // Bound vars are immutable until the guard passes, so don't emit any instructions
            // for the bound variables yet
            self.push_scope();
            self.scope_insert_pattern(&arm.x.pattern);
            let guard_bb_end = self.build(&arm.x.guard, guard_bb);
            self.pop_scope();

            let guard_bb_end = match guard_bb_end {
                Maybe::Some(guard_bb_end) => guard_bb_end,
                Maybe::Never => {
                    return (Maybe::Never, Maybe::Never);
                }
            };

            let guard_fail_bb =
                self.new_bb(AstPosition::AfterBool(arm.x.guard.span.id, false), false);
            let guard_success_bb = self.new_bb(AstPosition::Before(arm.x.body.span.id), false);

            self.basic_blocks[guard_bb_end].successors.push(guard_fail_bb);
            self.basic_blocks[guard_bb_end].successors.push(guard_success_bb);

            let arm_end_bb = self.build_arm_after_checks(cpt, arm, guard_success_bb);
            (Maybe::Some(guard_fail_bb), arm_end_bb)
        } else {
            //           pattern succeeds
            // cur_bb           --->        arm_bb --> (arm body) --> arm_end_bb
            //   |
            //   |
            // (pattern fails)
            //   |
            //   v
            // (next branch)

            let arm_bb = self.new_bb(AstPosition::Before(arm.x.body.span.id), false);
            self.basic_blocks[cur_bb].successors.push(arm_bb);
            let arm_end_bb = self.build_arm_after_checks(cpt, arm, arm_bb);
            (Maybe::Never, arm_end_bb)
        }
    }

    /// Build the arm, starting immediately after all checks pass (i.e., after the pattern
    /// and pattern-guard pass). This performs moves, mutations, and initialization of bound vars
    fn build_arm_after_checks(
        &mut self,
        cpt: &ComputedPlaceTyped,
        arm: &Arm,
        arm_bb: BBIndex,
    ) -> Maybe<BBIndex> {
        self.append_instructions_for_pattern_moves_mutations(
            &arm.x.pattern,
            &cpt,
            arm_bb,
            AstPosition::Before(arm.x.body.span.id),
        );

        self.push_scope();
        self.scope_insert_pattern(&arm.x.pattern);
        self.set_drop_scope_pattern(&arm.x.pattern, &arm.span);

        for bound_var in
            pattern_all_bound_vars_with_ownership(&arm.x.pattern, &self.locals.var_modes)
                .into_iter()
        {
            let fpt = FlattenedPlaceTyped {
                local: LocalName::Named(bound_var.name),
                typ: bound_var.typ,
                projections: vec![],
            };
            let fp = self.locals.add_place(&fpt);
            self.push_instruction_propagate(
                arm_bb,
                AstPosition::Before(arm.x.body.span.id),
                InstructionKind::Overwrite(fp),
            );
        }

        let arm_bb_end = self.build(&arm.x.body, arm_bb);
        if let Maybe::Some(arm_bb_end) = arm_bb_end {
            if self.counting_drops() {
                let n = self.drop_counting.as_ref().unwrap().scopes.len();
                let stmts = self.drop_counting.as_ref().unwrap().stmts.len();
                let position = AstPosition::After(arm.x.body.span.id);
                self.drop_scopes_and_temps(arm_bb_end, position, n - 1, stmts, false);
            }
        }

        self.pop_scope();

        arm_bb_end
    }

    //// Closures

    fn build_closure(
        &mut self,
        span: &Span,
        params: &VarBinders<Typ>,
        proof_fn_modes: &Option<(Arc<Vec<Mode>>, Mode)>,
        body: &Expr,
    ) -> FnScope {
        let closure_prologue = self.new_bb(AstPosition::Before(body.span.id), true);
        self.basic_blocks[closure_prologue].is_entry = true;
        let closure_start_bb = self.new_bb(AstPosition::Before(body.span.id), false);

        self.push_fn();
        self.push_scope();

        for (i, param) in params.iter().enumerate() {
            self.scope_insert(&param.name);

            let mode = crate::ast_util::arg_mode_from_proof_fn_modes(proof_fn_modes, i);

            let f = self.locals.var_modes.insert(param.name.clone(), mode);
            assert!(f.is_none());

            if mode != Mode::Spec {
                let local = FlattenedPlaceTyped {
                    local: LocalName::Named(param.name.clone()),
                    typ: param.a.clone(),
                    projections: vec![],
                };
                let local_place = self.locals.add_place(&local);
                self.push_instruction_raw(
                    closure_prologue,
                    AstPosition::Before(body.span.id),
                    InstructionKind::Overwrite(local_place),
                );
            }
        }

        let closure_normal_ret_bb = self.build(body, closure_start_bb);
        self.optionally_exit(closure_normal_ret_bb);

        self.pop_scope();
        let mut fn_scope = self.pop_fn();

        if fn_scope.upvars_mutated.len() > 0 {
            let name = &self.locals.locals[fn_scope.upvars_mutated[0].local].name;
            let name = match name {
                LocalName::Named(var_ident) => crate::def::user_local_name(&var_ident),
                LocalName::Temporary(..) => "[Verus Internal Error: mutably captured temporary]",
            };
            self.errors.push(error(span,
                format!("Verus does not currently support closures capturing a mutable reference (mutably captured variable `{name}`)")));
        }

        fn_scope.upvars_moved = sort_and_remove_redundant(fn_scope.upvars_moved);
        for fp in fn_scope.upvars_moved.iter() {
            self.push_instruction_raw(
                closure_prologue,
                AstPosition::Before(body.span.id),
                InstructionKind::Overwrite(fp.clone()),
            );
        }
        self.basic_blocks[closure_prologue].successors.push(closure_start_bb);

        fn_scope
    }

    fn push_fn(&mut self) {
        self.fns.push(FnScope {
            scope_map: ScopeMap::new(),
            upvars_mutated: vec![],
            upvars_moved: vec![],
        });
    }

    fn pop_fn(&mut self) -> FnScope {
        let p = self.fns.pop().unwrap();
        assert_eq!(p.scope_map.num_scopes(), 0);
        p
    }

    fn push_scope(&mut self) {
        self.fns.last_mut().unwrap().scope_map.push_scope(false);
        if self.counting_drops() {
            let dc = self.drop_counting.as_mut().unwrap();
            dc.scopes.push(DropScope { vars: vec![], site: None });
        }
    }

    fn pop_scope(&mut self) {
        if self.counting_drops() {
            let dc = self.drop_counting.as_mut().unwrap();
            dc.scopes.pop().unwrap();
        }
        self.fns.last_mut().unwrap().scope_map.pop_scope();
    }

    //// -V alloc-check: drop counting (see DropCounting)

    /// Are we counting the drops here (in the function, not in a closure inside it)?
    fn counting_drops(&self) -> bool {
        self.drop_counting.is_some() && self.fns.len() == 1
    }

    /// The innermost scope binds the pattern's variables, which are dropped at the end of `site`
    fn set_drop_scope_pattern(&mut self, pattern: &Pattern, site: &Span) {
        if !self.counting_drops() {
            return;
        }
        let vars: Vec<VarIdent> =
            pattern_all_bound_vars_with_ownership(pattern, &self.locals.var_modes)
                .into_iter()
                .filter(|v| self.locals.var_modes.get(&v.name) == Some(&Mode::Exec))
                .map(|v| v.name)
                .collect();
        let mut spans = vec![];
        pattern_binding_spans(pattern, &mut spans);
        let dc = self.drop_counting.as_mut().unwrap();
        for (x, span) in spans.into_iter() {
            dc.local_spans.insert(LocalName::Named(x), span);
        }
        let scope = dc.scopes.last_mut().unwrap();
        scope.vars = vars;
        scope.site = Some(site.clone());
    }

    fn push_charged_drop(
        &mut self,
        bb: BBIndex,
        position: AstPosition,
        kind: DropKind,
        site: &Span,
    ) {
        let dc = self.drop_counting.as_mut().unwrap();
        let i = dc.drops.len();
        let loc = (bb, self.basic_blocks[bb].instructions.len());
        dc.drops.push(DropPoint { kind, site: site.clone(), loc, position });
        self.push_instruction_raw(bb, position, InstructionKind::ChargedDrop(i));
    }

    /// Drop (innermost first) the variables of the drop scopes from index `scopes_from` on, and
    /// the temporaries of the statements from index `stmts_from` on (and, if `body_temps`, the
    /// temporaries outside of statements)
    fn drop_scopes_and_temps(
        &mut self,
        bb: BBIndex,
        position: AstPosition,
        scopes_from: usize,
        stmts_from: usize,
        body_temps: bool,
    ) {
        if !self.counting_drops() {
            return;
        }
        let mut to_drop: Vec<(usize, Span)> = vec![];
        let dc = self.drop_counting.as_ref().unwrap();
        // (temporaries are dropped at the end of their statement, before the locals of the
        // enclosing scopes)
        for (span, temps) in dc.stmts[stmts_from..].iter().rev() {
            for t in temps.iter().rev() {
                to_drop.push((*t, span.clone()));
            }
        }
        if body_temps {
            for t in dc.body_temps.iter().rev() {
                to_drop.push((*t, dc.body_span.clone()));
            }
        }
        for scope in dc.scopes[scopes_from..].iter().rev() {
            for x in scope.vars.iter().rev() {
                if let Some(idx) = self.locals.ident_to_idx.get(&LocalName::Named(x.clone())) {
                    to_drop.push((*idx, scope.site.clone().expect("drop scope site")));
                }
            }
        }
        for (local, site) in to_drop.into_iter() {
            let fp = FlattenedPlace { local, projections: vec![] };
            self.push_charged_drop(bb, position, DropKind::ScopeEnd(fp), &site);
        }
    }

    /// The drops of an assignment `place = ..` (that is not to a ghost place)
    fn drop_for_assign(&mut self, bb: BBIndex, assign_id: AstId, place: &Place, p: &ComputedPlace) {
        if !self.counting_drops() {
            return;
        }
        let position = AstPosition::BeforeAssignWrite(assign_id);
        match p {
            ComputedPlace::Exact(fp)
                if fp.has_deref() || self.locals.locals[fp.local].name.is_temp() =>
            {
                // (behind a mutable reference, always initialized; or part of a temporary,
                // which is evaluated with the place, after the right-hand side)
                let kind = DropKind::AssignWhole(fp.clone());
                self.push_charged_drop(bb, position, kind, &place.span);
            }
            ComputedPlace::Exact(fp) => {
                let kind = DropKind::Assign(fp.clone());
                self.push_charged_drop(bb, position, kind, &place.span);
            }
            ComputedPlace::Partial(fp) => {
                let kind = DropKind::AssignUntracked(fp.clone());
                self.push_charged_drop(bb, position, kind, &place.span);
            }
            ComputedPlace::Ghost(_) => {}
        }
    }

    fn scope_insert(&mut self, id: &VarIdent) {
        self.fns.last_mut().unwrap().scope_map.insert(id.clone(), ()).unwrap();
    }

    fn scope_insert_pattern(&mut self, pattern: &Pattern) {
        match &pattern.x {
            PatternX::Wildcard | PatternX::Expr(_) | PatternX::Range(_, _) => {
                // nothing to do
            }
            PatternX::Var(binding) => {
                self.scope_insert(&binding.name);
            }
            PatternX::Binding { binding, sub_pat } => {
                self.scope_insert(&binding.name);
                self.scope_insert_pattern(sub_pat);
            }
            PatternX::Constructor(_dt, _variant, patterns) => {
                for p in patterns.iter() {
                    self.scope_insert_pattern(&p.a);
                }
            }
            PatternX::Or(sub_pat, _) | PatternX::ImmutRef(sub_pat) | PatternX::MutRef(sub_pat) => {
                self.scope_insert_pattern(sub_pat);
            }
            PatternX::Slice(patterns) => {
                for p in patterns.iter() {
                    self.scope_insert_pattern(p);
                }
            }
        }
    }

    fn place_is_upvar(&self, fp: &FlattenedPlace) -> bool {
        match &self.locals.locals[fp.local].name {
            LocalName::Named(var_ident) => {
                for i in (0..self.fns.len()).rev() {
                    if self.fns[i].scope_map.contains_key(var_ident) {
                        return i != self.fns.len() - 1;
                    }
                }
                panic!("Verus Internal Error: place_is_upvar failed to find var {var_ident:?}");
            }
            LocalName::Temporary(..) => false,
        }
    }

    //// User-defined type invariants

    fn get_typ_inv_fun(&mut self, p: &Place) -> Option<FunWithVis> {
        match &*undecorate_typ(&p.typ) {
            TypX::Datatype(dt, ..) => get_typ_inv_fun_dt(&self.locals.datatypes, dt),
            _ => {
                dbg!(&p.typ);
                self.errors
                    .push(crate::messages::internal_error(&p.span, "`get_typ_inv_fun` failed"));
                None
            }
        }
    }

    //// Errors

    /// Call this when you try to move from a place and the place isn't Exact.
    ///
    /// The Partial case can only happen if the user tries to move out of an array
    /// or slice. This is illegal, but lifetime checking hasn't run
    /// yet, so we have to handle it here.
    ///
    /// If we get the Ghost case, that's an internal error; that should have been ruled
    /// out by mode-checking.
    fn emit_bad_move_err(&mut self, p: &ComputedPlaceTyped, span: &Span) {
        match p {
            ComputedPlaceTyped::Partial(fpt) => {
                let t = typ_to_diagnostic_str(&undecorate_typ(&fpt.projected_typ()));
                self.errors.push(error(
                    span,
                    format!("cannot move out of type `{:}`, which is non-copy", t),
                ));
            }
            ComputedPlaceTyped::Ghost(_) => {
                self.errors.push(crate::messages::internal_error(
                    span,
                    "inconsistent state, move out of ghost place",
                ));
            }
            ComputedPlaceTyped::Exact(_) => unreachable!(),
        }
    }
}

fn get_typ_inv_fun_dt(datatypes: &HashMap<Path, Datatype>, dt: &Dt) -> Option<FunWithVis> {
    match dt {
        Dt::Path(path) => match &datatypes.get(path).unwrap().x.user_defined_invariant_fn {
            Some(vis_fun) => Some(vis_fun.clone()),
            None => None,
        },
        Dt::Tuple(_) => None,
    }
}

////// Patterns

pub struct BoundVar {
    pub name: VarIdent,
    pub typ: Typ,
}

/// Get all non-spec vars bound by the pattern.
pub fn pattern_all_bound_vars_with_ownership(
    pattern: &Pattern,
    modes: &HashMap<VarIdent, Mode>,
) -> Vec<BoundVar> {
    fn pattern_all_bound_vars_rec(
        pattern: &Pattern,
        out: &mut Vec<BoundVar>,
        modes: &HashMap<VarIdent, Mode>,
    ) {
        match &pattern.x {
            PatternX::Wildcard => {}
            PatternX::Var(PatternBinding { name, user_mut: _, by_ref: _, typ, copy: _ })
            | PatternX::Binding {
                binding: PatternBinding { name, user_mut: _, by_ref: _, typ, copy: _ },
                sub_pat: _,
            } => {
                let spec = matches!(&modes[name], Mode::Spec);
                if !spec {
                    out.push(BoundVar { name: name.clone(), typ: typ.clone() });
                }

                match &pattern.x {
                    PatternX::Binding { sub_pat, .. } => {
                        pattern_all_bound_vars_rec(sub_pat, out, modes);
                    }
                    _ => {}
                }
            }
            PatternX::Constructor(_dt, _variant, patterns) => {
                for binder in patterns.iter() {
                    pattern_all_bound_vars_rec(&binder.a, out, modes);
                }
            }
            PatternX::Or(pat1, _) | PatternX::ImmutRef(pat1) | PatternX::MutRef(pat1) => {
                pattern_all_bound_vars_rec(&pat1, out, modes);
            }
            PatternX::Expr(_) => {}
            PatternX::Range(_, _) => {}
            PatternX::Slice(patterns) => {
                for p in patterns.iter() {
                    pattern_all_bound_vars_rec(p, out, modes);
                }
            }
        }
    }

    let mut v = vec![];
    pattern_all_bound_vars_rec(pattern, &mut v, modes);
    v
}

/// See `moves_and_muts_for_place_being_matched`
fn moves_and_muts_for_pattern(
    pattern: &Pattern,
    datatypes: &HashMap<Path, Datatype>,
    modes: &HashMap<VarIdent, Mode>,
    errors: &mut Vec<VirErr>,
) -> Vec<(Vec<ProjectionTyped>, ByRef)> {
    fn moves_and_muts_for_pattern_rec(
        pattern: &Pattern,
        projs: &mut Vec<ProjectionTyped>,
        out: &mut Vec<(Vec<ProjectionTyped>, ByRef)>,
        datatypes: &HashMap<Path, Datatype>,
        modes: &HashMap<VarIdent, Mode>,
        errors: &mut Vec<VirErr>,
    ) {
        match &pattern.x {
            PatternX::Wildcard => {}
            PatternX::Var(PatternBinding { name, user_mut: _, by_ref, typ: _, copy })
            | PatternX::Binding {
                binding: PatternBinding { name, user_mut: _, by_ref, typ: _, copy },
                sub_pat: _,
            } => {
                // no need to descend into subpat, already moving or borrowing the whole thing
                if *by_ref != ByRef::ImmutRef && !*copy && !matches!(modes[name], Mode::Spec) {
                    out.push((projs.clone(), *by_ref));
                }
            }
            PatternX::Constructor(dt, variant, patterns) => {
                let has_dtor = match dt {
                    Dt::Tuple(_) => false,
                    Dt::Path(path) => datatypes[path].x.destructor,
                };

                if !has_dtor {
                    for binder in patterns.iter() {
                        let field_typ = binder.a.typ.clone();
                        let proj = ProjectionTyped::StructField(
                            FieldOpr {
                                datatype: dt.clone(),
                                variant: variant.clone(),
                                field: binder.name.clone(),
                                get_variant: false,
                                check: crate::ast::VariantCheck::None,
                            },
                            field_typ,
                        );

                        projs.push(proj);
                        moves_and_muts_for_pattern_rec(
                            &binder.a, projs, out, datatypes, modes, errors,
                        );
                        projs.pop();
                    }
                } else {
                    // For a struct with a destructor, it's not possible to take moves,
                    // only mut refs. We also need to handle this as a whole place in our analysis
                    // so we check if there are any mutations and then stop here.
                    if pattern_has_mut(pattern) {
                        out.push((projs.clone(), ByRef::MutRef));
                    }
                }
            }
            PatternX::Or(pat1, pat2) => {
                moves_and_muts_for_pattern_rec(&pat1, projs, out, datatypes, modes, errors);
                moves_and_muts_for_pattern_rec(&pat2, projs, out, datatypes, modes, errors);
            }
            PatternX::Expr(..) | PatternX::Range(..) => {}
            PatternX::ImmutRef(_) => {
                // can skip this, nothing can be moved or mutated from behind an immutable ref
            }
            PatternX::MutRef(sub_pat) => {
                let proj = ProjectionTyped::DerefMut(sub_pat.typ.clone());

                projs.push(proj);
                moves_and_muts_for_pattern_rec(sub_pat, projs, out, datatypes, modes, errors);
                projs.pop();
            }
            PatternX::Slice(sub_patterns) => {
                let (kind, elem_typ) = crate::ast_util::array_kind_of_typ(&pattern.typ);
                match kind {
                    ArrayKind::Array => {
                        for (i, sub_pat) in sub_patterns.iter().enumerate() {
                            let proj = ProjectionTyped::Index(i, elem_typ.clone());
                            projs.push(proj);
                            moves_and_muts_for_pattern_rec(
                                sub_pat, projs, out, datatypes, modes, errors,
                            );
                            projs.pop();
                        }
                    }
                    ArrayKind::Slice => {
                        // We can assume there are no moves out of a slice pattern
                        // TODO: would be good to sanity check anyway
                        if pattern_has_mut(pattern) {
                            out.push((projs.clone(), ByRef::MutRef));
                        }
                    }
                }
            }
        }
    }

    let mut out = vec![];
    moves_and_muts_for_pattern_rec(pattern, &mut vec![], &mut out, datatypes, modes, errors);
    out
}

/// Check for mutable borrows inside datatype structs
fn check_illegal_muts(
    pattern: &Pattern,
    datatypes: &HashMap<Path, Datatype>,
    errors: &mut Vec<VirErr>,
) {
    match &pattern.x {
        PatternX::Wildcard => {}
        PatternX::Var(_binding) => {}
        PatternX::Binding { binding: _, sub_pat } => check_illegal_muts(sub_pat, datatypes, errors),
        PatternX::Constructor(dt, _variant, patterns) => {
            if let Some(_typ_inv_fun) = get_typ_inv_fun_dt(datatypes, dt) {
                if let Some(span) = crate::patterns::pattern_find_mut_binding(pattern) {
                    errors.push(error(&pattern.span, "Verus does not currently support using a pattern to take a mutable reference to a field of a datatype that has a declared type invariant").secondary_label(&span, "`ref mut` binding here"));
                }
                // Can skip recursing; either we already added an error, or there are no
                // mutable bindings in this node.
                return;
            }

            for binder in patterns.iter() {
                check_illegal_muts(&binder.a, datatypes, errors);
            }
        }
        PatternX::Or(pat1, pat2) => {
            check_illegal_muts(pat1, datatypes, errors);
            check_illegal_muts(pat2, datatypes, errors);
        }
        PatternX::Expr(_e) => {}
        PatternX::Range(_lower, _upper) => {}
        PatternX::ImmutRef(p) | PatternX::MutRef(p) => check_illegal_muts(p, datatypes, errors),
        PatternX::Slice(pats) => {
            for p in pats.iter() {
                check_illegal_muts(p, datatypes, errors);
            }
        }
    }
}

////// Place trees

impl<'a> LocalCollection<'a> {
    fn new_temp_name(&mut self, ast_id: AstId) -> LocalName {
        let temp_id = TempId(self.next_temp_id);
        self.next_temp_id += 1;
        if let Some(prev) = self.ast_id_to_temp_id.get(&ast_id) {
            panic!("attempt to override entry AstId({ast_id}) => {prev:?} with {temp_id:?}");
        };

        self.ast_id_to_temp_id.insert(ast_id, temp_id);
        LocalName::Temporary(ast_id, temp_id)
    }

    fn add_computed_place(&mut self, p: ComputedPlaceTyped) -> ComputedPlace {
        match p {
            ComputedPlaceTyped::Exact(fpt) => {
                let sp = self.add_place(&fpt);
                ComputedPlace::Exact(sp)
            }
            ComputedPlaceTyped::Partial(fpt) => {
                let sp = self.add_place(&fpt);
                ComputedPlace::Partial(sp)
            }
            ComputedPlaceTyped::Ghost(Some(fpt)) => {
                let sp = self.add_place(&fpt);
                ComputedPlace::Ghost(Some(sp))
            }
            ComputedPlaceTyped::Ghost(None) => ComputedPlace::Ghost(None),
        }
    }

    /// Given a FlattenedPlaceTyped, we extend the tree if necessary so that it is deep enough
    /// to incorporate the given place. Returns a FlattenedPlace which indexes into the tree.
    fn add_place(&mut self, p: &FlattenedPlaceTyped) -> FlattenedPlace {
        if !self.ident_to_idx.contains_key(&p.local) {
            self.locals.push(Local { name: p.local.clone(), tree: PlaceTree::Leaf(p.typ.clone()) });
            self.ident_to_idx.insert(p.local.clone(), self.locals.len() - 1);
        }
        let idx = self.ident_to_idx[&p.local];

        let mut below_box = false;
        let projections = Self::extend_tree(
            &mut self.locals[idx].tree,
            &p.typ,
            &p.projections,
            &self.datatypes,
            &mut below_box,
        );
        if below_box {
            self.box_split.insert(idx);
        }

        FlattenedPlace { local: idx, projections: projections }
    }

    fn extend_tree(
        tree: &mut PlaceTree,
        root_typ: &Typ,
        projections: &[ProjectionTyped],
        datatypes: &HashMap<Path, Datatype>,
        below_box: &mut bool,
    ) -> Vec<Projection> {
        let mut tree: &mut PlaceTree = tree;
        let mut output_projections: Vec<Projection> = vec![];
        let mut cur_typ = root_typ.clone();
        for projection_typed in projections.iter() {
            if let PlaceTree::Leaf(_typ) = tree {
                // Note: the type off the PlaceTree::Leaf might not be head-normalized
                // (i.e., it might be a TypX::Projection instead of something concrete
                // like TypX::MutRef or TypX::Datatype).
                // (Note: TypX::Projection shouldn't be confused with the notion of
                // 'place projection' common in this file.)
                // Anyway, the `cur_typ` should be equivalent and should also be
                // head-normalized, so use that instead.
                //
                // We can skip over Box and Tracked modifiers.
                //
                // We also skip over shared reference modifiers.
                // These should not actually appear in well-formed code;
                // however, this will only be caught by lifetime-checking,
                // which hasn't run yet.
                // Thus, we just skip over them to avoid panicking.
                let typ = undecorate_box_trk_shr_decorations(&cur_typ);
                if typ_has_box_decoration(&cur_typ) {
                    *below_box = true;
                }

                match &**typ {
                    TypX::MutRef(inner_typ) => {
                        *tree = PlaceTree::MutRef(
                            typ.clone(),
                            Box::new(PlaceTree::Leaf(inner_typ.clone())),
                        );
                    }
                    TypX::Datatype(dt, typ_args, _) => match dt {
                        Dt::Tuple(n) => {
                            *tree = PlaceTree::Struct(
                                typ.clone(),
                                dt.clone(),
                                vec![
                                    (0..*n)
                                        .map(|i| Some(PlaceTree::Leaf(typ_args[i].clone())))
                                        .collect(),
                                ],
                            );
                        }
                        Dt::Path(path) => {
                            let datatype = &datatypes[path];

                            // Sanity check that we haven't been asked to split a datatype
                            // with a nontrivial destructor.
                            assert!(!datatype.x.destructor);

                            let fields = datatype
                                .x
                                .variants
                                .iter()
                                .map(|variant| {
                                    variant
                                        .fields
                                        .iter()
                                        .map(|f| {
                                            if f.a.1 == Mode::Spec {
                                                None
                                            } else {
                                                Some(PlaceTree::Leaf(subst_typ_for_datatype(
                                                    &datatype.x.typ_params,
                                                    typ_args,
                                                    &f.a.0,
                                                )))
                                            }
                                        })
                                        .collect::<Vec<Option<PlaceTree>>>()
                                })
                                .collect::<Vec<Vec<Option<PlaceTree>>>>();
                            *tree = PlaceTree::Struct(typ.clone(), dt.clone(), fields);
                        }
                    },
                    TypX::Primitive(Primitive::Array, typs) => {
                        assert!(typs.len() == 2);
                        let len: usize = match &*typs[1] {
                            TypX::ConstInt(n) => n.try_into().unwrap(),
                            _ => {
                                panic!("Verus internal error: expected array to have fixed length")
                            }
                        };
                        let children = std::iter::repeat_n(PlaceTree::Leaf(typs[0].clone()), len)
                            .collect::<Vec<PlaceTree>>();
                        *tree = PlaceTree::Array(typ.clone(), children);
                    }
                    _ => {
                        panic!("Verus internal error: unexpected type from projections")
                    }
                }
            }

            let projection = match projection_typed {
                ProjectionTyped::StructField(field_opr, _typ) => {
                    Projection::StructField(field_opr_to_indices(field_opr, datatypes))
                }
                ProjectionTyped::DerefMut(_typ) => Projection::DerefMut,
                ProjectionTyped::Index(idx, _typ) => Projection::Index(*idx),
            };
            output_projections.push(projection);

            match &projection {
                Projection::StructField((variant_idx, field_idx)) => match tree {
                    PlaceTree::Leaf(_) => unreachable!(),
                    PlaceTree::Struct(_, _, subtrees) => {
                        // If this unwrap fails, it means we are improperly trying to
                        // manipulate a ghost place
                        tree = subtrees[*variant_idx][*field_idx].as_mut().unwrap();
                    }
                    PlaceTree::MutRef(..) | PlaceTree::Array(..) => {
                        panic!(
                            "Verus internal error: extend_tree failed, conflicting projection type"
                        );
                    }
                },
                Projection::DerefMut => match tree {
                    PlaceTree::Leaf(_) => unreachable!(),
                    PlaceTree::Struct(..) | PlaceTree::Array(..) => {
                        panic!(
                            "Verus internal error: extend_tree failed, conflicting projection type"
                        );
                    }
                    PlaceTree::MutRef(_, inner) => {
                        tree = &mut *inner;
                    }
                },
                Projection::Index(idx) => match tree {
                    PlaceTree::Leaf(_) => unreachable!(),
                    PlaceTree::Array(_, subtrees) => {
                        tree = &mut subtrees[*idx];
                    }
                    PlaceTree::Struct(..) | PlaceTree::MutRef(..) => {
                        panic!(
                            "Verus internal error: extend_tree failed, conflicting projection type"
                        );
                    }
                },
            }

            cur_typ = projection_typed.typ();
        }
        output_projections
    }

    fn get_typ(&self, fp: &FlattenedPlace) -> Typ {
        let mut tree = &self.locals[fp.local].tree;
        for projection in fp.projections.iter() {
            match projection {
                Projection::StructField((variant_idx, field_idx)) => {
                    let (_dt, inner_trees) = match tree {
                        PlaceTree::Struct(_ty, dt, trees) => (dt, trees),
                        _ => unreachable!(),
                    };
                    let inner_tree = inner_trees[*variant_idx][*field_idx].as_ref().unwrap();
                    tree = inner_tree;
                }
                Projection::DerefMut => {
                    let inner_tree = match tree {
                        PlaceTree::MutRef(_ty, tr) => tr,
                        _ => unreachable!(),
                    };
                    tree = &inner_tree;
                }
                Projection::Index(idx) => {
                    let inner_trees = match tree {
                        PlaceTree::Array(_ty, inner_trees) => inner_trees,
                        _ => unreachable!(),
                    };
                    tree = &inner_trees[*idx];
                }
            }
        }
        tree.typ().clone()
    }

    /// Turn a FlattenedPlace back into a vir::ast::Place
    fn to_ast_place(&self, span: &Span, fp: &FlattenedPlace) -> Place {
        let mut ast_place = SpannedTyped::new(
            span,
            self.locals[fp.local].tree.typ(),
            PlaceX::Local(self.locals[fp.local].name.to_var_ident()),
        );
        let mut tree = &self.locals[fp.local].tree;
        for projection in fp.projections.iter() {
            match projection {
                Projection::StructField((variant_idx, field_idx)) => {
                    let (dt, inner_trees) = match tree {
                        PlaceTree::Struct(_ty, dt, trees) => (dt, trees),
                        _ => unreachable!(),
                    };
                    let inner_tree = inner_trees[*variant_idx][*field_idx].as_ref().unwrap();
                    let field_opr = match dt {
                        Dt::Tuple(n) => {
                            assert!(*variant_idx == 0);
                            crate::ast_util::mk_tuple_field_opr(*n, *field_idx)
                        }
                        Dt::Path(path) => {
                            let datatype = &self.datatypes[path];
                            let variant = &datatype.x.variants[*variant_idx];
                            FieldOpr {
                                datatype: dt.clone(),
                                variant: variant.name.clone(),
                                field: variant.fields[*field_idx].name.clone(),
                                get_variant: false,
                                check: crate::ast::VariantCheck::None,
                            }
                        }
                    };
                    ast_place = SpannedTyped::new(
                        span,
                        inner_tree.typ(),
                        PlaceX::Field(field_opr, ast_place),
                    );
                    tree = &inner_tree;
                }
                Projection::DerefMut => {
                    let inner_tree = match tree {
                        PlaceTree::MutRef(_ty, tr) => tr,
                        _ => unreachable!(),
                    };
                    ast_place =
                        SpannedTyped::new(span, inner_tree.typ(), PlaceX::DerefMut(ast_place));
                    tree = &inner_tree;
                }
                Projection::Index(idx) => {
                    let inner_trees = match tree {
                        PlaceTree::Array(_ty, inner_trees) => inner_trees,
                        _ => unreachable!(),
                    };
                    let inner_tree = &inner_trees[*idx];
                    ast_place = SpannedTyped::new(
                        span,
                        inner_tree.typ(),
                        PlaceX::Index(
                            ast_place,
                            mk_int_lit_from_usize(span, *idx),
                            ArrayKind::Array,
                            BoundsCheck::Allow,
                        ),
                    );
                    tree = inner_tree;
                }
            }
        }
        ast_place
    }

    fn places_skip_insides_of_mut_refs(&self) -> Vec<FlattenedPlace> {
        self.traverse_get_places(false)
    }

    fn places_including_insides_of_mut_refs(&self) -> Vec<FlattenedPlace> {
        self.traverse_get_places(true)
    }

    fn traverse_get_places(&self, go_inside_muts: bool) -> Vec<FlattenedPlace> {
        let mut v = vec![];
        for (i, local) in self.locals.iter().enumerate() {
            let mut sp = FlattenedPlace { local: i, projections: vec![] };
            Self::traverse_rec(&local.tree, &mut sp, &mut v, go_inside_muts);
        }
        v
    }

    fn traverse_rec(
        tree: &PlaceTree,
        cur: &mut FlattenedPlace,
        output: &mut Vec<FlattenedPlace>,
        go_inside_muts: bool,
    ) {
        match tree {
            PlaceTree::Leaf(_t) => {
                output.push(cur.clone());
            }
            PlaceTree::Struct(_t, _, children) => {
                for (v, variant_children) in children.iter().enumerate() {
                    for (f, child) in variant_children.iter().enumerate() {
                        if let Some(child) = child {
                            cur.projections.push(Projection::StructField((v, f)));
                            Self::traverse_rec(child, cur, output, go_inside_muts);
                            cur.projections.pop();
                        }
                    }
                }
            }
            PlaceTree::MutRef(_t, child) => {
                output.push(cur.clone());
                if go_inside_muts {
                    cur.projections.push(Projection::DerefMut);
                    Self::traverse_rec(child, cur, output, go_inside_muts);
                    cur.projections.pop();
                }
            }
            PlaceTree::Array(_t, children) => {
                for (i, child) in children.iter().enumerate() {
                    cur.projections.push(Projection::Index(i));
                    Self::traverse_rec(child, cur, output, go_inside_muts);
                    cur.projections.pop();
                }
            }
        }
    }

    fn try_get_flattened_place(&self, place: &Place) -> Option<FlattenedPlace> {
        self.try_get_flattened_place_rec(place).map(|m| m.0)
    }

    fn try_get_flattened_place_rec(
        &self,
        place: &Place,
    ) -> Option<(FlattenedPlace, Option<&PlaceTree>)> {
        match &place.x {
            PlaceX::Local(var) => match self.ident_to_idx.get(&LocalName::Named(var.clone())) {
                Some(idx) => {
                    let fp = FlattenedPlace { local: *idx, projections: vec![] };
                    let tree = &self.locals[*idx].tree;
                    Some((fp, Some(tree)))
                }
                None => None,
            },
            PlaceX::DerefMut(p) => {
                let m = self.try_get_flattened_place_rec(p);
                m.map(|(mut fp, tree)| match tree {
                    None => (fp, None),
                    Some(PlaceTree::Leaf(_)) => (fp, None),
                    Some(PlaceTree::Struct(..)) => {
                        panic!("Verus Internal Error: unexpected PlaceTree::Struct")
                    }
                    Some(PlaceTree::Array(..)) => {
                        panic!("Verus Internal Error: unexpected PlaceTree::Array")
                    }
                    Some(PlaceTree::MutRef(_, child)) => {
                        fp.projections.push(Projection::DerefMut);
                        let child: &PlaceTree = &child;
                        (fp, Some(child))
                    }
                })
            }
            PlaceX::Field(field_opr, p) => {
                let m = self.try_get_flattened_place_rec(p);
                m.map(|(mut fp, tree)| match tree {
                    None => (fp, None),
                    Some(PlaceTree::Leaf(_)) => (fp, None),
                    Some(PlaceTree::MutRef(..)) => {
                        panic!("Verus Internal Error: unexpected PlaceTree::MutRef")
                    }
                    Some(PlaceTree::Array(..)) => {
                        panic!("Verus Internal Error: unexpected PlaceTree::Array")
                    }
                    Some(PlaceTree::Struct(_, _, variants)) => {
                        let indices = field_opr_to_indices(field_opr, &self.datatypes);
                        fp.projections.push(Projection::StructField(indices));
                        let child: Option<&PlaceTree> = variants[indices.0][indices.1].as_ref();
                        (fp, child)
                    }
                })
            }
            PlaceX::Temporary(..) => None,
            PlaceX::ModeUnwrap(p, ModeWrapperMode::Proof) => self.try_get_flattened_place_rec(p),
            PlaceX::ModeUnwrap(_, ModeWrapperMode::Spec) => None,
            PlaceX::WithExpr(..) | PlaceX::UserDefinedTypInvariantObligation(..) => {
                panic!("Verus Internal Error: unexpected place");
            }
            PlaceX::Index(p, idx_expr, ..) => {
                let m = self.try_get_flattened_place_rec(p);
                m.map(|(mut fp, tree)| match tree {
                    None => (fp, None),
                    Some(PlaceTree::Leaf(_)) => (fp, None),
                    Some(PlaceTree::Struct(..)) => {
                        panic!("Verus Internal Error: unexpected PlaceTree::Struct")
                    }
                    Some(PlaceTree::MutRef(..)) => {
                        panic!("Verus Internal Error: unexpected PlaceTree::MutRef")
                    }
                    Some(PlaceTree::Array(_, children)) => {
                        match crate::ast_util::const_usize_of_expr(idx_expr) {
                            Some(i) if i < children.len() => {
                                fp.projections.push(Projection::Index(i));
                                let child: &PlaceTree = &children[i];
                                (fp, Some(child))
                            }
                            _ => (fp, None),
                        }
                    }
                })
            }
        }
    }
}

fn typ_has_box_decoration(t: &Typ) -> bool {
    match &**t {
        TypX::Decorate(TypDecoration::Box, _, _) => true,
        TypX::Decorate(TypDecoration::Tracked, _, t) | TypX::Decorate(TypDecoration::Ref, _, t) => {
            typ_has_box_decoration(t)
        }
        _ => false,
    }
}

fn undecorate_box_trk_shr_decorations(t: &Typ) -> &Typ {
    match &**t {
        TypX::Decorate(TypDecoration::Box, _, t)
        | TypX::Decorate(TypDecoration::Tracked, _, t)
        | TypX::Decorate(TypDecoration::Ref, _, t) => undecorate_box_trk_shr_decorations(t),
        _ => t,
    }
}

fn field_opr_to_indices(
    field_opr: &FieldOpr,
    datatypes: &HashMap<Path, Datatype>,
) -> (usize, usize) {
    match &field_opr.datatype {
        Dt::Tuple(n) => {
            let p = field_opr.field.parse::<usize>().unwrap();
            assert!(p < *n);
            (0, p)
        }
        Dt::Path(path) => {
            let datatype = &datatypes[path];
            let variant_idx =
                datatype.x.variants.iter().position(|v| v.name == field_opr.variant).unwrap();
            let variant = &datatype.x.variants[variant_idx];
            let field_idx = variant.fields.iter().position(|f| f.name == field_opr.field).unwrap();
            (variant_idx, field_idx)
        }
    }
}

/// Return:
///  - Mode: mode of the field,
///  - bool: does the datatype implement Drop?
fn field_opr_to_mode(field_opr: &FieldOpr, datatypes: &HashMap<Path, Datatype>) -> (Mode, bool) {
    match &field_opr.datatype {
        Dt::Tuple(_) => (Mode::Exec, false),
        Dt::Path(path) => {
            let datatype = &datatypes[path];
            let variant = crate::ast_util::get_variant(&datatype.x.variants, &field_opr.variant);
            let field = crate::ast_util::get_field(&variant.fields, &field_opr.field);
            let mode = field.a.1;
            (mode, datatype.x.destructor)
        }
    }
}

impl PlaceTree {
    fn typ(&self) -> &Typ {
        match self {
            PlaceTree::Leaf(t) => t,
            PlaceTree::Struct(t, _, _) => t,
            PlaceTree::MutRef(t, _) => t,
            PlaceTree::Array(t, _) => t,
        }
    }
}

impl FlattenedPlace {
    /// Do the 2 places intersect at all?
    fn intersects(&self, other: &Self) -> bool {
        if self.local == other.local {
            let m = std::cmp::min(self.projections.len(), other.projections.len());
            (0..m).all(|i| self.projections[i] == other.projections[i])
        } else {
            false
        }
    }

    /// Does the first place fully contain the second?
    /// e.g., x, x.f  -> yes
    ///       x, x    -> yes
    ///       x, *x   -> yes
    ///       x.f, x  -> no
    fn contains(&self, other: &Self) -> bool {
        self.local == other.local
            && self.projections.len() <= other.projections.len()
            && (0..self.projections.len()).all(|i| self.projections[i] == other.projections[i])
    }

    /// Does the first place fully contain the second but NOT via deref?
    /// e.g., x, x.f  -> yes
    ///       x, *x   -> no
    fn contains_and_not_separated_by_deref(&self, other: &Self) -> bool {
        self.contains(other)
            && (self.projections.len()..other.projections.len())
                .all(|i| !matches!(other.projections[i], Projection::DerefMut))
    }

    /// Does the place have a deref projection?
    fn has_deref(&self) -> bool {
        self.projections.iter().any(|p| matches!(p, Projection::DerefMut))
    }

    /// Can the spec-value of the given place be changed by the instruction?
    fn value_may_change(&self, instr: &Instruction) -> bool {
        match &instr.kind {
            InstructionKind::MoveFrom(_) => false,
            InstructionKind::Overwrite(sp) => self.intersects(sp),
            InstructionKind::Mutate(sp) => self.intersects(sp),
            InstructionKind::DropFrom(_) => false,
            InstructionKind::ChargedDrop(_) => false,
        }
    }

    fn truncate_to_deref(&self) -> FlattenedPlace {
        for i in 0..self.projections.len() {
            if matches!(self.projections[i], Projection::DerefMut) {
                return FlattenedPlace {
                    local: self.local,
                    projections: self.projections[0..i].into(),
                };
            }
        }
        return self.clone();
    }
}

impl ComputedPlace {
    fn get_place_for_mutation(self) -> Option<FlattenedPlace> {
        match self {
            ComputedPlace::Exact(p) => Some(p),
            ComputedPlace::Partial(p) => Some(p),
            ComputedPlace::Ghost(p) => {
                // When mutating a ghost place, we treat it as a mutation of whatever
                // "real" place contains it
                p
            }
        }
    }
}

impl ComputedPlaceTyped {
    fn to_ghost(self) -> ComputedPlaceTyped {
        match self {
            ComputedPlaceTyped::Exact(fpt) => ComputedPlaceTyped::Ghost(Some(fpt)),
            ComputedPlaceTyped::Partial(fpt) => ComputedPlaceTyped::Ghost(Some(fpt)),
            ComputedPlaceTyped::Ghost(opt_fpt) => ComputedPlaceTyped::Ghost(opt_fpt),
        }
    }

    fn to_partial(self) -> ComputedPlaceTyped {
        match self {
            ComputedPlaceTyped::Exact(fpt) => ComputedPlaceTyped::Partial(fpt),
            ComputedPlaceTyped::Partial(fpt) => ComputedPlaceTyped::Partial(fpt),
            ComputedPlaceTyped::Ghost(opt_fpt) => ComputedPlaceTyped::Ghost(opt_fpt),
        }
    }

    fn get_place_for_move(self) -> Option<FlattenedPlaceTyped> {
        match self {
            ComputedPlaceTyped::Exact(p) => Some(p),
            ComputedPlaceTyped::Partial(_) | ComputedPlaceTyped::Ghost(_) => {
                // reading out of a ghost field is NOT a move
                None
            }
        }
    }
}

impl ProjectionTyped {
    fn struct_field(
        dt_typ: &Typ,
        field_name: &Ident,
        datatypes: &HashMap<Path, Datatype>,
    ) -> ProjectionTyped {
        let typ = undecorate_typ(dt_typ);
        let (dt, typ_args) = match &*typ {
            TypX::Datatype(dt, typ_args, _) => (dt, typ_args),
            _ => panic!("Internal Verus Error: struct_field called for non-struct type"),
        };
        let (variant_name, field_typ) = match dt {
            Dt::Tuple(_arity) => {
                panic!("Internal Verus Error: struct_field called for tuple")
                /*let p = field_name.parse::<usize>().unwrap();
                let field_typ = typ_args[p].clone()
                let variant_name = crate::def::prefix_tuple_variant(arity);
                (variant_name, field_typ)*/
            }
            Dt::Path(path) => {
                let datatype = &datatypes[path];
                assert!(datatype.x.variants.len() == 1);
                let variant = &datatype.x.variants[0];
                let field = crate::ast_util::get_field(&variant.fields, field_name);
                let field_typ =
                    subst_typ_for_datatype(&datatype.x.typ_params, typ_args, &field.a.0);
                (variant.name.clone(), field_typ)
            }
        };
        ProjectionTyped::StructField(
            FieldOpr {
                datatype: dt.clone(),
                variant: variant_name.clone(),
                field: field_name.clone(),
                get_variant: false,
                check: crate::ast::VariantCheck::None,
            },
            field_typ,
        )
    }

    fn typ(&self) -> Typ {
        match self {
            ProjectionTyped::StructField(_, typ) => typ.clone(),
            ProjectionTyped::DerefMut(typ) => typ.clone(),
            ProjectionTyped::Index(_, typ) => typ.clone(),
        }
    }
}

impl FlattenedPlaceTyped {
    fn projected_typ(&self) -> Typ {
        if self.projections.len() > 0 {
            self.projections.last().unwrap().typ()
        } else {
            self.typ.clone()
        }
    }
}

impl LocalName {
    fn to_var_ident(&self) -> VarIdent {
        match self {
            LocalName::Named(x) => {
                // This disambiguator shouldn't have been used yet
                assert!(!matches!(x.1, VarIdentDisambiguate::ResInfTemp(_)));
                x.clone()
            }
            LocalName::Temporary(_ast_id, TempId(i)) => {
                VarIdent(str_ident("tmp"), VarIdentDisambiguate::ResInfTemp(*i))
            }
        }
    }

    fn is_temp(&self) -> bool {
        match self {
            LocalName::Named(..) => false,
            LocalName::Temporary(..) => true,
        }
    }
}

fn sort_and_remove_redundant(v: Vec<FlattenedPlace>) -> Vec<FlattenedPlace> {
    let mut v = v;
    v.sort();
    let mut w: Vec<FlattenedPlace> = vec![];
    for fp in v.into_iter() {
        if w.len() == 0 || !w[w.len() - 1].contains(&fp) {
            w.push(fp);
        }
    }
    for i in 0..w.len() {
        for j in 0..i {
            assert!(!w[i].intersects(&w[j]));
        }
    }
    w
}

////// CFG dataflow analysis

/// Trait defining a lattice for dataflow analysis
trait DataflowState {
    type Const;

    fn join(&mut self, b: &Self);
    fn transfer(&self, instr: &Instruction, c: &Self::Const) -> Self;
}

enum Direction {
    Forward,
    Reverse,
}

struct DataflowOutput<D> {
    /// output[bb][0] means "value at the start of bb"
    /// output[bb][i] means "value right after instruction (i-1)"
    output: Vec<Vec<D>>,
}

fn do_dataflow<D: DataflowState + Clone + Eq>(
    cfg: &CFG,
    empty: D,
    entry_or_exit: D,
    c: &D::Const,
    dir: Direction,
) -> DataflowOutput<D> {
    let mut output = DataflowOutput { output: vec![] };
    for bb in cfg.basic_blocks.iter() {
        let mut v = vec![];
        for _i in 0..bb.instructions.len() + 1 {
            v.push(empty.clone());
        }
        output.output.push(v);
    }

    let mut worklist = VecDeque::<BBIndex>::new();
    let mut in_worklist = vec![false; cfg.basic_blocks.len()];
    let mut has_run_yet = vec![false; cfg.basic_blocks.len()];

    match dir {
        Direction::Forward => {
            for i in 0..cfg.basic_blocks.len() {
                if cfg.basic_blocks[i].is_entry {
                    *output.output[i].last_mut().unwrap() = entry_or_exit.clone();
                }
                worklist.push_back(i);
                in_worklist[i] = true;
            }

            while let Some(bb) = worklist.pop_front() {
                in_worklist[bb] = false;

                let new_value = join_predecessors(&output, &cfg, bb, &empty, &entry_or_exit);
                let slot = &mut output.output[bb][0];

                if !has_run_yet[bb] || *slot != new_value {
                    *slot = new_value;
                    transfer_forward(&mut output.output[bb], &cfg.basic_blocks[bb].instructions, c);
                    has_run_yet[bb] = true;
                    for bb1 in cfg.basic_blocks[bb].successors.iter() {
                        if !in_worklist[*bb1] {
                            worklist.push_back(*bb1);
                            in_worklist[*bb1] = true;
                        }
                    }
                }
            }
        }
        Direction::Reverse => {
            for i in (0..cfg.basic_blocks.len()).rev() {
                if cfg.basic_blocks[i].is_exit {
                    *output.output[i].last_mut().unwrap() = entry_or_exit.clone();
                }
                worklist.push_back(i);
                in_worklist[i] = true;
            }

            while worklist.len() > 0 {
                let Some(bb) = worklist.pop_front() else {
                    break;
                };
                in_worklist[bb] = false;

                let new_value = join_successors(&output, &cfg, bb, &empty, &entry_or_exit);
                let slot = output.output[bb].last_mut().unwrap();

                if !has_run_yet[bb] || *slot != new_value {
                    *slot = new_value;
                    transfer_reverse(&mut output.output[bb], &cfg.basic_blocks[bb].instructions, c);
                    has_run_yet[bb] = true;
                    for bb1 in cfg.basic_blocks[bb].predecessors.iter() {
                        if !in_worklist[*bb1] {
                            worklist.push_back(*bb1);
                            in_worklist[*bb1] = true;
                        }
                    }
                }
            }
        }
    }

    output
}

fn join_predecessors<D: DataflowState + Clone>(
    output: &DataflowOutput<D>,
    cfg: &CFG,
    bb: BBIndex,
    empty: &D,
    entry: &D,
) -> D {
    if cfg.basic_blocks[bb].is_entry {
        let mut res = entry.clone();
        for pred in cfg.basic_blocks[bb].predecessors.iter().cloned() {
            res.join(&output.output[pred][output.output[pred].len() - 1]);
        }
        res
    } else if cfg.basic_blocks[bb].predecessors.len() > 0 {
        let pred0 = cfg.basic_blocks[bb].predecessors[0];
        let mut res = output.output[pred0][output.output[pred0].len() - 1].clone();
        for pred in cfg.basic_blocks[bb].predecessors.iter().skip(1).cloned() {
            res.join(&output.output[pred][output.output[pred].len() - 1]);
        }
        res
    } else {
        empty.clone()
    }
}

fn join_successors<D: DataflowState + Clone>(
    output: &DataflowOutput<D>,
    cfg: &CFG,
    bb: BBIndex,
    empty: &D,
    exit: &D,
) -> D {
    if cfg.basic_blocks[bb].is_exit {
        let mut res = exit.clone();
        for succ in cfg.basic_blocks[bb].successors.iter().cloned() {
            res.join(&output.output[succ][0]);
        }
        res
    } else if cfg.basic_blocks[bb].successors.len() > 0 {
        let succ0 = cfg.basic_blocks[bb].successors[0];
        let mut res = output.output[succ0][0].clone();
        for succ in cfg.basic_blocks[bb].successors.iter().skip(1).cloned() {
            res.join(&output.output[succ][0]);
        }
        res
    } else {
        empty.clone()
    }
}

fn transfer_forward<D: DataflowState>(
    output: &mut Vec<D>,
    instructions: &[Instruction],
    c: &D::Const,
) {
    for i in 0..instructions.len() {
        output[i + 1] = output[i].transfer(&instructions[i], c);
    }
}

fn transfer_reverse<D: DataflowState>(
    output: &mut Vec<D>,
    instructions: &[Instruction],
    c: &D::Const,
) {
    for i in (0..instructions.len()).rev() {
        output[i] = output[i + 1].transfer(&instructions[i], c);
    }
}

////// CFG debugging

#[allow(dead_code)]
fn pretty_cfg(cfg: &CFG) -> String {
    format!(
        "Locals:\n{:}\nCFG:\n{:}",
        pretty_locals(&cfg.locals),
        pretty_basic_blocks(&cfg, |_, _| None),
    )
}

fn pretty_locals(locals: &LocalCollection) -> String {
    let mut v = vec![];
    for l in locals.locals.iter() {
        v.push(pretty_local(l, locals.datatypes));
    }
    v.join("\n")
}

fn pretty_local(l: &Local, datatypes: &HashMap<Path, Datatype>) -> String {
    format!(
        "{:}{:} : {:}",
        pretty_local_name(&l.name),
        pretty_tree(&l.tree, datatypes),
        crate::ast_util::typ_to_diagnostic_str(l.tree.typ())
    )
}

fn pretty_tree(pt: &PlaceTree, datatypes: &HashMap<Path, Datatype>) -> String {
    match pt {
        PlaceTree::Leaf(_) => "".to_string(),
        PlaceTree::MutRef(_, pt) => format!(".*{:}", pretty_tree(&pt, datatypes)),
        PlaceTree::Struct(_, dt, variants) => {
            let mut v = vec![];
            for (variant_idx, fields) in variants.iter().enumerate() {
                for (field_idx, field) in fields.iter().enumerate() {
                    match field {
                        Some(child) => {
                            let name = pretty_field_name(dt, variant_idx, field_idx, datatypes);
                            v.push(format!("{:}{:}", name, pretty_tree(child, datatypes)));
                        }
                        _ => {}
                    }
                }
            }
            format!(".{{{:}}}", v.join(", "))
        }
        PlaceTree::Array(_, children) => {
            let mut v = vec![];
            for (i, child) in children.iter().enumerate() {
                v.push(format!("{:}{:}", i, pretty_tree(child, datatypes)));
            }
            format!(".[{:}]", v.join(", "))
        }
    }
}

#[allow(dead_code)]
fn pretty_basics_blocks_with_dataflow<D: std::fmt::Debug>(
    cfg: &CFG,
    output: &DataflowOutput<D>,
) -> String {
    pretty_basic_blocks(cfg, |i, j| Some(format!("{:?}", output.output[i][j])))
}

#[allow(dead_code)]
fn pretty_basics_blocks_with_dataflow2<D: std::fmt::Debug, E: std::fmt::Debug>(
    cfg: &CFG,
    output: &DataflowOutput<D>,
    output2: &DataflowOutput<E>,
) -> String {
    pretty_basic_blocks(cfg, |i, j| {
        Some(format!("{:?}; {:?}", output.output[i][j], output2.output[i][j]))
    })
}

fn pretty_basic_blocks(
    cfg: &CFG,
    intersperse_fn: impl Fn(BBIndex, usize) -> Option<String>,
) -> String {
    let mut v = vec![];
    for (i, bb) in cfg.basic_blocks.iter().enumerate() {
        v.push(format!("BasicBlock {:}:\n", i));
        v.push(format!("    is_entry = {:}\n", bb.is_entry));
        v.push(format!("    Predecessors: {:?}\n", pretty_bb_list(&bb.predecessors)));
        v.push(format!(
            "    (always_add_resolution_at_start = {:?})\n",
            bb.always_add_resolution_at_start
        ));
        v.push("    ----\n".to_string());
        for (j, instr) in bb.instructions.iter().enumerate() {
            match intersperse_fn(i, j) {
                Some(s) => {
                    v.push(format!("    // {:}\n", s));
                }
                None => {}
            }
            v.push(format!("    {:}\n", pretty_instr(&cfg.locals, instr)));
        }
        match intersperse_fn(i, bb.instructions.len()) {
            Some(s) => {
                v.push(format!("    // {:}\n", s));
            }
            None => {}
        }
        v.push("    ----\n".to_string());
        v.push(format!("    Successors: {:?}\n", pretty_bb_list(&bb.successors)));
        v.push(format!("    is_exit = {:}\n", bb.is_exit));
        v.push("\n".to_string());
    }
    v.join("")
}

fn pretty_bb_list(l: &Vec<BBIndex>) -> String {
    l.iter().map(|s| s.to_string()).collect::<Vec<_>>().join(", ")
}

fn pretty_instr(locals: &LocalCollection, instr: &Instruction) -> String {
    let (name, fp) = match &instr.kind {
        InstructionKind::MoveFrom(fp) => ("MoveFrom", fp),
        InstructionKind::Overwrite(fp) => ("Overwrite", fp),
        InstructionKind::Mutate(fp) => ("Mutate", fp),
        InstructionKind::DropFrom(fp) => ("DropFrom", fp),
        InstructionKind::ChargedDrop(i) => {
            return format!("ChargedDrop({:})", i);
        }
    };
    format!("{:}({:})", name, pretty_flattened_place(locals, fp))
}

fn pretty_local_name(l: &LocalName) -> String {
    match l {
        LocalName::Named(i) => (*i.0).clone(),
        LocalName::Temporary(_ast_id, TempId(i)) => format!("Temp_{i}"),
    }
}

fn pretty_flattened_place(locals: &LocalCollection, fp: &FlattenedPlace) -> String {
    let mut s: String = pretty_local_name(&locals.locals[fp.local].name);
    let mut tree: &PlaceTree = &locals.locals[fp.local].tree;
    for proj in fp.projections.iter() {
        let (x, t) = match proj {
            Projection::DerefMut => {
                let inner_tree: &PlaceTree = match tree {
                    PlaceTree::MutRef(_, t) => &**t,
                    _ => unreachable!(),
                };
                (".*".to_string(), inner_tree)
            }
            Projection::StructField((variant_idx, field_idx)) => {
                let (dt, inner_tree) = match tree {
                    PlaceTree::Struct(_, dt, trees) => (dt, &trees[*variant_idx][*field_idx]),
                    _ => unreachable!(),
                };
                let x = pretty_field_name(dt, *variant_idx, *field_idx, &locals.datatypes);
                let x = format!(".{:}", x);
                (x, inner_tree.as_ref().unwrap())
            }
            Projection::Index(idx) => {
                let inner_tree = match tree {
                    PlaceTree::Array(_, trees) => &trees[*idx],
                    _ => unreachable!(),
                };
                let x = format!("[{:}]", idx);
                (x, inner_tree)
            }
        };
        s += &x;
        tree = t;
    }
    s
}

fn pretty_field_name(
    dt: &Dt,
    variant_idx: usize,
    field_idx: usize,
    datatypes: &HashMap<Path, Datatype>,
) -> String {
    match dt {
        Dt::Tuple(_) => {
            format!("{:}", field_idx)
        }
        Dt::Path(p) => {
            let datatype = &datatypes[p];
            if datatype.x.variants.len() > 1 {
                format!(
                    "{:}_{:}",
                    datatype.x.variants[variant_idx].name,
                    datatype.x.variants[variant_idx].fields[field_idx].name
                )
            } else {
                format!("{:}", datatype.x.variants[variant_idx].fields[field_idx].name)
            }
        }
    }
}

////// Analysis: Initialization

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct InitializationPossibilities {
    /// Is it possible to reach the given program point with the given place
    /// not initialized?
    /// (Using the definition of "conditionally initialized" described above)
    can_be_uninit: bool,
}

impl DataflowState for InitializationPossibilities {
    type Const = FlattenedPlace;

    fn join(&mut self, b: &Self) {
        *self =
            InitializationPossibilities { can_be_uninit: self.can_be_uninit || b.can_be_uninit };
    }

    // forward transfer
    fn transfer(&self, instr: &Instruction, place: &FlattenedPlace) -> Self {
        match &instr.kind {
            InstructionKind::MoveFrom(sp) => {
                if sp.contains(place) {
                    InitializationPossibilities { can_be_uninit: true }
                } else {
                    *self
                }
            }
            InstructionKind::Overwrite(sp) => {
                if sp.contains(place) {
                    InitializationPossibilities { can_be_uninit: false }
                } else {
                    *self
                }
            }
            InstructionKind::Mutate(_sp) => *self,
            InstructionKind::DropFrom(sp) => {
                if sp.contains(place) {
                    InitializationPossibilities { can_be_uninit: true }
                } else {
                    *self
                }
            }
            InstructionKind::ChargedDrop(_) => *self,
        }
    }
}

impl InitializationPossibilities {
    fn empty() -> Self {
        InitializationPossibilities { can_be_uninit: false }
    }

    fn entry() -> Self {
        InitializationPossibilities { can_be_uninit: true }
    }
}

////// Analysis: Resolve

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct ResolveSafety {
    can_resolve: bool,
}

impl DataflowState for ResolveSafety {
    type Const = FlattenedPlace;

    fn join(&mut self, b: &Self) {
        *self = ResolveSafety { can_resolve: self.can_resolve && b.can_resolve }
    }

    // backward transfer
    fn transfer(&self, instr: &Instruction, place: &FlattenedPlace) -> Self {
        match &instr.kind {
            InstructionKind::MoveFrom(sp) | InstructionKind::Mutate(sp) => {
                if sp.intersects(place) {
                    ResolveSafety { can_resolve: false }
                } else {
                    *self
                }
            }
            InstructionKind::Overwrite(sp) | InstructionKind::DropFrom(sp) => {
                if sp.contains_and_not_separated_by_deref(place) {
                    ResolveSafety { can_resolve: true }
                } else if sp.intersects(place) {
                    ResolveSafety { can_resolve: false }
                } else {
                    *self
                }
            }
            InstructionKind::ChargedDrop(_) => *self,
        }
    }
}

impl ResolveSafety {
    fn empty() -> Self {
        ResolveSafety { can_resolve: true }
    }

    fn exit(place: &FlattenedPlace) -> Self {
        ResolveSafety { can_resolve: !place.has_deref() }
    }
}

////// Use the results of the analysis to determine where resolutions should go

/// Determine the resolutions to be inserted. Doesn't account for scopes, so we might
/// drop some resolutions later if they turn out to refer to variables that are out-of-scope.
fn get_resolutions(
    cfg: &CFG,
    rtypes: &ResolutionTypes,
    asserts: Vec<((BBIndex, usize), Expr)>,
) -> Vec<ResolutionToInsert> {
    // A place behind an initialized mutable reference can't be uninitialized,
    // so we only check places that aren't behind mutable references.
    let initialization_places = cfg.locals.places_skip_insides_of_mut_refs();
    let initialization_analyses: Vec<DataflowOutput<InitializationPossibilities>> =
        initialization_places
            .iter()
            .map(|place| {
                do_dataflow::<InitializationPossibilities>(
                    cfg,
                    InitializationPossibilities::empty(),
                    InitializationPossibilities::entry(),
                    place,
                    Direction::Forward,
                )
            })
            .collect();

    // A place typed as a mutable reference needs to be checked separately from
    // the places behind that mutable reference (see the explanation above).
    let resolve_places = cfg.locals.places_including_insides_of_mut_refs();
    let resolve_analyses: Vec<DataflowOutput<ResolveSafety>> = resolve_places
        .iter()
        .map(|place| {
            do_dataflow::<ResolveSafety>(
                cfg,
                ResolveSafety::empty(),
                ResolveSafety::exit(place),
                place,
                Direction::Reverse,
            )
        })
        .collect();

    let mut output = vec![];

    let mut i_idx = 0;
    for r_idx in 0..resolve_places.len() {
        while !initialization_places[i_idx].contains(&resolve_places[r_idx]) {
            i_idx += 1;
        }

        //println!("{:}\n", pretty_flattened_place(&cfg.locals, &resolve_places[r_idx]));
        //println!("{:}\n", pretty_basics_blocks_with_dataflow2(&cfg, &resolve_analyses[r_idx], &initialization_analyses[i_idx]));

        let typ = cfg.locals.get_typ(&resolve_places[r_idx]);
        if rtypes.has_nontrivial_resolve(&typ) {
            get_resolutions_for_place(
                cfg,
                &resolve_places[r_idx],
                &initialization_analyses[i_idx],
                &resolve_analyses[r_idx],
                &mut output,
            );
        }
    }

    // Check the asserts for explicit mentions of has_resolved
    for (cfg_loc, assert_expr) in asserts.into_iter() {
        crate::ast_visitor::expr_visitor_check::<(), _>(&assert_expr, &mut |_, e: &Expr| {
            let ExprX::UnaryOpr(UnaryOpr::HasResolved(_), e1) = &e.x else {
                return Ok(());
            };
            let ExprX::ReadPlace(p, _) = &e1.x else {
                return Ok(());
            };
            let Some(fp) = cfg.locals.try_get_flattened_place(p) else {
                return Ok(());
            };
            // Suppose the user is asserting about has_resolved(x) but the analysis
            // operates over subplaces x.0 and x.1. We have to take the union of all these
            // subplaces.
            let is_safe = whole_is_initialized(
                &initialization_places,
                &initialization_analyses,
                &fp,
                cfg_loc,
            ) && whole_can_resolve(&resolve_places, &resolve_analyses, &fp, cfg_loc);
            if is_safe {
                output.push(ResolutionToInsert {
                    place: fp,
                    position: cfg.basic_blocks[cfg_loc.0].position(cfg_loc.1),
                });
            }
            Ok(())
        })
        .unwrap();
    }

    output
}

fn whole_is_initialized(
    initialized_places: &[FlattenedPlace],
    initialization_analysis: &[DataflowOutput<InitializationPossibilities>],
    fp: &FlattenedPlace,
    cfg_loc: (BBIndex, usize),
) -> bool {
    let fp = fp.truncate_to_deref();
    for (fp0, analysis) in initialized_places.iter().zip(initialization_analysis.iter()) {
        if fp.contains(fp0) {
            if analysis.output[cfg_loc.0][cfg_loc.1].can_be_uninit {
                return false;
            }
        }
    }
    true
}

fn whole_can_resolve(
    resolve_places: &[FlattenedPlace],
    resolve_analysis: &[DataflowOutput<ResolveSafety>],
    fp: &FlattenedPlace,
    cfg_loc: (BBIndex, usize),
) -> bool {
    for (fp0, analysis) in resolve_places.iter().zip(resolve_analysis.iter()) {
        if fp.contains_and_not_separated_by_deref(fp0) {
            if !analysis.output[cfg_loc.0][cfg_loc.1].can_resolve {
                return false;
            }
        }
    }
    true
}

fn get_resolutions_for_place(
    cfg: &CFG,
    place: &FlattenedPlace,
    initialization_analysis: &DataflowOutput<InitializationPossibilities>,
    resolve_analysis: &DataflowOutput<ResolveSafety>,
    output: &mut Vec<ResolutionToInsert>,
) {
    let is_temp = cfg.locals.locals[place.local].name.is_temp();
    for bb in 0..cfg.basic_blocks.len() {
        for i in 0..cfg.basic_blocks[bb].instructions.len() + 1 {
            // Is it safe to resolve here?
            let can_assume_has_resolved = resolve_analysis.output[bb][i].can_resolve
                && !initialization_analysis.output[bb][i].can_be_uninit;
            if can_assume_has_resolved {
                // If so, is it *useful* to resolve here?
                let should_assume_has_resolved =
                    // At beginning of function, or beginning or end of a loop,
                    // Always add resolutions for non-temps
                    (i == 0 && cfg.basic_blocks[bb].always_add_resolution_at_start && !is_temp)
                    // If there's any predecessor block where this value can't be resolved
                    || (i == 0
                        && cfg.basic_blocks[bb].predecessors.iter().any(|pred| {
                            !resolve_analysis.output[*pred].last().unwrap().can_resolve
                        }))
                    // If this couldn't have been resolved at the previous instruction
                    || (i > 0 && !resolve_analysis.output[bb][i - 1].can_resolve)
                    // If the place had a different value at the previous instruction
                    || (i > 0 && place.value_may_change(&cfg.basic_blocks[bb].instructions[i - 1]));
                if should_assume_has_resolved {
                    push_resolution(cfg, place, bb, i, output);
                }
            }
        }
    }
}

/// Emit a resolution at instruction `i` of `bb`.
///
/// We special case the `MatchIntermediate` position because there's otherwise no good place
/// to put it in the AST. To deal with it, we try to forward it to the successor blocks,
/// which is sound to do if the successor block only has a single predecessor.
/// (This can be seen from the dataflow equations.)
/// However, this criterion doesn't always hold (See the
/// `test_match_guard_asymmetric_mutation_no_panic` case)
/// TODO (new_mut_ref) (completeness): Find a different solutio that works in all cases
fn push_resolution(
    cfg: &CFG,
    place: &FlattenedPlace,
    bb: BBIndex,
    i: usize,
    output: &mut Vec<ResolutionToInsert>,
) {
    let position = cfg.basic_blocks[bb].position(i);
    if matches!(position, AstPosition::MatchIntermediate)
        && i == 0
        && cfg.basic_blocks[bb].instructions.is_empty()
        && cfg.basic_blocks[bb].successors.iter().all(|succ| {
            cfg.basic_blocks[*succ].predecessors.as_slice() == [bb]
                && !cfg.basic_blocks[*succ].is_entry
        })
    {
        for succ in cfg.basic_blocks[bb].successors.iter() {
            push_resolution(cfg, place, *succ, 0, output);
        }
    } else {
        output.push(ResolutionToInsert { place: place.clone(), position });
    }
}

impl BasicBlock {
    fn position(&self, i: usize) -> AstPosition {
        if i == 0 {
            self.position_of_start
        } else {
            self.instructions[i - 1].post_instruction_position
        }
    }
}

////// Modify the AST Expr with the new resolutions

/// Returns the given expression with AssumeResolved expressions inserted.
fn apply_resolutions(
    cfg: &CFG,
    params: &Params,
    body: &Expr,
    resolutions: Vec<ResolutionToInsert>,
    assigns_to_resolve: Vec<AstId>,
    typ_inv_obligations: Vec<(AstId, FunWithVis)>,
    typ_inv_info: &crate::modes::TypeInvInfo,
    loops_with_no_back_edges: HashSet<AstId>,
    module: &Path,
    drops: DropInsertions,
) -> Result<Expr, VirErr> {
    let DropInsertions { items: drop_items, temps: drop_temps, flags: drop_flags, sites: _ } =
        drops;
    // All the resolutions that apply to PlaceX::Temporary nodes
    let mut temp_map = HashMap::<AstId, (Vec<FlattenedPlace>, bool)>::new();
    let mut typ_inv_map = HashMap::<AstId, (FunWithVis, bool)>::new();

    // All the resolutions that apply to Expr and Stmt nodes
    let mut id_map = HashMap::<
        AstId,
        (
            Vec<FlattenedPlace>,
            Vec<FlattenedPlace>,
            Vec<FlattenedPlace>,
            Vec<FlattenedPlace>,
            Vec<FlattenedPlace>,
            bool,
            bool,
        ),
    >::new();

    for r in resolutions.into_iter() {
        // For any temp that has an Assume(HasResolved(...)) about it, we need to expand that temp
        if let Some(temp_ast_id) = r.is_for_temp(cfg) {
            temp_map.entry(temp_ast_id).or_insert_with_key(|_| (vec![], false));
        }

        let ast_id = match r.position {
            AstPosition::Before(ast_id) => ast_id,
            AstPosition::After(ast_id) => ast_id,
            AstPosition::AfterArguments(ast_id) => ast_id,
            AstPosition::OnUnwind(_) => {
                // It might be necessary to do something here for more
                // advanced unwind-related stuff?
                continue;
            }
            AstPosition::MatchIntermediate => {
                continue;
            }
            AstPosition::AfterBool(ast_id, _b) => ast_id,
            AstPosition::AfterTempAssignment(ast_id) => {
                temp_map.entry(ast_id).or_insert_with_key(|_| (vec![], false)).0.push(r.place);
                continue;
            }
            AstPosition::BeforeAssignWrite(_) => {
                // (only drop points are here, which the resolution analysis does not see)
                continue;
            }
        };

        let entry = id_map
            .entry(ast_id)
            .or_insert_with_key(|_| (vec![], vec![], vec![], vec![], vec![], false, false));

        match r.position {
            AstPosition::Before(_ast_id) => {
                entry.0.push(r.place);
            }
            AstPosition::After(_ast_id) => {
                entry.1.push(r.place);
            }
            AstPosition::AfterArguments(_ast_id) => {
                entry.2.push(r.place);
            }
            AstPosition::OnUnwind(_) => unreachable!(),
            AstPosition::AfterTempAssignment(_) => unreachable!(),
            AstPosition::MatchIntermediate => unreachable!(),
            AstPosition::BeforeAssignWrite(_) => unreachable!(),
            AstPosition::AfterBool(_ast_id, false) => {
                entry.3.push(r.place);
            }
            AstPosition::AfterBool(_ast_id, true) => {
                entry.4.push(r.place);
            }
        };
    }

    for ast_id in assigns_to_resolve.into_iter() {
        let entry = id_map
            .entry(ast_id)
            .or_insert_with_key(|_| (vec![], vec![], vec![], vec![], vec![], false, false));
        assert!(!entry.5);
        entry.5 = true;
    }

    for (ast_id, fun) in typ_inv_obligations.iter() {
        let found = typ_inv_map.insert(*ast_id, (fun.clone(), false));
        assert!(found.is_none());
    }

    // -V alloc-check: the temporaries whose values the drop charges read must be named
    for ast_id in drop_temps.iter() {
        temp_map.entry(*ast_id).or_insert_with_key(|_| (vec![], false));
    }

    let mut maps = (id_map, temp_map, typ_inv_map, drop_items);

    let mut scope_map = VisitorScopeMap::new();
    scope_map.push_scope(true);
    for param in params.iter() {
        scope_map
            .insert(
                param.x.name.clone(),
                crate::ast_visitor::ScopeEntry::new(&param.x.typ, Some(param.x.user_mut), true),
            )
            .unwrap();
    }

    let mut result = crate::ast_visitor::map_expr_visitor_env(
        body,
        &mut scope_map,
        &mut maps,
        &|(id_map, _, _, drop_items), scope_map, expr: &Expr| {
            let expr2 = crate::user_defined_type_invariants::annotate_one(
                expr,
                typ_inv_info,
                &cfg.locals.functions,
                &cfg.locals.datatypes,
                module,
            )?;
            let expr2 = maybe_set_loop_no_back_edge(expr2, &loops_with_no_back_edges);

            let res = id_map.get_mut(&expr.span.id);
            let drops = drop_items.get_mut(&expr.span.id);
            if res.is_none() && drops.is_none() {
                return Ok(expr2.clone());
            }
            let mut befores_exprs = vec![];
            let mut afters_exprs = vec![];
            let mut after_args_exprs = vec![];
            let mut after_f_exprs = vec![];
            let mut after_t_exprs = vec![];
            let mut assign_write_exprs = vec![];
            let mut e = expr2.clone();
            if let Some((befores, afters, after_args, after_f, after_t, assn, seen_yet)) = res {
                if *seen_yet {
                    panic!("Verus internal error: duplicate AstId {:?}", expr.span);
                }
                *seen_yet = true;

                befores_exprs = filter_and_make_assumes(cfg, &expr.span, scope_map, befores);
                afters_exprs = filter_and_make_assumes(cfg, &expr.span, scope_map, afters);
                after_args_exprs = filter_and_make_assumes(cfg, &expr.span, scope_map, after_args);
                after_f_exprs = filter_and_make_assumes(cfg, &expr.span, scope_map, after_f);
                after_t_exprs = filter_and_make_assumes(cfg, &expr.span, scope_map, after_t);

                if *assn {
                    e = apply_resolution_to_assignment(&e);
                }
            }
            if let Some(d) = drops {
                if d.seen {
                    panic!("Verus internal error: duplicate AstId {:?}", expr.span);
                }
                d.seen = true;
                befores_exprs.extend(drop_items_in_scope(&expr.span, scope_map, &d.befores)?);
                afters_exprs.extend(drop_items_in_scope(&expr.span, scope_map, &d.afters)?);
                after_args_exprs.extend(drop_items_in_scope(&expr.span, scope_map, &d.after_args)?);
                after_f_exprs.extend(drop_items_in_scope(&expr.span, scope_map, &d.after_f)?);
                after_t_exprs.extend(drop_items_in_scope(&expr.span, scope_map, &d.after_t)?);
                assign_write_exprs = drop_items_in_scope(&expr.span, scope_map, &d.assign_write)?;
                if d.charge_assign {
                    e = match &e.x {
                        ExprX::Assign { place, rhs, op, resolve, typ, charge_drop: _ } => {
                            e.new_x(ExprX::Assign {
                                place: place.clone(),
                                rhs: rhs.clone(),
                                op: *op,
                                resolve: *resolve,
                                typ: typ.clone(),
                                charge_drop: true,
                            })
                        }
                        _ => panic!("charge_assign expects Assign node"),
                    };
                }
            }

            let e = apply_assign_write_exprs(e, assign_write_exprs);
            let e = apply_after_args_exprs(e, after_args_exprs);
            let e = apply_before_exprs(e, befores_exprs);
            let e = apply_after_exprs(e, afters_exprs);
            let e = apply_after_bool_exprs(e, after_f_exprs, after_t_exprs);

            Ok(e)
        },
        &|(id_map, _, _, drop_items), scope_map, stmt| {
            let res = id_map.get_mut(&stmt.span.id);
            let drops = drop_items.get_mut(&stmt.span.id);
            if res.is_none() && drops.is_none() {
                return Ok(vec![stmt.clone()]);
            }
            let mut befores_exprs = vec![];
            let mut afters_exprs = vec![];
            let empty = vec![];
            let mut res_afters = &empty;
            if let Some((befores, afters, after_args, after_f, after_t, assn, seen_yet)) = res {
                if *seen_yet {
                    panic!("Verus internal error: duplicate AstId");
                }
                if after_f.len() > 0 || after_t.len() > 0 {
                    panic!("Verus internal error: AfterBool should only apply to exprs");
                }
                if *assn {
                    panic!("Verus internal error: assignment should only apply to exprs");
                }
                assert!(after_args.len() == 0);
                *seen_yet = true;

                befores_exprs = filter_and_make_assumes(cfg, &stmt.span, scope_map, befores);
                res_afters = afters;
            }
            let mut drop_afters = &vec![];
            if let Some(d) = drops {
                if d.seen {
                    panic!("Verus internal error: duplicate AstId");
                }
                d.seen = true;
                if d.after_args.len() > 0
                    || d.after_f.len() > 0
                    || d.after_t.len() > 0
                    || d.assign_write.len() > 0
                    || d.charge_assign
                {
                    return Err(crate::messages::internal_error(
                        &stmt.span,
                        "a drop is charged at an expression position of a statement",
                    ));
                }
                befores_exprs.extend(drop_items_in_scope(&stmt.span, scope_map, &d.befores)?);
                drop_afters = &d.afters;
            }

            scope_map.push_scope(true);
            match &stmt.x {
                StmtX::Expr(_) => {}
                StmtX::Decl { pattern, mode: _, init, els: _, assert_irrefutable: _ } => {
                    use crate::ast_visitor::Scoper;
                    scope_map.insert_pattern_bindings(pattern, init.is_some());
                }
            }
            afters_exprs.extend(filter_and_make_assumes(cfg, &stmt.span, scope_map, res_afters));
            let drop_afters_exprs = drop_items_in_scope(&stmt.span, scope_map, drop_afters);
            scope_map.pop_scope();
            afters_exprs.extend(drop_afters_exprs?);

            let mut v = exprs_to_stmts(befores_exprs);
            v.push(stmt.clone());
            v.append(&mut exprs_to_stmts(afters_exprs));

            Ok(v)
        },
        &|_, t| Ok(t.clone()),
        &|(_, temp_map, typ_inv_map, _), scope_map, p| {
            let p1 = if matches!(&p.x, PlaceX::Temporary(_)) {
                if let Some((afters, seen_yet)) = temp_map.get_mut(&p.span.id) {
                    if *seen_yet {
                        panic!("Verus internal error: duplicate AstId");
                    }
                    *seen_yet = true;
                    let afters_exprs = filter_and_make_assumes(cfg, &p.span, scope_map, afters);
                    apply_temp_simplification(cfg, p, afters_exprs)
                } else {
                    p.clone()
                }
            } else {
                p.clone()
            };

            if let Some((fun, seen_yet)) = typ_inv_map.get_mut(&p.span.id) {
                if *seen_yet {
                    panic!("Verus internal error: duplicate AstId");
                }
                *seen_yet = true;

                let fun = fun.check_vis(&p.span, module)?;

                let x = PlaceX::UserDefinedTypInvariantObligation(p1.clone(), fun.clone());
                Ok(SpannedTyped::new(&p1.span, &p1.typ, x))
            } else {
                Ok(p1)
            }
        },
        &|_, _, pattern| Ok(pattern.clone()),
    )?;

    let (id_map, temp_map, typ_inv_map, drop_items) = maps;

    for (_, d) in drop_items.iter() {
        if !d.seen {
            return Err(crate::messages::internal_error(
                &body.span,
                "-V alloc-check: a drop of this function could not be placed",
            ));
        }
    }

    for (_, (_, _, _, _, _, _, found)) in id_map.iter() {
        if !*found {
            panic!("resolution_inference: bad run for apply_resolutions");
        }
    }

    for (_, (_, found)) in temp_map.iter() {
        if !*found {
            panic!("resolution_inference: bad run for apply_resolutions");
        }
    }

    for (_, (_, found)) in typ_inv_map.iter() {
        if !*found {
            panic!("resolution_inference: bad run for apply_resolutions");
        }
    }

    if temp_map.len() > 0 || drop_flags.len() > 0 {
        result = add_decls_for_temps(cfg, &temp_map, &drop_flags, &result);
    }

    Ok(result)
}

/// The drop items (see `DropInsertions`), whose named locals must be in scope
fn drop_items_in_scope(
    span: &Span,
    scope_map: &VisitorScopeMap,
    items: &Vec<(Expr, Option<VarIdent>)>,
) -> Result<Vec<Expr>, VirErr> {
    let mut v = vec![];
    for (e, local) in items.iter() {
        if let Some(x) = local {
            if !scope_map.contains_key(x) {
                return Err(crate::messages::internal_error(
                    span,
                    format!(
                        "-V alloc-check: a drop of `{}` is charged where it is not in scope",
                        crate::def::user_local_name(x)
                    ),
                ));
            }
        }
        v.push(e.clone());
    }
    Ok(v)
}

/// Run the given statements in an assignment after its right-hand side, before the write
fn apply_assign_write_exprs(expr: Expr, exprs: Vec<Expr>) -> Expr {
    if exprs.len() == 0 {
        return expr;
    }
    match &expr.x {
        ExprX::Assign { place, rhs, op, resolve, typ, charge_drop } => {
            let stmts: Vec<Stmt> = exprs_to_stmts(exprs);
            let block =
                SpannedTyped::new(&rhs.span, &unit_typ(), ExprX::Block(Arc::new(stmts), None));
            let rhs =
                SpannedTyped::new(&rhs.span, &rhs.typ, ExprX::EvalAndResolve(rhs.clone(), block));
            expr.new_x(ExprX::Assign {
                place: place.clone(),
                rhs,
                op: *op,
                resolve: *resolve,
                typ: typ.clone(),
                charge_drop: *charge_drop,
            })
        }
        _ => panic!("apply_assign_write_exprs expects Assign node"),
    }
}

impl ResolutionToInsert {
    fn is_for_temp(&self, cfg: &CFG) -> Option<AstId> {
        match &cfg.locals.locals[self.place.local].name {
            LocalName::Temporary(ast_id, _temp_id) => Some(*ast_id),
            LocalName::Named(_) => None,
        }
    }
}

/// Filter for the resolutions that are actually in scope and make the AssumeResolved expressions.
fn filter_and_make_assumes(
    cfg: &CFG,
    span: &Span,
    scope_map: &VisitorScopeMap,
    v: &Vec<FlattenedPlace>,
) -> Vec<Expr> {
    v.iter()
        .filter_map(|fp| {
            let name = &cfg.locals.locals[fp.local].name;
            let keep = match name {
                LocalName::Named(name) => scope_map.contains_key(name),
                LocalName::Temporary(..) => {
                    // We can't use the scope_map to check if the temporary is in scope
                    // Instead, we make sure the algorithm doesn't try to insert a resolution
                    // for a temp-place outside of the temp scope.
                    true
                }
            };
            if keep { Some(make_assume(cfg, span, fp)) } else { None }
        })
        .collect()
}

/// Returns:
/// assume(all IsVariant conditions needed for Place to be valid ==> HasResolved(Place))
fn make_assume(cfg: &CFG, span: &Span, fp: &FlattenedPlace) -> Expr {
    let ast_place = cfg.locals.to_ast_place(span, fp);
    let e = crate::ast_util::place_to_spec_expr(&ast_place);
    // The typ is correct up to Box and Tracked decorations, which is fine
    let has_resolvedx = ExprX::UnaryOpr(UnaryOpr::HasResolved(ast_place.typ.clone()), e);
    let has_resolved = SpannedTyped::new(&ast_place.span, &bool_typ(), has_resolvedx);
    let conditional_has_resolved =
        condition_on_enum_variants(&has_resolved, &ast_place, &cfg.locals.datatypes);
    crate::ast_util::mk_assume(&ast_place.span, &conditional_has_resolved)
}

/// Given an `Assign`, sets the `resolve` field to true
/// (Equivalently, adds an `assume(has_resolved(...))` for the value being overwritten
fn apply_resolution_to_assignment(e: &Expr) -> Expr {
    match &e.x {
        ExprX::Assign { place, rhs, op, resolve, typ, charge_drop } => {
            assert!(!resolve);
            e.new_x(ExprX::Assign {
                place: place.clone(),
                rhs: rhs.clone(),
                op: *op,
                resolve: true,
                typ: typ.clone(),
                charge_drop: *charge_drop,
            })
        }
        _ => {
            panic!("apply_resolution_to_assignment expects Assign node");
        }
    }
}

/// Returns:
/// `all IsVariant conditions needed for Place to be valid ==> bool_expr`
fn condition_on_enum_variants(
    bool_expr: &Expr,
    place: &Place,
    datatypes: &HashMap<Path, Datatype>,
) -> Expr {
    match &place.x {
        PlaceX::Local(_l) => bool_expr.clone(),
        PlaceX::DerefMut(p) => condition_on_enum_variants(bool_expr, p, datatypes),
        PlaceX::Index(p, _, ArrayKind::Array, _) => {
            condition_on_enum_variants(bool_expr, p, datatypes)
        }
        PlaceX::Field(field_opr, p) => {
            let is_irref = match &field_opr.datatype {
                Dt::Tuple(_) => true,
                Dt::Path(path) => datatypes[path].x.variants.len() == 1,
            };
            let conditioned_bool_expr = if is_irref {
                bool_expr
            } else {
                let e0 = crate::ast_util::place_to_spec_expr(p);
                let is_variantx = ExprX::UnaryOpr(
                    UnaryOpr::IsVariant {
                        datatype: field_opr.datatype.clone(),
                        variant: field_opr.variant.clone(),
                    },
                    e0,
                );
                let is_variant = SpannedTyped::new(&place.span, &bool_typ(), is_variantx);
                &crate::ast_util::mk_implies(&place.span, &is_variant, bool_expr)
            };
            condition_on_enum_variants(conditioned_bool_expr, p, datatypes)
        }
        _ => {
            // We only have to handle places produced by `to_ast_place`
            panic!("condition_on_enum_variants got unexpected Place kind")
        }
    }
}

fn exprs_to_stmts(exprs: Vec<Expr>) -> Vec<Stmt> {
    exprs.into_iter().map(|e| Spanned::new(e.span.clone(), StmtX::Expr(e.clone()))).collect()
}

fn apply_before_exprs(expr: Expr, before_exprs: Vec<Expr>) -> Expr {
    if before_exprs.len() == 0 {
        return expr;
    }
    let mut stmts = vec![];
    for e in before_exprs.into_iter() {
        stmts.push(Spanned::new(e.span.clone(), StmtX::Expr(e)));
    }
    SpannedTyped::new(&expr.span, &expr.typ, ExprX::Block(Arc::new(stmts), Some(expr.clone())))
}

fn apply_after_exprs(expr: Expr, after_exprs: Vec<Expr>) -> Expr {
    if after_exprs.len() == 0 {
        return expr;
    }
    let e = if after_exprs.len() == 1 {
        after_exprs[0].clone()
    } else {
        let mut stmts = vec![];
        for e in after_exprs.into_iter() {
            stmts.push(Spanned::new(e.span.clone(), StmtX::Expr(e)));
        }
        SpannedTyped::new(&expr.span, &unit_typ(), ExprX::Block(Arc::new(stmts), None))
    };
    SpannedTyped::new(&expr.span, &expr.typ, ExprX::EvalAndResolve(expr.clone(), e))
}

fn apply_after_bool_exprs(expr: Expr, after_f: Vec<Expr>, after_t: Vec<Expr>) -> Expr {
    if after_f.len() == 0 && after_t.len() == 0 {
        return expr;
    }

    // Turn b into:
    // if b { t_stmts; true } else { f_stmts; false }
    // where t_stmts are the statements to run on true, and
    // f_stmts are the statements to run on false

    let mut f_stmts = vec![];
    for e in after_f.into_iter() {
        f_stmts.push(Spanned::new(e.span.clone(), StmtX::Expr(e)));
    }

    let mut t_stmts = vec![];
    for e in after_t.into_iter() {
        t_stmts.push(Spanned::new(e.span.clone(), StmtX::Expr(e)));
    }

    SpannedTyped::new(
        &expr.span,
        &bool_typ(),
        ExprX::If(
            expr.clone(),
            SpannedTyped::new(
                &expr.span,
                &unit_typ(),
                ExprX::Block(Arc::new(t_stmts), Some(mk_bool(&expr.span, true))),
            ),
            Some(SpannedTyped::new(
                &expr.span,
                &unit_typ(),
                ExprX::Block(Arc::new(f_stmts), Some(mk_bool(&expr.span, false))),
            )),
        ),
    )
}

fn apply_after_args_exprs(expr: Expr, exprs: Vec<Expr>) -> Expr {
    if exprs.len() == 0 {
        return expr;
    }
    match &expr.x {
        ExprX::Call { target: ct, args, post_args: None, body } => {
            let mut stmts = vec![];
            for e in exprs.into_iter() {
                stmts.push(Spanned::new(e.span.clone(), StmtX::Expr(e)));
            }
            let block =
                SpannedTyped::new(&expr.span, &unit_typ(), ExprX::Block(Arc::new(stmts), None));
            SpannedTyped::new(
                &expr.span,
                &expr.typ,
                ExprX::Call {
                    target: ct.clone(),
                    args: args.clone(),
                    post_args: Some(block),
                    body: body.clone(),
                },
            )
        }
        _ => {
            panic!("apply_after_args_exprs expected ExprX::Call");
        }
    }
}

fn apply_temp_simplification(cfg: &CFG, place: &Place, exprs: Vec<Expr>) -> Place {
    // Note that exprs might be empty here; we still need to do the transformation if there
    // is some Assume(HasResolved) for this temporary being inserted at a different location.

    let PlaceX::Temporary(expr) = &place.x else {
        panic!("Verus Internal Error: apply_temp_simplification expected Temporary");
    };

    // Translate:
    // Temporary(expr)   -->   WithExpr({ tmp = expr; other_stmts; }, Local(tmp))
    // Use an Assign node (we add the Decl in `add_decls_for_temps`)

    let ast_id = place.span.id;
    let temp_id = cfg.locals.ast_id_to_temp_id[&ast_id];
    let x = LocalName::Temporary(ast_id, temp_id).to_var_ident();

    let tmp_local_place = SpannedTyped::new(&place.span, &place.typ, PlaceX::Local(x.clone()));

    let assign_expr = SpannedTyped::new(
        &place.span,
        &unit_typ(),
        ExprX::Assign {
            place: tmp_local_place.clone(),
            rhs: expr.clone(),
            op: None,
            typ: place.typ.clone(),
            resolve: false,
            charge_drop: false,
        },
    );

    let mut stmts = vec![Spanned::new(place.span.clone(), StmtX::Expr(assign_expr))];
    for e in exprs.into_iter() {
        stmts.push(Spanned::new(e.span.clone(), StmtX::Expr(e)));
    }

    let block_expr =
        SpannedTyped::new(&place.span, &unit_typ(), ExprX::Block(Arc::new(stmts), None));

    SpannedTyped::new(&place.span, &place.typ, PlaceX::WithExpr(block_expr, tmp_local_place))
}

fn add_decls_for_temps(
    cfg: &CFG,
    temp_map: &HashMap<AstId, (Vec<FlattenedPlace>, bool)>,
    drop_flags: &Vec<VarIdent>,
    expr: &Expr,
) -> Expr {
    // Declare all temp vars at the beginning of the function body
    // (There doesn't seem to be any point in minimizing the scope of such variables,
    // but maybe we should restrict them to individual loops?)
    let mut stmts = vec![];
    for local in cfg.locals.locals.iter() {
        if let LocalName::Temporary(ast_id, temp_id) = &local.name {
            if temp_map.contains_key(ast_id) {
                let x = LocalName::Temporary(*ast_id, *temp_id).to_var_ident();
                let typ = local.tree.typ();
                stmts.push(Spanned::new(
                    expr.span.clone(),
                    StmtX::Decl {
                        pattern: PatternX::simple_var(x, &expr.span, typ),
                        mode: None, // doesn't matter
                        init: None,
                        els: None,
                        assert_irrefutable: false,
                    },
                ));
            }
        }
    }
    // -V alloc-check: the drop flags, initially false
    for x in drop_flags.iter() {
        stmts.push(Spanned::new(
            expr.span.clone(),
            StmtX::Decl {
                pattern: PatternX::simple_var(x.clone(), &expr.span, &bool_typ()),
                mode: None, // doesn't matter
                init: None,
                els: None,
                assert_irrefutable: false,
            },
        ));
        let e = mk_flag_assign(&expr.span, x, false);
        stmts.push(Spanned::new(expr.span.clone(), StmtX::Expr(e)));
    }
    SpannedTyped::new(&expr.span, &expr.typ, ExprX::Block(Arc::new(stmts), Some(expr.clone())))
}

fn maybe_set_loop_no_back_edge(e: Expr, loops_with_no_back_edges: &HashSet<AstId>) -> Expr {
    if matches!(&e.x, ExprX::Loop { .. }) && loops_with_no_back_edges.contains(&e.span.id) {
        let mut e = e;
        let ExprX::Loop { ref mut known_no_back_edge, .. } = Arc::make_mut(&mut e).x else {
            unreachable!();
        };
        *known_no_back_edge = true;
        e
    } else {
        e
    }
}

////// -V alloc-check: charging the implicit drops (see DropCounting)

/// The (name, span) of each variable that the pattern binds
fn pattern_binding_spans(pattern: &Pattern, out: &mut Vec<(VarIdent, Span)>) {
    match &pattern.x {
        PatternX::Var(binding) => out.push((binding.name.clone(), pattern.span.clone())),
        PatternX::Binding { binding, sub_pat } => {
            out.push((binding.name.clone(), pattern.span.clone()));
            pattern_binding_spans(sub_pat, out);
        }
        PatternX::Constructor(_, _, binders) => {
            for b in binders.iter() {
                pattern_binding_spans(&b.a, out);
            }
        }
        PatternX::Or(p1, _) | PatternX::ImmutRef(p1) | PatternX::MutRef(p1) => {
            pattern_binding_spans(p1, out)
        }
        PatternX::Slice(pats) => {
            for p in pats.iter() {
                pattern_binding_spans(p, out);
            }
        }
        PatternX::Wildcard | PatternX::Expr(_) | PatternX::Range(..) => {}
    }
}

/// Initialization of a place for the drop analysis: may it be initialized, and may it be
/// uninitialized? (A drop point ends the life of the place, unlike for the resolution analysis.)
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct DropInit {
    can_be_uninit: bool,
    can_be_init: bool,
}

struct DropInitConst {
    place: FlattenedPlace,
    /// For each drop point: the place whose life it ends (a scope end), if any
    ends: Arc<Vec<Option<FlattenedPlace>>>,
}

impl DataflowState for DropInit {
    type Const = DropInitConst;

    fn join(&mut self, b: &Self) {
        *self = DropInit {
            can_be_uninit: self.can_be_uninit || b.can_be_uninit,
            can_be_init: self.can_be_init || b.can_be_init,
        };
    }

    // forward transfer
    fn transfer(&self, instr: &Instruction, c: &DropInitConst) -> Self {
        let uninit = DropInit { can_be_uninit: true, can_be_init: false };
        match &instr.kind {
            InstructionKind::MoveFrom(sp) | InstructionKind::DropFrom(sp) => {
                if sp.contains(&c.place) { uninit } else { *self }
            }
            InstructionKind::Overwrite(sp) => {
                if sp.contains(&c.place) {
                    DropInit { can_be_uninit: false, can_be_init: true }
                } else {
                    *self
                }
            }
            InstructionKind::Mutate(_) => *self,
            InstructionKind::ChargedDrop(i) => match &c.ends[*i] {
                Some(sp) if sp.contains(&c.place) => uninit,
                _ => *self,
            },
        }
    }
}

/// -V alloc-check: what the drop points insert into the body
#[derive(Default)]
struct DropInsertions {
    items: HashMap<AstId, DropItems>,
    /// The temporaries whose values the charges read (named as for resolutions)
    temps: HashSet<AstId>,
    /// The drop flags (declared at the start of the body, initially false)
    flags: Vec<VarIdent>,
    /// (the span of the local's binding or temporary's expression, the drop site, whether the
    /// local is a parameter) of each charged drop, for the MIR cross-check
    sites: Vec<(Span, Span, bool)>,
}

/// The statements (charges, drop flag updates) inserted at an AstId, with the named local that
/// each one reads (which must be in scope there)
#[derive(Default)]
struct DropItems {
    befores: Vec<(Expr, Option<VarIdent>)>,
    afters: Vec<(Expr, Option<VarIdent>)>,
    after_args: Vec<(Expr, Option<VarIdent>)>,
    after_f: Vec<(Expr, Option<VarIdent>)>,
    after_t: Vec<(Expr, Option<VarIdent>)>,
    assign_write: Vec<(Expr, Option<VarIdent>)>,
    /// The assignment charges the drop of its whole old value (`charge_drop`)
    charge_assign: bool,
    seen: bool,
}

impl DropInsertions {
    fn push(
        &mut self,
        span: &Span,
        position: AstPosition,
        e: Expr,
        local: Option<VarIdent>,
    ) -> Result<(), VirErr> {
        let (id, which): (AstId, fn(&mut DropItems) -> &mut Vec<(Expr, Option<VarIdent>)>) =
            match position {
                AstPosition::Before(id) => (id, |d| &mut d.befores),
                AstPosition::After(id) => (id, |d| &mut d.afters),
                AstPosition::AfterArguments(id) => (id, |d| &mut d.after_args),
                AstPosition::AfterBool(id, false) => (id, |d| &mut d.after_f),
                AstPosition::AfterBool(id, true) => (id, |d| &mut d.after_t),
                AstPosition::BeforeAssignWrite(id) => (id, |d| &mut d.assign_write),
                // (only normal returns are counted)
                AstPosition::OnUnwind(_) => return Ok(()),
                AstPosition::AfterTempAssignment(_) | AstPosition::MatchIntermediate => {
                    return Err(error(
                        span,
                        "-V alloc-check: Verus cannot count this drop yet (a value that is moved on some paths only, in a position Verus cannot follow); move or drop the value explicitly on every path",
                    ));
                }
            };
        which(self.items.entry(id).or_default()).push((e, local));
        Ok(())
    }
}

/// May dropping a value of this type run drop glue? (false only when it certainly does not;
/// the MIR cross-check catches a drop that this misses)
fn typ_may_need_drop(
    typ: &Typ,
    datatypes: &HashMap<Path, Datatype>,
    no_drop_closures: &HashSet<usize>,
) -> bool {
    let rec = |t: &Typ| typ_may_need_drop(t, datatypes, no_drop_closures);
    match &**typ {
        TypX::AnonymousClosure(_, _, _, id) => !no_drop_closures.contains(id),
        TypX::Bool | TypX::Int(_) | TypX::Real | TypX::Float(_) | TypX::FnDef(..) => false,
        TypX::MutRef(_) => false,
        TypX::Decorate(dec, _, _) => match dec {
            TypDecoration::Ref
            | TypDecoration::Ghost
            | TypDecoration::Tracked
            | TypDecoration::Never
            | TypDecoration::ConstPtr => false,
            TypDecoration::Box | TypDecoration::Rc | TypDecoration::Arc => true,
        },
        TypX::Primitive(prim, typs) => match prim {
            crate::ast::Primitive::Array | crate::ast::Primitive::Slice => rec(&typs[0]),
            crate::ast::Primitive::StrSlice
            | crate::ast::Primitive::Ptr
            | crate::ast::Primitive::Global => false,
        },
        TypX::Datatype(Dt::Tuple(_), typs, _) => typs.iter().any(|t| rec(t)),
        TypX::Datatype(Dt::Path(path), typs, _) => {
            let Some(datatype) = datatypes.get(path) else {
                return true;
            };
            // (rustc's components of its drop glue, see DatatypeX::drop_glue)
            let Some(components) = &datatype.x.drop_glue else {
                return true;
            };
            let substs: HashMap<Ident, Typ> = datatype
                .x
                .typ_params
                .iter()
                .map(|(x, _)| x.clone())
                .zip(typs.iter().cloned())
                .collect();
            components.iter().any(|c| rec(&crate::sst_util::subst_typ(&substs, c)))
        }
        _ => true,
    }
}

/// The IsVariant conditions under which the place exists
fn place_variant_conditions(
    place: &Place,
    datatypes: &HashMap<Path, Datatype>,
    out: &mut Vec<Expr>,
) {
    match &place.x {
        PlaceX::Local(_) => {}
        PlaceX::DerefMut(p) | PlaceX::Index(p, _, ArrayKind::Array, _) => {
            place_variant_conditions(p, datatypes, out)
        }
        PlaceX::Field(field_opr, p) => {
            place_variant_conditions(p, datatypes, out);
            let is_irref = match &field_opr.datatype {
                Dt::Tuple(_) => true,
                Dt::Path(path) => datatypes[path].x.variants.len() == 1,
            };
            if !is_irref {
                let e0 = crate::ast_util::place_to_spec_expr(p);
                let is_variantx = ExprX::UnaryOpr(
                    UnaryOpr::IsVariant {
                        datatype: field_opr.datatype.clone(),
                        variant: field_opr.variant.clone(),
                    },
                    e0,
                );
                out.push(SpannedTyped::new(&place.span, &bool_typ(), is_variantx));
            }
        }
        _ => panic!("place_variant_conditions got unexpected Place kind"),
    }
}

/// `ChargeDeallocations(if conds { drop_deallocations(place) } else { 0 })`
fn mk_drop_charge(span: &Span, place: &Place, conds: Vec<Expr>) -> Expr {
    let nat = Arc::new(TypX::Int(crate::ast::IntRange::Nat));
    let call_target_attrs = crate::ast::CallTargetAttrs {
        autospec: crate::ast::AutospecUsage::Final,
        const_var: false,
        assume_external_allowed: false,
        trusted_call: false,
        into_forward: None,
    };
    let value = crate::ast_util::place_to_spec_expr(place);
    let call = ExprX::Call {
        target: crate::ast::CallTarget::Fun(
            crate::ast::CallTargetKind::Static,
            crate::def::fn_drop_deallocations(),
            Arc::new(vec![place.typ.clone()]),
            Arc::new(vec![]),
            call_target_attrs,
        ),
        args: Arc::new(vec![value]),
        post_args: None,
        body: None,
    };
    let mut n = SpannedTyped::new(span, &nat, call);
    if conds.len() > 0 {
        let cond = crate::ast_util::conjoin(span, &conds);
        let zero = SpannedTyped::new(
            span,
            &nat,
            ExprX::Const(crate::ast::Constant::Int(num_bigint::BigInt::from(0))),
        );
        n = SpannedTyped::new(span, &nat, ExprX::If(cond, n, Some(zero)));
    }
    SpannedTyped::new(span, &unit_typ(), ExprX::ChargeDeallocations(n))
}

fn mk_flag_assign(span: &Span, flag: &VarIdent, b: bool) -> Expr {
    let place = SpannedTyped::new(span, &bool_typ(), PlaceX::Local(flag.clone()));
    SpannedTyped::new(
        span,
        &unit_typ(),
        ExprX::Assign {
            place,
            rhs: mk_bool(span, b),
            op: None,
            resolve: false,
            typ: bool_typ(),
            charge_drop: false,
        },
    )
}

impl<'a> LocalCollection<'a> {
    /// The leaf is an exec-mode part of an exec-mode local, which may need dropping
    fn drop_leaf_needs_charge(&self, leaf: &FlattenedPlace) -> bool {
        let local = &self.locals[leaf.local];
        let mode = match &local.name {
            LocalName::Named(x) => self.var_modes.get(x).copied(),
            LocalName::Temporary(id, _) => self.temporary_modes.get(id).copied(),
        };
        if mode != Some(Mode::Exec) {
            return false;
        }
        let mut tree = &local.tree;
        for projection in leaf.projections.iter() {
            match (projection, tree) {
                (Projection::StructField((v, f)), PlaceTree::Struct(_, dt, trees)) => {
                    if let Dt::Path(path) = dt {
                        if self.datatypes[path].x.variants[*v].fields[*f].a.1 != Mode::Exec {
                            return false;
                        }
                    }
                    tree = trees[*v][*f].as_ref().unwrap();
                }
                (Projection::DerefMut, PlaceTree::MutRef(_, inner)) => tree = inner,
                (Projection::Index(i), PlaceTree::Array(_, trees)) => tree = &trees[*i],
                _ => unreachable!(),
            }
        }
        typ_may_need_drop(tree.typ(), self.datatypes, &self.no_drop_closures)
    }
}

/// Compute the charges of the drop points (and the drop flags they need)
fn drop_insertions(cfg: &CFG, dc: &DropCounting) -> Result<DropInsertions, VirErr> {
    let mut out = DropInsertions::default();
    let leaves = cfg.locals.places_skip_insides_of_mut_refs();
    let ends: Arc<Vec<Option<FlattenedPlace>>> = Arc::new(
        dc.drops
            .iter()
            .map(|d| match &d.kind {
                DropKind::ScopeEnd(fp) => Some(fp.clone()),
                _ => None,
            })
            .collect(),
    );
    let local_span = |local: usize| -> (Span, bool) {
        let name = &cfg.locals.locals[local].name;
        let span = dc.local_spans.get(name).cloned().unwrap_or_else(|| dc.body_span.clone());
        let is_param = matches!(name, LocalName::Named(x) if dc.params.contains(x));
        (span, is_param)
    };
    let named = |local: usize| -> Option<VarIdent> {
        match &cfg.locals.locals[local].name {
            LocalName::Named(x) => Some(x.clone()),
            LocalName::Temporary(..) => None,
        }
    };

    // Which leaves each drop point charges, and whether under a flag
    let mut analyses: HashMap<usize, DataflowOutput<DropInit>> = HashMap::new();
    let mut charges: Vec<Vec<(usize, bool)>> = vec![];
    let mut flagged: HashSet<usize> = HashSet::new();
    for d in dc.drops.iter() {
        let mut c = vec![];
        if let DropKind::ScopeEnd(fp) | DropKind::Assign(fp) = &d.kind {
            for (li, leaf) in leaves.iter().enumerate() {
                if !fp.contains(leaf) || !cfg.locals.drop_leaf_needs_charge(leaf) {
                    continue;
                }
                if cfg.locals.box_split.contains(&leaf.local) {
                    return Err(error(
                        &d.site,
                        "-V alloc-check: Verus cannot count the drop of a box whose contents were moved out (in part) yet",
                    ));
                }
                let analysis = analyses.entry(li).or_insert_with(|| {
                    do_dataflow::<DropInit>(
                        cfg,
                        DropInit { can_be_uninit: false, can_be_init: false },
                        DropInit { can_be_uninit: true, can_be_init: false },
                        &DropInitConst { place: leaf.clone(), ends: ends.clone() },
                        Direction::Forward,
                    )
                });
                let st = analysis.output[d.loc.0][d.loc.1];
                if !st.can_be_init {
                    continue;
                }
                if st.can_be_uninit {
                    if cfg.locals.locals[leaf.local].name.is_temp() {
                        return Err(error(
                            &d.site,
                            "-V alloc-check: Verus cannot count the drop of a temporary value that is moved on some paths only yet",
                        ));
                    }
                    flagged.insert(li);
                }
                c.push((li, st.can_be_uninit));
            }
        }
        charges.push(c);
    }
    let mut flags: HashMap<usize, VarIdent> = HashMap::new();
    let mut flagged: Vec<usize> = flagged.into_iter().collect();
    flagged.sort();
    for li in flagged.iter() {
        let x = VarIdent(
            str_ident("drop_flag"),
            VarIdentDisambiguate::ResInfTemp(cfg.locals.next_temp_id + *li as u64),
        );
        out.flags.push(x.clone());
        flags.insert(*li, x);
    }

    let set_flags = |out: &mut DropInsertions,
                     sp: &FlattenedPlace,
                     b: bool,
                     span: &Span,
                     position: AstPosition|
     -> Result<(), VirErr> {
        for li in flagged.iter() {
            if sp.contains(&leaves[*li]) {
                let e = mk_flag_assign(span, &flags[li], b);
                out.push(span, position, e, None)?;
            }
        }
        Ok(())
    };

    // In the order of the instructions: the charges and the drop flag updates
    for bb in cfg.basic_blocks.iter() {
        for instr in bb.instructions.iter() {
            let position = instr.post_instruction_position;
            match &instr.kind {
                InstructionKind::Overwrite(sp) => {
                    set_flags(&mut out, sp, true, &dc.body_span, position)?;
                }
                InstructionKind::MoveFrom(sp) | InstructionKind::DropFrom(sp) => {
                    set_flags(&mut out, sp, false, &dc.body_span, position)?;
                }
                InstructionKind::Mutate(_) => {}
                InstructionKind::ChargedDrop(i) => {
                    let d = &dc.drops[*i];
                    match &d.kind {
                        DropKind::ScopeEnd(fp) | DropKind::Assign(fp) => {
                            if charges[*i].len() > 0 {
                                let (span, is_param) = local_span(fp.local);
                                out.sites.push((span, d.site.clone(), is_param));
                            }
                            for (li, under_flag) in charges[*i].iter() {
                                let leaf = &leaves[*li];
                                let place = cfg.locals.to_ast_place(&d.site, leaf);
                                let mut conds = vec![];
                                if *under_flag {
                                    let flag = SpannedTyped::new(
                                        &d.site,
                                        &bool_typ(),
                                        ExprX::Var(flags[li].clone()),
                                    );
                                    conds.push(flag);
                                }
                                place_variant_conditions(&place, &cfg.locals.datatypes, &mut conds);
                                let e = mk_drop_charge(&d.site, &place, conds);
                                if let LocalName::Temporary(id, _) =
                                    &cfg.locals.locals[leaf.local].name
                                {
                                    out.temps.insert(*id);
                                }
                                out.push(&d.site, d.position, e, named(leaf.local))?;
                            }
                            if let DropKind::ScopeEnd(fp) = &d.kind {
                                set_flags(&mut out, fp, false, &d.site, position)?;
                            }
                        }
                        DropKind::AssignWhole(fp) | DropKind::AssignUntracked(fp) => {
                            // (charged by the assignment itself, from the old value it reads
                            // after evaluating the place)
                            let AstPosition::BeforeAssignWrite(id) = d.position else {
                                unreachable!()
                            };
                            out.items.entry(id).or_default().charge_assign = true;
                            let (span, is_param) = local_span(fp.local);
                            out.sites.push((span, d.site.clone(), is_param));
                        }
                    }
                }
            }
        }
    }
    Ok(out)
}
