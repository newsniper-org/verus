#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Differential check of `allocates` bounds against the compiled program (-V alloc-check).
//
// An `allocates e` bound is a claim about the source program (the Rust abstract machine): an
// upper bound on the calls to the allocator that obtain memory (`alloc`, `alloc_zeroed`,
// `realloc`; `dealloc` is not counted) during one call that returns normally. The compiler is
// documented to be free to *remove* or *merge* such calls (LLVM LangRef's allocation elision and
// realloc splitting; std's "The allocator may ... elide or merge allocations", Rust #159720), which
// can only lower the count; no current document allows or forbids it to *introduce* calls.
//
// These tests verify programs whose checked functions have numeric bounds, compile them at
// several optimization levels with a counting `#[global_allocator]`, run them, and compare the
// counts each call actually made with its verified bound. A count above the bound would mean a
// specification in vstd is wrong or the compiler introduced an allocator call. They also run a
// user allocator, and an allocator with a state, through std's containers, and count the
// deallocations of `#[verifier::fip]` functions (which must make none).

const COUNTING_PRELUDE: &str = r#"
use std::sync::atomic::{AtomicUsize, Ordering};
struct Counting;
static COUNT: AtomicUsize = AtomicUsize::new(0);
// (deallocations, for `#[verifier::fip]`: `dealloc`, and the old block of a `realloc`)
static FREES: AtomicUsize = AtomicUsize::new(0);
unsafe impl std::alloc::GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: std::alloc::Layout) -> *mut u8 {
        COUNT.fetch_add(1, Ordering::SeqCst);
        unsafe { std::alloc::System.alloc(l) }
    }
    unsafe fn alloc_zeroed(&self, l: std::alloc::Layout) -> *mut u8 {
        COUNT.fetch_add(1, Ordering::SeqCst);
        unsafe { std::alloc::System.alloc_zeroed(l) }
    }
    unsafe fn realloc(&self, p: *mut u8, l: std::alloc::Layout, n: usize) -> *mut u8 {
        COUNT.fetch_add(1, Ordering::SeqCst);
        FREES.fetch_add(1, Ordering::SeqCst);
        unsafe { std::alloc::System.realloc(p, l, n) }
    }
    unsafe fn dealloc(&self, p: *mut u8, l: std::alloc::Layout) {
        FREES.fetch_add(1, Ordering::SeqCst);
        unsafe { std::alloc::System.dealloc(p, l) }
    }
}
#[global_allocator]
static GLOBAL: Counting = Counting;

// Runs `f` and prints how many allocator calls it made next to its verified bound
fn measure<R>(name: &str, bound: usize, f: impl FnOnce() -> R) {
    let before = COUNT.load(Ordering::SeqCst);
    let r = std::hint::black_box(f());
    let after = COUNT.load(Ordering::SeqCst);
    // (the result is dropped outside the measured region: the bound covers the call only)
    drop(r);
    println!("ALLOC-CASE {} {} {}", name, after - before, bound);
}

// The same for a `#[verifier::fip]` function, which must also not deallocate
fn measure_fip(name: &str, bound: usize, f: impl FnOnce()) {
    let (before, freed_before) = (COUNT.load(Ordering::SeqCst), FREES.load(Ordering::SeqCst));
    f();
    let (after, freed_after) = (COUNT.load(Ordering::SeqCst), FREES.load(Ordering::SeqCst));
    println!("ALLOC-CASE {} {} {}", name, after - before, bound);
    println!("FIP-CASE {} {}", name, freed_after - freed_before);
}
"#;

const CASES: &str = r#"
use vstd::prelude::*;
use vstd::alloc_check::{AllocFreeDrop, BoundedAllocator, FipAllocator, NoDeallocDrop};
use vstd::alloc_heap::*;
use vstd::atomic_ghost::*;
use vstd::resource::Loc;
use vstd::resource::preorder_auth::Preorder;
use vstd::std_specs::vec::spec_vec_capacity;
use std::alloc::{AllocError, Allocator, Global, Layout};
use std::collections::BTreeMap;
use std::ptr::NonNull;
use std::collections::{HashMap, VecDeque};
use std::rc::Rc;
use std::sync::Arc;

verus! {

fn vec_push_grow() -> (v: Vec<u64>)
    allocates 2
{
    let mut v: Vec<u64> = Vec::with_capacity(2);
    v.push(1);
    v.push(2);
    v.push(3);
    v
}

fn vec_new_push() -> (v: Vec<u64>)
    allocates 1
{
    broadcast use vstd::std_specs::vec::group_vec_axioms;
    let mut v: Vec<u64> = Vec::new();
    v.push(1);
    v
}

fn vec_reserve_then_push(n: u64) -> (v: Vec<u64>)
    allocates 1
{
    let mut v: Vec<u64> = Vec::new();
    v.reserve(4);
    v.push(n);
    v.push(n);
    v.push(n);
    v.push(n);
    v
}

fn vec_drop(v: Vec<Vec<u64>>)
    allocates 0
{
}

fn vec_clear(v: &mut Vec<Vec<u64>>)
    allocates 0
{
    v.clear();
}

fn boxes() -> (r: (Box<u64>, Box<u64>))
    allocates 2
{
    (Box::new(1), Box::new(2))
}

fn rc_new_clone() -> (r: (Rc<u64>, Rc<u64>))
    allocates 1
{
    let a = Rc::new(5);
    let b = a.clone();
    (a, b)
}

fn arc_new_clone() -> (r: (Arc<u64>, Arc<u64>))
    allocates 1
{
    let a = Arc::new(5);
    let b = a.clone();
    (a, b)
}

fn string_push() -> (s: String)
    allocates 2
{
    let mut s = String::new();
    s.push('a');
    s.push_str("bcdefghijklmnopqrstuvwxyz");
    s
}

fn deque_push() -> (d: VecDeque<u64>)
    allocates 2
{
    let mut d: VecDeque<u64> = VecDeque::new();
    d.push_back(1);
    d.push_back(2);
    d
}

fn hash_insert_lookup() -> (m: HashMap<u64, u64>)
    allocates 2
{
    broadcast use vstd::std_specs::hash::group_hash_axioms;
    let mut m: HashMap<u64, u64> = HashMap::new();
    m.insert(1, 10);
    m.insert(2, 20);
    let _b = m.contains_key(&1);
    m
}

fn closure_bounded() -> (r: Box<u64>)
    allocates 1
{
    let c = || -> (r: Box<u64>) allocates 1 { Box::new(7) };
    c()
}

fn loop_allocs(n: usize) -> (r: Vec<Box<usize>>)
    requires n <= 8,
    allocates 1 + n
{
    broadcast use vstd::std_specs::vec::group_vec_axioms;
    let mut v: Vec<Box<usize>> = Vec::with_capacity(8);
    for i in 0..n
        invariant
            v@.len() == i,
            n <= 8,
            allocated() <= 1 + i,
            vstd::std_specs::vec::spec_vec_capacity(&v) >= 8,
    {
        v.push(Box::new(i));
    }
    v
}

// std's growth policy as vstd states it (`vec_amortized_cap`, std 1.100): the verified
// capacities are compared with the compiled program's below
fn cap_after_push_u8() -> (c: usize)
    ensures
        c == 8,
    allocates 1
{
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    v.capacity()
}

fn cap_after_pushes_u64() -> (c: usize)
    ensures
        c == 8,
    allocates 2
{
    let mut v: Vec<u64> = Vec::new();
    v.push(1);
    assert(v.capacity() == 4);
    v.push(2);
    v.push(3);
    v.push(4);
    v.push(5);
    v.capacity()
}

fn cap_after_reserve_u32() -> (c: usize)
    ensures
        c == 10,
    allocates 2
{
    let mut v: Vec<u32> = Vec::new();
    v.push(1);
    v.reserve(9);
    v.capacity()
}

// A user allocator (forwarding to the global one, which is counted)
pub struct Fwd;

impl Clone for Fwd {
    #[verifier::fip]
    fn clone(&self) -> (r: Self)
        allocates 0
    {
        Fwd
    }
}

unsafe impl Allocator for Fwd {
    #[verifier::fip]
    fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>)
        allocates 1
    {
        Global.allocate(layout)
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout)
        allocates 0
    {
        #[verifier::trusted_call] { unsafe { Global.deallocate(ptr, layout) } }
    }
}

unsafe impl AllocFreeDrop for Fwd {}
unsafe impl NoDeallocDrop for Fwd {}
unsafe impl BoundedAllocator for Fwd {
    open spec fn max_cost() -> int { 1 }
}
unsafe impl FipAllocator for Fwd {}

#[verifier::fip]
fn fip_push_spare(v: &mut Vec<u64>)
    requires
        old(v)@.len() < spec_vec_capacity(&*old(v)),
{
    v.push(1);
}

#[verifier::fip]
fn fip_push_empty_fwd(v: &mut Vec<u8, Fwd>)
    requires
        spec_vec_capacity(&*old(v)) == 0,
    allocates 1
{
    v.push(1);
}

// dropping a `BTreeMap` clones its allocator for every node it frees
fn btree_drop_fwd(m: BTreeMap<u8, u8, Fwd>)
    allocates 0
{
}

fn box_zst_fwd() -> (r: Box<(), Fwd>)
    allocates 0
{
    Box::new_in((), Fwd)
}

fn vec_clone_fwd(v: &Vec<u8, Fwd>) -> (r: Vec<u8, Fwd>)
    allocates 1
{
    v.clone()
}

// An allocator with a state: a pool that hands out `remaining` blocks from a chunk it already
// holds (standing in for an arena: `from_chunk` uses the system allocator, which the counting
// global allocator does not see), and then asks the global allocator. Its costs depend on the
// state (`vstd::alloc_heap::StatefulAllocator`).
pub struct Free(pub nat);
impl Preorder for Free {
    open spec fn le(self, other: Self) -> bool { self.0 <= other.0 }
    proof fn le_refl(a: Self) {}
    proof fn le_trans(a: Self, b: Self, c: Self) {}
}

pub struct PoolPred;
impl AtomicInvariantPredicate<Loc, u64, AllocAuth<Free>> for PoolPred {
    open spec fn atomic_inv(k: Loc, v: u64, g: AllocAuth<Free>) -> bool {
        g@ == Free(v as nat) && g.id() == k
    }
}

pub struct Pool {
    remaining: AtomicU64<Loc, AllocAuth<Free>, PoolPred>,
    reg: Tracked<Registered<Free>>,
}

impl Pool {
    #[verifier::type_invariant]
    spec fn inv(&self) -> bool {
        self.remaining.well_formed() && self.remaining.constant() == self.reg@.loc()
    }

    pub closed spec fn id(&self) -> Loc { self.reg@.loc() }

    fn new(n: u64) -> (p: Self)
        ensures
            allocator_heap() == heap_register::<Free>(old_allocator_heap(), p.id(), Free(n as nat)),
        allocates 0
    {
        let tracked (auth, reg) = AllocAuth::register(Free(n as nat));
        let ghost l = reg.loc();
        let remaining = AtomicU64::new(Ghost(l), n, Tracked(auth));
        Pool { remaining, reg: Tracked(reg) }
    }
}

#[verifier::external_body]
fn from_chunk(layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>)
    ensures vstd::std_specs::rust_1_100::allocator_block_fits(r, layout),
    allocates 0
{
    std::alloc::System.allocate(layout)
}

unsafe impl Allocator for Pool {
    fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>)
        allocates 1
    {
        proof { use_type_invariant(self); }
        let tracked reg = self.reg.borrow();
        let ghost s = heap_state::<Free>(allocator_heap(), reg.loc());
        let v = atomic_with_ghost!(&self.remaining => load(); ghost g => {
            g.lower_bound(reg);
        });
        if v > 0 {
            atomic_with_ghost!(&self.remaining => store(v - 1); ghost g => {
                g.step(reg, Free((v - 1) as nat), if s.0 > 0 { Free((s.0 - 1) as nat) } else { s });
            });
            from_chunk(layout)
        } else {
            Global.allocate(layout)
        }
    }

    // (blocks are not returned: the memory of the chunk and of the global allocator would have
    // to be told apart)
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout)
        allocates 0
    {
    }
}

unsafe impl AllocFreeDrop for Pool {}

unsafe impl BoundedAllocator for Pool {
    open spec fn max_cost() -> int { 1 }
}

unsafe impl StatefulAllocator for Pool {
    type State = Free;

    open spec fn loc(&self) -> Loc { self.id() }

    proof fn witness<'a>(tracked &'a self) -> (tracked w: &'a Registered<Free>) {
        self.reg.borrow()
    }

    open spec fn allocate_cost_at(&self, s: Free, layout: Layout) -> int {
        if s.0 > 0 { 0 } else { 1 }
    }

    open spec fn allocate_next(&self, s: Free, layout: Layout, r: Result<NonNull<[u8]>, AllocError>) -> Free {
        if s.0 > 0 { Free((s.0 - 1) as nat) } else { s }
    }
}

// two boxes come from the pool, the third from the global allocator
fn pool_boxes() -> (r: u64)
    allocates 1
{
    let p = Pool::new(2);
    let a = Box::new_in(1u64, &p);
    let b = Box::new_in(2u64, &p);
    let c = Box::new_in(3u64, &p);
    *a + *b + *c
}

// an empty pool: every box comes from the global allocator
fn pool_empty_boxes() -> (r: u64)
    allocates 2
{
    let p = Pool::new(0);
    let a = Box::new_in(1u64, &p);
    let b = Box::new_in(2u64, &p);
    *a + *b
}

fn main() {
}

} // verus!

unsafe impl core::alloc::AllocatorClone for Fwd {}

#[verifier::external]
fn run_cases() {
    let mut v0: Vec<u64> = Vec::with_capacity(4);
    measure_fip("fip_push_spare", 0, || fip_push_spare(&mut v0));
    let mut v1: Vec<u8, Fwd> = Vec::new_in(Fwd);
    measure_fip("fip_push_empty_fwd", 1, || fip_push_empty_fwd(&mut v1));
    let mut m = BTreeMap::new_in(Fwd);
    for i in 0..100u8 {
        m.insert(i, i);
    }
    measure("btree_drop_fwd", 0, || btree_drop_fwd(m));
    measure("box_zst_fwd", 0, || box_zst_fwd());
    let mut w: Vec<u8, Fwd> = Vec::new_in(Fwd);
    w.push(1);
    w.push(2);
    measure("vec_clone_fwd", 1, || vec_clone_fwd(&w));
    measure("pool_boxes", 1, || pool_boxes());
    measure("pool_empty_boxes", 2, || pool_empty_boxes());
    measure("vec_push_grow", 2, || vec_push_grow());
    measure("vec_new_push", 1, || vec_new_push());
    measure("vec_reserve_then_push", 1, || vec_reserve_then_push(3));
    let vv = vec![vec![1u64; 4]; 4];
    measure("vec_drop", 0, || vec_drop(vv));
    let mut vv2 = vec![vec![1u64; 4]; 4];
    measure("vec_clear", 0, || vec_clear(&mut vv2));
    measure("boxes", 2, || boxes());
    measure("rc_new_clone", 1, || rc_new_clone());
    measure("arc_new_clone", 1, || arc_new_clone());
    measure("string_push", 2, || string_push());
    measure("deque_push", 2, || deque_push());
    measure("hash_insert_lookup", 2, || hash_insert_lookup());
    measure("closure_bounded", 1, || closure_bounded());
    measure("loop_allocs", 1 + 8, || loop_allocs(8));
    println!("CAP-CASE cap_after_push_u8 {} 8", cap_after_push_u8());
    println!("CAP-CASE cap_after_pushes_u64 {} 8", cap_after_pushes_u64());
    println!("CAP-CASE cap_after_reserve_u32 {} 10", cap_after_reserve_u32());
}
"#;

fn run_at(opt_level: &str) {
    let tempdir = tempfile::TempDir::new().expect("temp dir");
    let entry_file = tempdir.path().join("cases.rs");
    // (`fn main` comes from `verus!`, so `run_cases` is called from a second, external `main`
    // in a module-level wrapper: replace the empty verified `main`)
    let cases = CASES.replace("fn main() {\n}", "#[verifier::external] fn main() { run_cases() }");
    let code = format!(
        "{}\n#![feature(btreemap_alloc)]\n{}\n{}\n",
        FEATURE_PRELUDE, COUNTING_PRELUDE, cases
    );
    std::fs::write(&entry_file, code).expect("write source file");
    let opt = format!("opt-level={}", opt_level);
    let output = run_verus_raw(
        &["-V", "alloc-check", "--compile", "-C", &opt, entry_file.to_str().unwrap()],
        tempdir.path(),
    );
    assert!(
        output.status.success(),
        "verus failed (opt-level={opt_level}):\n{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let exe = tempdir.path().join(if cfg!(target_os = "windows") { "cases.exe" } else { "cases" });
    let run = std::process::Command::new(&exe).output().expect("run compiled cases");
    assert!(run.status.success(), "cases failed:\n{}", String::from_utf8_lossy(&run.stderr));
    let stdout = String::from_utf8_lossy(&run.stdout);
    let mut n = 0;
    let mut caps = 0;
    let mut fips = 0;
    for line in stdout.lines() {
        if let Some(rest) = line.strip_prefix("FIP-CASE ") {
            let parts: Vec<&str> = rest.split_whitespace().collect();
            assert_eq!(
                parts[1], "0",
                "{} (opt-level={}): {} deallocations, but it verified as `#[verifier::fip]`",
                parts[0], opt_level, parts[1]
            );
            fips += 1;
            continue;
        }
        if let Some(rest) = line.strip_prefix("CAP-CASE ") {
            let parts: Vec<&str> = rest.split_whitespace().collect();
            assert_eq!(
                parts[1], parts[2],
                "{} (opt-level={}): capacity {}, but vstd's growth policy says {} (did std's `RawVec` growth change?)",
                parts[0], opt_level, parts[1], parts[2]
            );
            caps += 1;
            continue;
        }
        let Some(rest) = line.strip_prefix("ALLOC-CASE ") else { continue };
        let parts: Vec<&str> = rest.split_whitespace().collect();
        let (name, observed, bound): (&str, usize, usize) =
            (parts[0], parts[1].parse().unwrap(), parts[2].parse().unwrap());
        assert!(
            observed <= bound,
            "{} (opt-level={}): {} allocator calls, but verified `allocates {}`",
            name,
            opt_level,
            observed,
            bound
        );
        n += 1;
    }
    assert_eq!(n, 20, "expected 20 cases, got:\n{}", stdout);
    assert_eq!(fips, 2, "expected 2 fip cases, got:\n{}", stdout);
    assert_eq!(caps, 3, "expected 3 capacity cases, got:\n{}", stdout);
}

#[test]
fn alloc_check_runtime_opt0() {
    run_at("0");
}

#[test]
fn alloc_check_runtime_opt3() {
    run_at("3");
}

// `#[verifier::fip(strict)]` relies on `become` (`explicit_tail_calls`) for constant stack space:
// a verified tail-recursive function runs 10^8 levels deep, which overflows the stack unless
// each call replaces the caller's frame, at every optimization level (an ordinary tail call is
// not eliminated at opt-level=0, nor at opt-level=3 when a drop is pending after it)
const TAIL_CALLS: &str = r#"
use vstd::prelude::*;

verus! {

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

fn main() {
}

} // verus!

#[verifier::external]
fn run_cases() {
    println!("TAIL-CASE sum {}", sum(100_000_000, 0));
    println!("TAIL-CASE even {}", even(100_000_001));
}
"#;

fn run_tail_calls_at(opt_level: &str) {
    let tempdir = tempfile::TempDir::new().expect("temp dir");
    let entry_file = tempdir.path().join("tails.rs");
    let cases =
        TAIL_CALLS.replace("fn main() {\n}", "#[verifier::external] fn main() { run_cases() }");
    // (`explicit_tail_calls` is in the prelude)
    let code = format!("{}\n{}\n", FEATURE_PRELUDE, cases);
    std::fs::write(&entry_file, code).expect("write source file");
    let opt = format!("opt-level={}", opt_level);
    let output = run_verus_raw(
        &["-V", "alloc-check", "--compile", "-C", &opt, entry_file.to_str().unwrap()],
        tempdir.path(),
    );
    assert!(
        output.status.success(),
        "verus failed (opt-level={opt_level}):\n{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let exe = tempdir.path().join(if cfg!(target_os = "windows") { "tails.exe" } else { "tails" });
    let run = std::process::Command::new(&exe).output().expect("run compiled cases");
    assert!(run.status.success(), "tail calls failed:\n{}", String::from_utf8_lossy(&run.stderr));
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(stdout.contains("TAIL-CASE sum 5000000050000000"), "{}", stdout);
    assert!(stdout.contains("TAIL-CASE even false"), "{}", stdout);
}

#[test]
fn fip_strict_tail_calls_opt0() {
    run_tail_calls_at("0");
}

#[test]
fn fip_strict_tail_calls_opt3() {
    run_tail_calls_at("3");
}

// `-V fip-lint=fix` rewrites recursion modulo a constructor into a loop (direct and mutual
// recursion, tuple and struct constructors, different result types); the rewritten functions
// verify as `#[verifier::fip(strict)]` and run 10^6 levels deep, which overflows the stack when
// each level is a call
const TRMC: &str = r#"
use vstd::prelude::*;

verus! {

pub enum List { Nil, Cons(u64, Box<List>) }
pub enum A { End, Node(u64, Box<B>) }
pub enum B { End, Node { val: u64, next: Box<A> } }

pub open spec fn len(l: List) -> nat decreases l {
    match l { List::Nil => 0, List::Cons(_, t) => 1 + len(*t) }
}
pub open spec fn half(l: List) -> List decreases l {
    match l { List::Nil => List::Nil, List::Cons(x, t) => List::Cons(x / 2, Box::new(half(*t))) }
}
pub open spec fn to_a(l: List) -> A decreases l {
    match l { List::Nil => A::End, List::Cons(x, t) => A::Node(x, Box::new(to_b(*t))) }
}
pub open spec fn to_b(l: List) -> B decreases l {
    match l { List::Nil => B::End, List::Cons(x, t) => B::Node { val: x, next: Box::new(to_a(*t)) } }
}

#[verifier::fip]
fn half_rec(l: &List) -> (r: List)
    ensures r == half(*l)
    decreases l
    allocates len(*l)
{
    match l {
        List::Nil => List::Nil,
        List::Cons(x, xs) => List::Cons(*x / 2, Box::new(half_rec(xs))),
    }
}

#[verifier::fip]
fn to_a_rec(l: &List) -> (r: A)
    ensures r == to_a(*l)
    decreases l
    allocates len(*l)
{
    match l {
        List::Nil => A::End,
        List::Cons(x, xs) => A::Node(*x, Box::new(to_b_rec(xs))),
    }
}

#[verifier::fip]
fn to_b_rec(l: &List) -> (r: B)
    ensures r == to_b(*l)
    decreases l
    allocates len(*l)
{
    match l {
        List::Nil => B::End,
        List::Cons(x, xs) => B::Node { val: *x, next: Box::new(to_a_rec(xs)) },
    }
}

fn main() {
}

} // verus!

#[verifier::external]
fn build(n: u64) -> List {
    let mut l = List::Nil;
    for i in 0..n {
        l = List::Cons(2 * i + 1, Box::new(l));
    }
    l
}

#[verifier::external]
fn sum(l: &List) -> u64 {
    let (mut s, mut cur) = (0, l);
    while let List::Cons(x, t) = cur {
        s += x;
        cur = t;
    }
    s
}

#[verifier::external]
fn count_a(a: &A) -> u64 {
    let (mut n, mut cur) = (0, a);
    loop {
        match cur {
            A::End => return n,
            A::Node(_, b) => match &**b {
                B::End => return n + 1,
                B::Node { next, .. } => {
                    n += 2;
                    cur = next;
                }
            },
        }
    }
}

#[verifier::external]
fn run_cases() {
    let l = build(1_000_000);
    let h = half_rec(&l);
    println!("TRMC-CASE half {}", sum(&h));
    let a = to_a_rec(&l);
    println!("TRMC-CASE to_a {}", count_a(&a));
    // (dropping a list this long recurses in its drop glue)
    std::mem::forget((l, h, a));
}
"#;

fn run_trmc_fix_at(opt_level: &str) {
    let tempdir = tempfile::TempDir::new().expect("temp dir");
    let entry_file = tempdir.path().join("trmc.rs");
    let cases = TRMC.replace("fn main() {\n}", "#[verifier::external] fn main() { run_cases() }");
    std::fs::write(&entry_file, format!("{}\n{}\n", FEATURE_PRELUDE, cases)).expect("write");
    let output = run_verus_raw(
        &["-V", "alloc-check", "-V", "fip-lint=fix", entry_file.to_str().unwrap()],
        tempdir.path(),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "verus -V fip-lint=fix failed:\n{}", stderr);
    assert!(stderr.contains("rewrote `trmc::half_rec` into a loop"), "{}", stderr);
    assert!(
        stderr.contains("rewrote `trmc::to_a_rec`, `trmc::to_b_rec` into a loop"),
        "{}",
        stderr
    );
    let fixed = std::fs::read_to_string(&entry_file).expect("read");
    assert!(
        fixed.contains("'__trmc: loop") && fixed.contains("fn to_a_rec_to_b_rec_trmc"),
        "{}",
        fixed
    );
    // the rewritten functions use constant stack space
    let strict = fixed.replace("#[verifier::fip]", "#[verifier::fip(strict)]");
    std::fs::write(&entry_file, strict).expect("write");
    let opt = format!("opt-level={}", opt_level);
    let output = run_verus_raw(
        &["-V", "alloc-check", "--compile", "-C", &opt, entry_file.to_str().unwrap()],
        tempdir.path(),
    );
    assert!(
        output.status.success(),
        "verus failed on the rewritten code (opt-level={opt_level}):\n{}\n{}",
        String::from_utf8_lossy(&output.stderr),
        fixed
    );
    let exe = tempdir.path().join(if cfg!(target_os = "windows") { "trmc.exe" } else { "trmc" });
    let run = std::process::Command::new(&exe).output().expect("run compiled cases");
    assert!(
        run.status.success(),
        "rewritten code failed:\n{}",
        String::from_utf8_lossy(&run.stderr)
    );
    let stdout = String::from_utf8_lossy(&run.stdout);
    // sum of (2i+1)/2 = i for i < 10^6
    assert!(stdout.contains("TRMC-CASE half 499999500000"), "{}", stdout);
    assert!(stdout.contains("TRMC-CASE to_a 1000000"), "{}", stdout);
}

#[test]
fn fip_trmc_fix_opt0() {
    run_trmc_fix_at("0");
}

#[test]
fn fip_trmc_fix_opt3() {
    run_trmc_fix_at("3");
}

const RANGE: &str = r#"
use vstd::prelude::*;
verus! {
pub enum List { Nil, Cons(u64, Box<List>) }
pub open spec fn len(l: List) -> nat decreases l {
    match l { List::Nil => 0, List::Cons(_, t) => 1 + len(*t) }
}
fn range(n: u64) -> (r: List)
    ensures len(r) == n
    decreases n
{
    if n == 0 { List::Nil } else { List::Cons(n, Box::new(range(n - 1))) }
}
fn main() { }
}
"#;

// `-V fip-lint=fix` rewrites a file in place: through a symbolic link, keeping hard links and
// the file's mode; it leaves a read-only file and a file with CRLF line endings alone; a journal
// next to the crate root (also listing backups outside it) keeps a second run from starting
// (portable-fip, fip-beta 3eb69f3c3, §2)
#[cfg(unix)]
#[test]
fn fip_trmc_fix_files() {
    use std::os::unix::fs::{MetadataExt, PermissionsExt};
    let tempdir = tempfile::TempDir::new().expect("temp dir");
    let dir = tempdir.path();
    let src = format!("{}\n{}\n", FEATURE_PRELUDE, RANGE);
    let fix = |file: &str| {
        let out = run_verus_raw(&["-V", "fip-lint=fix", file], dir);
        String::from_utf8_lossy(&out.stderr).to_string()
    };
    let rewritten = |p: &std::path::Path| std::fs::read_to_string(p).unwrap().contains("'__trmc");
    // a symbolic link: the file it points to is rewritten, the link stays
    std::fs::create_dir(dir.join("real")).unwrap();
    std::fs::write(dir.join("real/t.rs"), &src).unwrap();
    std::os::unix::fs::symlink("real/t.rs", dir.join("link.rs")).unwrap();
    let e = fix("link.rs");
    assert!(e.contains("rewrote `link::range` into a loop"), "{}", e);
    assert!(std::fs::symlink_metadata(dir.join("link.rs")).unwrap().file_type().is_symlink());
    assert!(rewritten(&dir.join("real/t.rs")));
    // a hard link and the mode stay
    std::fs::write(dir.join("h.rs"), &src).unwrap();
    std::fs::hard_link(dir.join("h.rs"), dir.join("h2.rs")).unwrap();
    std::fs::set_permissions(dir.join("h.rs"), std::fs::Permissions::from_mode(0o640)).unwrap();
    let e = fix("h.rs");
    assert!(e.contains("rewrote `h::range` into a loop"), "{}", e);
    let (m1, m2) = (
        std::fs::metadata(dir.join("h.rs")).unwrap(),
        std::fs::metadata(dir.join("h2.rs")).unwrap(),
    );
    assert_eq!(m1.ino(), m2.ino());
    assert_eq!(m1.mode() & 0o777, 0o640);
    assert!(rewritten(&dir.join("h2.rs")));
    // a read-only file is left alone
    std::fs::write(dir.join("ro.rs"), &src).unwrap();
    std::fs::set_permissions(dir.join("ro.rs"), std::fs::Permissions::from_mode(0o440)).unwrap();
    let e = fix("ro.rs");
    assert!(e.contains("cannot be written"), "{}", e);
    assert!(!rewritten(&dir.join("ro.rs")));
    // CRLF line endings
    std::fs::write(dir.join("crlf.rs"), src.replace('\n', "\r\n")).unwrap();
    let e = fix("crlf.rs");
    assert!(e.contains("CRLF line endings"), "{}", e);
    assert!(!rewritten(&dir.join("crlf.rs")));
    // nothing is left behind
    let left: Vec<String> = std::fs::read_dir(dir)
        .unwrap()
        .flatten()
        .map(|e| e.file_name().to_string_lossy().to_string())
        .filter(|n| n.contains("fip-lint"))
        .collect();
    assert!(left.is_empty(), "{:?}", left);
    // a journal (of a run that was interrupted, or is running) stops a new run
    std::fs::write(dir.join("j.rs"), &src).unwrap();
    std::fs::write(dir.join(".fip-lint-journal"), "/elsewhere/x.rs.fip-lint-orig\n").unwrap();
    let out = run_verus_raw(&["-V", "fip-lint=fix", "j.rs"], dir);
    let e = String::from_utf8_lossy(&out.stderr);
    assert!(!out.status.success(), "{}", e);
    assert!(
        e.contains(".fip-lint-journal exists") && e.contains("/elsewhere/x.rs.fip-lint-orig"),
        "{}",
        e
    );
    assert!(!rewritten(&dir.join("j.rs")));
}
