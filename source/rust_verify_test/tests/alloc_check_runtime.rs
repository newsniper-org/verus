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
// specification in vstd is wrong or the compiler introduced an allocator call.

const COUNTING_PRELUDE: &str = r#"
use std::sync::atomic::{AtomicUsize, Ordering};
struct Counting;
static COUNT: AtomicUsize = AtomicUsize::new(0);
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
        unsafe { std::alloc::System.realloc(p, l, n) }
    }
    unsafe fn dealloc(&self, p: *mut u8, l: std::alloc::Layout) {
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
"#;

const CASES: &str = r#"
use vstd::prelude::*;
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

fn main() {
}

} // verus!

#[verifier::external]
fn run_cases() {
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
}
"#;

fn run_at(opt_level: &str) {
    let tempdir = tempfile::TempDir::new().expect("temp dir");
    let entry_file = tempdir.path().join("cases.rs");
    // (`fn main` comes from `verus!`, so `run_cases` is called from a second, external `main`
    // in a module-level wrapper: replace the empty verified `main`)
    let cases = CASES.replace("fn main() {\n}", "#[verifier::external] fn main() { run_cases() }");
    let code = format!("{}\n{}\n{}\n", FEATURE_PRELUDE, COUNTING_PRELUDE, cases);
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
    for line in stdout.lines() {
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
    assert_eq!(n, 13, "expected 13 cases, got:\n{}", stdout);
}

#[test]
fn alloc_check_runtime_opt0() {
    run_at("0");
}

#[test]
fn alloc_check_runtime_opt3() {
    run_at("3");
}
