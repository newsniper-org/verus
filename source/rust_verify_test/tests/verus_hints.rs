#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// `.verus-hints`: how some obligations are checked (rlimit, isolate), kept out of the source.
// The hash of an entry depends on the text of the code, so most tests run twice: first with the
// entries as written, without a hash (not applied, with a warning that shows each entry for the
// current code), then with the entries that the warnings show.

const SUM: &str = verus_code_str! {
    spec fn sum(n: nat) -> nat decreases n { if n == 0 { 0 } else { n + sum((n - 1) as nat) } }
};

fn run(name: &str, code: &str, hints: &str, options: &[&str]) -> Result<TestErr, TestErr> {
    verify_one_file_with_files(
        name,
        code.to_string(),
        vec![(".verus-hints".to_string(), hints.to_string())],
        options,
    )
}

/// The entries that the warnings show for the current code
fn refreshed(err: &TestErr) -> String {
    let mut entries = vec![];
    for w in err.warnings.iter().chain(err.errors.iter()) {
        let r = &w.rendered;
        let Some(i) = r.find("replace it with") else { continue };
        let lines: Vec<&str> =
            r[i..].lines().skip(1).map(|l| l.trim()).take_while(|l| !l.is_empty()).collect();
        entries.push(lines.join("\n"));
    }
    entries.join("\n\n")
}

fn result(r: Result<TestErr, TestErr>) -> TestErr {
    match r {
        Ok(e) | Err(e) => e,
    }
}

fn applied_note(err: &TestErr, n: usize) -> bool {
    let s = if n == 1 { "hint" } else { "hints" };
    err.notes.iter().any(|d| d.message.starts_with(&format!("{n} {s} from")))
}

/// Run with the hints as written (none applied, a warning for each), then with the hashes
fn run_pinned(name: &str, code: &str, hints: &str, options: &[&str]) -> Result<TestErr, TestErr> {
    let first = result(run(name, code, hints, options));
    let hint_warnings = first.warnings.iter().filter(|w| w.message.contains("hint"));
    assert!(hint_warnings.clone().count() > 0);
    assert!(hint_warnings.clone().all(|w| w.message.contains("it has no `hash`")));
    let pinned = refreshed(&first);
    assert_eq!(pinned.matches("[[hint]]").count(), hints.matches("[[hint]]").count());
    run(name, code, &pinned, options)
}

#[test]
fn hint_rlimit() {
    let code = SUM.to_string()
        + verus_code_str! {
            #[verifier::rlimit(0.02)]
            proof fn a() {
                reveal_with_fuel(sum, 13);
                assert(sum(12) == 78);
            }
        };
    let hints = "[[hint]]\nfunction = \"a\"\nrlimit = 10\n";
    // not applied without its hash: the source's rlimit holds
    let first = run("hint_rlimit", &code, hints, &[]).unwrap_err();
    assert_eq!(first.errors.len(), 1);
    assert!(first.errors[0].message.contains("resource limit (rlimit) exceeded"));
    assert_eq!(first.warnings.len(), 1);
    assert!(first.warnings[0].message.contains("the hint was not applied: it has no `hash`"));
    // with it, the hint replaces the source's rlimit
    let pinned = refreshed(&first);
    assert!(pinned.contains("hash = \""));
    let second = run("hint_rlimit", &code, &pinned, &[]).unwrap();
    assert!(second.warnings.is_empty());
    assert!(applied_note(&second, 1));
}

#[test]
fn hint_ensures_clause() {
    let code = SUM.to_string()
        + verus_code_str! {
            #[verifier::rlimit(0.02)]
            proof fn by_index(b: bool)
                ensures
                    b ==> b,
                    sum(12) == 78,
            {
                if b { reveal_with_fuel(sum, 13); return; }
                reveal_with_fuel(sum, 13);
            }
            #[verifier::rlimit(0.02)]
            proof fn by_note()
                ensures
                    true,
                    #![verifier::proof_note("sum")]
                    sum(12) == 78,
            {
                reveal_with_fuel(sum, 13);
            }
            #[verifier::rlimit(0.02)]
            proof fn all_ensures()
                ensures sum(12) == 78,
            {
                reveal_with_fuel(sum, 13);
            }
        };
    let hints = "[[hint]]\nfunction = \"by_index\"\nensures = 2\nisolate = { rlimit = 10 }\n\n\
                 [[hint]]\nfunction = \"by_note\"\nproof_note = \"sum\"\nisolate = { rlimit = 10 }\n\n\
                 [[hint]]\nfunction = \"all_ensures\"\nisolate = { rlimit = 10 }\n";
    let first = run("hint_ensures_clause", &code, hints, &[]).unwrap_err();
    assert_eq!(first.errors.len(), 3);
    let second = run_pinned("hint_ensures_clause", &code, hints, &[]).unwrap();
    assert!(applied_note(&second, 3));
}

#[test]
fn hint_overrides_source_isolate() {
    // the source isolates the clause with too small an rlimit; the hint replaces it
    let code = SUM.to_string()
        + verus_code_str! {
            #[verifier::rlimit(10)]
            proof fn t()
                ensures
                    #![verifier::tactic(isolate(rlimit = 0.001))]
                    sum(12) == 78,
            {
                reveal_with_fuel(sum, 13);
            }
        };
    let hints = "[[hint]]\nfunction = \"t\"\nensures = 1\nisolate = {}\n";
    let first = run("hint_overrides_source_isolate", &code, hints, &[]).unwrap_err();
    assert!(first.errors[0].message.contains("exceeded in the proof isolated here"));
    run_pinned("hint_overrides_source_isolate", &code, hints, &[]).unwrap();
}

#[test]
fn hint_stale() {
    let code = |comment: &str| {
        SUM.to_string()
            + &verus_code_str! {
                #[verifier::rlimit(0.02)]
                proof fn a() {
                    reveal_with_fuel(sum, 13);
                    assert(sum(12) == 78);
                }
            }
            .replace("reveal_with_fuel", &format!("{comment}reveal_with_fuel"))
    };
    let hints = "[[hint]]\nfunction = \"a\"\nrlimit = 10\n";
    let pinned = refreshed(&run("hint_stale", &code(""), hints, &[]).unwrap_err());
    run("hint_stale", &code(""), &pinned, &[]).unwrap();
    // another function changed: the hint still applies (also with -V hints-locked)
    let other = code("") + verus_code_str! { proof fn b() { assert(true); } };
    let r = run("hint_stale", &other, &pinned, &["hints-locked"]).unwrap();
    assert!(applied_note(&r, 1));
    // the function changed: the hint is not applied, and the warning shows the new entry
    let changed = code("assert(true); ");
    let err = run("hint_stale", &changed, &pinned, &[]).unwrap_err();
    assert_eq!(err.errors.len(), 1);
    assert!(err.errors[0].message.contains("resource limit (rlimit) exceeded"));
    assert!(err.warnings[0].message.contains("`a` has changed since it was written"));
    let repinned = refreshed(&err);
    assert_ne!(repinned, pinned);
    run("hint_stale", &changed, &repinned, &[]).unwrap();
    // with -V hints-locked, it is an error
    let err = run("hint_stale", &changed, &pinned, &["hints-locked"]).unwrap_err();
    assert!(err.errors.iter().any(|e| e.message.contains("`a` has changed since it was written")));
    assert!(err.errors.iter().any(|e| e.message.contains("did not apply to the code")));
}

#[test]
fn hint_whitespace_is_not_a_change() {
    let code = |sep: &str| {
        SUM.to_string()
            + &verus_code_str! {
                #[verifier::rlimit(0.02)]
                proof fn a() {
                    reveal_with_fuel(sum, 13);
                    assert(sum(12) == 78);
                }
            }
            .replace("reveal_with_fuel", &format!("{sep}reveal_with_fuel"))
    };
    let hints = "[[hint]]\nfunction = \"a\"\nrlimit = 10\n";
    let pinned = refreshed(&run("hint_whitespace", &code(""), hints, &[]).unwrap_err());
    run("hint_whitespace", &code("\n\n        "), &pinned, &[]).unwrap();
}

#[test]
fn hint_not_found() {
    let code = SUM.to_string()
        + verus_code_str! {
            mod m {
                pub proof fn p() ensures true {}
            }
            proof fn q() ensures true {}
        };
    let hints = "[[hint]]\nfunction = \"p\"\nrlimit = 5\n\n\
                 [[hint]]\nfunction = \"q\"\nensures = 2\nisolate = {}\n\n\
                 [[hint]]\nfunction = \"q\"\nproof_note = \"none\"\nisolate = {}\n";
    let err = run("hint_not_found", &code, hints, &[]).unwrap();
    let not_applied = |e: &&Diagnostic| e.message.contains("the hint was not applied");
    assert_eq!(err.warnings.iter().filter(not_applied).count(), 3);
    assert!(err.warnings[0].message.contains("there is no function `p` in this crate"));
    assert!(err.warnings[0].rendered.contains("m::p"));
    assert!(err.warnings[1].message.contains("has 1 `ensures` clause, not 2"));
    assert!(err.warnings[2].message.contains("no `ensures` clause with the proof note \"none\""));
    let err = run("hint_not_found", &code, hints, &["hints-locked"]).unwrap_err();
    assert!(err.errors.iter().any(|e| e.message.contains("3 hints of")));
}

#[test]
fn hint_module_path_and_explicit_file() {
    let code = SUM.to_string()
        + verus_code_str! {
            mod m {
                use super::*;
                #[verifier::rlimit(0.02)]
                pub proof fn p() {
                    reveal_with_fuel(sum, 13);
                    assert(sum(12) == 78);
                }
            }
        };
    let hints = "[[hint]]\nfunction = \"m::p\"\nrlimit = 10\n";
    let first = result(run("hint_module_path", &code, hints, &[]));
    let pinned = refreshed(&first);
    // `-V hints=<path>`: that file, not `.verus-hints`
    let dir = tempfile::tempdir().unwrap();
    let other = dir.path().join("other-hints.toml");
    std::fs::write(&other, &pinned).unwrap();
    let option = format!("hints={}", other.display());
    let r = verify_one_file_with_files(
        "hint_module_path",
        code.clone(),
        vec![(".verus-hints".to_string(), "not toml at all [".to_string())],
        &[option.as_str()],
    );
    assert!(applied_note(&r.unwrap(), 1));
    // and the full path, with the crate
    let full = pinned.replace("function = \"m::p\"", "function = \"crate::m::p\"");
    assert!(applied_note(&run("hint_module_path", &code, &full, &[]).unwrap(), 1));
}

#[test]
fn hint_malformed() {
    let code = verus_code_str! {
        proof fn p() ensures true {}
        trait T {
            proof fn d() ensures true;
        }
    }
    .to_string();
    let cases: &[(&str, &str)] = &[
        ("[[hint]]\nfunction = \"p\"\nrlimit = 5\nadmit = true\n", "is not valid"),
        ("[[hint]]\nfunction = \"p\"\nensures = 1\nproof_note = \"x\"\nisolate = {}\n", "not both"),
        (
            "[[hint]]\nfunction = \"p\"\nensures = 1\nrlimit = 5\nisolate = {}\n",
            "takes only `isolate`",
        ),
        ("[[hint]]\nfunction = \"p\"\nensures = 1\n", "needs `isolate`"),
        ("[[hint]]\nfunction = \"p\"\n", "neither `rlimit` nor `isolate`"),
        ("[[hint]]\nfunction = \"p\"\nensures = 0\nisolate = {}\n", "counts the clauses from 1"),
        ("[[hint]]\nfunction = \"p\"\nrlimit = -1\n", "expected a number"),
        ("[[hint]]\nfunction = \"p\"\nisolate = { backend = \"oxiz\" }\n", "unknown backend"),
        (
            "[[hint]]\nfunction = \"p\"\nisolate = { backend = \"cvc5\" }\n",
            "needs the encoding for cvc5",
        ),
        ("[[hint]]\nfunction = \"p\"\nisolate = { assume = true }\n", "is not valid"),
        (
            "[[hint]]\nfunction = \"T::d\"\nisolate = {}\n",
            "not allowed for a trait method declaration",
        ),
        (
            "[[hint]]\nfunction = \"p\"\nrlimit = 5\n\n[[hint]]\nfunction = \"p\"\nisolate = {}\n",
            "another hint is for the same function",
        ),
    ];
    for (hints, msg) in cases {
        let err = run("hint_malformed", &code, hints, &[]).unwrap_err();
        assert!(
            err.errors.iter().any(|e| e.message.contains(msg)),
            "expected an error with \"{msg}\" for:\n{hints}\ngot: {:?}",
            err.errors.iter().map(|e| e.message.clone()).collect::<Vec<_>>()
        );
    }
}

#[test]
fn hint_backend_cvc5() {
    // the hint makes cvc5 check the clause, with its rlimit, as `isolate(backend = cvc5)` would
    // (an rlimit too small for anything, so that the error shows which solver ran out of it)
    let code = SUM.to_string()
        + verus_code_str! {
            proof fn t()
                ensures sum(12) == 78,
            {
                reveal_with_fuel(sum, 13);
            }
        };
    let hints = "[[hint]]\nfunction = \"t\"\nensures = 1\nisolate = { backend = \"cvc5\", rlimit = 0.0001 }\n";
    let err = run_pinned("hint_backend_cvc5", &code, hints, &["-V cvc5-smtlib"]).unwrap_err();
    assert_eq!(err.errors.len(), 1);
    assert!(err.errors[0].message.starts_with("isolated proof, checked by cvc5: "));
    assert!(err.errors[0].message.contains("exceeded in the proof isolated here"));
}

#[test]
fn hint_clause_hash_is_local() {
    // the hash of a hint for a clause covers the clause: the body may change
    let code = |extra: &str| {
        SUM.to_string()
            + &verus_code_str! {
                #[verifier::rlimit(0.02)]
                proof fn t()
                    ensures sum(12) == 78,
                {
                    reveal_with_fuel(sum, 13);
                }
            }
            .replace("reveal_with_fuel", &format!("{extra}reveal_with_fuel"))
    };
    let hints = "[[hint]]\nfunction = \"t\"\nensures = 1\nisolate = { rlimit = 10 }\n";
    let pinned = refreshed(&run("hint_clause_hash_is_local", &code(""), hints, &[]).unwrap_err());
    let r = run("hint_clause_hash_is_local", &code("assert(true); "), &pinned, &["hints-locked"]);
    assert!(applied_note(&r.unwrap(), 1));
}

#[test]
fn hint_root() {
    // entries for another crate that shares the file are skipped, also under -V hints-locked
    let code = SUM.to_string()
        + verus_code_str! {
            #[verifier::rlimit(0.02)]
            proof fn a() {
                reveal_with_fuel(sum, 13);
                assert(sum(12) == 78);
            }
        };
    let hints = "[[hint]]\nfunction = \"a\"\nroot = \"test.rs\"\nrlimit = 10\n";
    let pinned = refreshed(&run("hint_root", &code, hints, &[]).unwrap_err());
    assert!(pinned.contains("root = \"test.rs\""));
    let other = "[[hint]]\nfunction = \"elsewhere\"\nroot = \"src/main.rs\"\nrlimit = 10\n";
    let both = format!("{pinned}\n\n{other}");
    let r = run("hint_root", &code, &both, &["hints-locked"]).unwrap();
    assert!(applied_note(&r, 1));
    assert!(r.warnings.iter().all(|w| !w.message.contains("hint")));
}

#[test]
fn hint_same_name() {
    // two methods named `S::m`: the hash picks one; rustc's full path names each
    let code = verus_code_str! {
        struct S;
        trait T1 { proof fn m(); }
        trait T2 { proof fn m(); }
        impl T1 for S { proof fn m() {} }
        impl T2 for S { proof fn m() { assert(true); } }
    }
    .to_string();
    let hints = "[[hint]]\nfunction = \"S::m\"\nrlimit = 5\n";
    let first = run("hint_same_name", &code, hints, &[]).unwrap();
    assert!(first.warnings.iter().any(|w| w.message.contains("`S::m` names 2 functions")));
    let one = refreshed(&first);
    assert!(one.contains("as T1>::m") || one.contains("as T2>::m"), "{}", one);
    let r = run("hint_same_name", &code, &one, &["hints-locked"]).unwrap();
    assert!(applied_note(&r, 1));
    // and the short name, with the hash of one of them
    let short =
        one.lines().map(|l| if l.starts_with("function") { "function = \"S::m\"" } else { l });
    let short = short.collect::<Vec<_>>().join("\n");
    let r = run("hint_same_name", &code, &short, &["hints-locked"]).unwrap();
    assert!(applied_note(&r, 1));
}

#[test]
fn hint_param_pattern() {
    // a clause of a function with parameter patterns, found by its proof note
    let code = SUM.to_string()
        + verus_code_str! {
            #[verifier::rlimit(0.02)]
            proof fn t((a, b): (nat, nat))
                ensures
                    a + b == b + a,
                    #![verifier::proof_note("sum")]
                    sum(12) + a == 78 + a,
            {
                reveal_with_fuel(sum, 13);
            }
        };
    let hints = "[[hint]]\nfunction = \"t\"\nproof_note = \"sum\"\nisolate = { rlimit = 10 }\n";
    let first = run("hint_param_pattern", &code, hints, &[]).unwrap_err();
    assert!(first.errors[0].message.contains("resource limit (rlimit) exceeded"));
    let pinned = refreshed(&first);
    assert!(applied_note(
        &run("hint_param_pattern", &code, &pinned, &["hints-locked"]).unwrap(),
        1
    ));
}

#[test]
fn hint_file_errors() {
    let code = verus_code_str! { proof fn p() {} }.to_string();
    let err = verify_one_file_with_files(
        "hint_file_errors",
        code.clone(),
        vec![],
        &["hints=/nonexistent/dir/hints.toml"],
    )
    .unwrap_err();
    assert!(err.errors.iter().any(|e| e.message.contains("cannot read the hints file")));
    // a path with `=` in it
    let dir = tempfile::tempdir().unwrap();
    let sub = dir.path().join("a=b");
    std::fs::create_dir(&sub).unwrap();
    let file = sub.join("hints.toml");
    std::fs::write(&file, "").unwrap();
    let option = format!("hints={}", file.display());
    verify_one_file_with_files("hint_file_errors", code, vec![], &[option.as_str()]).unwrap();
}
