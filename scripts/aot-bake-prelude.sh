#!/usr/bin/env bash
# §3.5.H — bake an adsmt AOT prelude/axiom bank (.luart-cdcl) AND a JIT replay
# trace (.lutrace) from the warm-up query, printing the `VERUS_ADSMT_AOT_LUART`
# + `VERUS_ADSMT_JIT_TRACE` lines that activate them on the §3.5.I SmtProcess
# path (the §3.5.F consult fires only when both are present).
#
# Frontend-agnostic by design (Y4 unified-verification goal): the bank caches
# the SMT-LIB *axiom set* a frontend feeds adsmt.  Two input modes:
#
#   --from-smt2 <file.smt2>     bake an arbitrary SMT-LIB axiom set directly
#                              (any SMT-LIB-emitting frontend)
#   --from-verus <source.rs>   extract the Verus prelude via the verus binary's
#                              `--log smt-transcript`, then bake it
#                              (default source: a minimal `verus! { fn main(){} }`)
#
# Cache location is user-overridable (the user explicitly wants this):
#   $VERUS_ADSMT_AOT_CACHE_DIR   — default: <repo>/target-verus/release/aot
#
# The cache key is (sha256 of the baked SMT-LIB text, lu-smt version), so a
# prelude change or a lu-smt bump produces a fresh artefact and never serves a
# stale bank.  Re-running is cheap: an existing matching artefact is reused.
#
# Activation (§3.5.I, proven sound end-to-end at rc.28): the printed
# `export VERUS_ADSMT_AOT_LUART=<path>` makes air's `solver_argv` thread
# `--aot-load <path>` into every per-query lu-smt invocation.  The AOT path is
# sound since rc.28 (S.1-AOT) — an opaque OR-of-AND baked alongside a real
# contradiction returns `unsat`, never a false-positive `sat`.

set -uo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# --- resolve binaries ---------------------------------------------------------
lu_smt="${VERUS_ADSMT_PATH:-lu-smt}"
if ! command -v "$lu_smt" >/dev/null 2>&1 && [ ! -x "$lu_smt" ]; then
    echo "error: lu-smt not found (set VERUS_ADSMT_PATH or put lu-smt on PATH)" >&2
    exit 1
fi

verus_bin="$repo_root/source/target-verus/release/verus"

# --- args ---------------------------------------------------------------------
mode="verus"          # verus | smt2
input=""              # source path (optional in verus mode)
quiet=0
while [ $# -gt 0 ]; do
    case "$1" in
        --from-smt2)  mode="smt2";  input="${2:?--from-smt2 needs a file}"; shift 2 ;;
        --from-verus) mode="verus"; input="${2:-}"; shift 2 ;;
        --quiet|-q)   quiet=1; shift ;;
        -h|--help)
            sed -n '2,40p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
            exit 0 ;;
        *) echo "error: unknown argument: $1" >&2; exit 2 ;;
    esac
done

log() { [ "$quiet" -eq 1 ] || echo "$@" >&2; }

lu_smt_version="$("$lu_smt" --version 2>/dev/null | awk '{print $NF}')"
if [ -z "$lu_smt_version" ]; then
    echo "error: could not read lu-smt --version" >&2; exit 1
fi

cache_dir="${VERUS_ADSMT_AOT_CACHE_DIR:-$repo_root/target-verus/release/aot}"
mkdir -p "$cache_dir"

tmp_bake="$(mktemp --suffix=.smt2)"   # prelude/axiom prefix → the .luart-cdcl bank
tmp_full="$(mktemp --suffix=.smt2)"   # full warm-up incl. (check-sat) → the .lutrace
trap 'rm -f "$tmp_bake" "$tmp_full"' EXIT

# --- obtain the SMT-LIB axiom set (the "bake input") --------------------------
case "$mode" in
    smt2)
        # Arbitrary SMT-LIB axiom set: bake everything up to (but not
        # including) the first (check-sat) — the axioms, not the query.
        awk '/^\(check-sat\)/{stop=1} !stop' "$input" > "$tmp_bake"
        # The trace warm-up is the whole file (axioms + query + check-sat).
        cp "$input" "$tmp_full"
        log "§3.5.H: baking SMT-LIB axiom set from $input"
        ;;
    verus)
        if [ ! -x "$verus_bin" ]; then
            echo "error: verus binary not built ($verus_bin) — run 'vargo build --release' first" >&2
            exit 1
        fi
        src="$input"
        src_tmpdir=""
        if [ -z "$src" ]; then
            # verus uses the source file's stem as the crate name, which must be
            # a valid Rust identifier — so place a fixed-name file in a temp dir
            # (mktemp's random `.`-containing stem is rejected by verus).
            src_tmpdir="$(mktemp -d)"
            src="$src_tmpdir/aot_prelude_probe.rs"
            cat > "$src" <<'RS'
use verus_builtin::*;
use verus_builtin_macros::*;
use vstd::prelude::*;
verus! {
fn main() {}
} // verus!
RS
        fi
        log "§3.5.H: extracting Verus prelude transcript from ${input:-<minimal source>}"
        logdir="$(mktemp -d)"
        VERUS_ADSMT_PATH="$lu_smt" timeout 120 "$verus_bin" \
            --crate-type=lib -V no-solver-version-check -V adsmt \
            --log smt-transcript --log-dir "$logdir" \
            "$src" >/dev/null 2>&1 || true   # verus may time out; transcript is still flushed
        transcript="$logdir/root.smt_transcript"
        if [ ! -f "$transcript" ]; then
            echo "error: verus produced no smt-transcript at $transcript" >&2
            [ -n "$src_tmpdir" ] && rm -rf "$src_tmpdir"; rm -rf "$logdir"; exit 1
        fi
        # Strip the transcript's QUERY/RESPONSE framing → SMT-LIB.  The bank
        # is the prelude prefix (before verus's trailing (get-info :version));
        # the trace warm-up is the same SMT-LIB but keeps the obligation's
        # (check-sat) so the recorder sees a real solve.  verus's version
        # probe (a separate get-info query) is dropped from both.
        qlines="$(mktemp --suffix=.smt2)"
        awk '
            /^;;;>>> QUERY/    { q=1; r=0; next }
            /^;;;>>> RESPONSE/ { q=0; r=1; next }
            /^;;;<<</          { q=0; r=0; next }
            q
        ' "$transcript" > "$qlines"
        awk '/^\(get-info :version\)/{stop=1} !stop' "$qlines" > "$tmp_bake"
        grep -v '^(get-info :version)$' "$qlines" > "$tmp_full"
        rm -f "$qlines"
        [ -n "$src_tmpdir" ] && rm -rf "$src_tmpdir"
        rm -rf "$logdir"
        ;;
esac

if [ ! -s "$tmp_bake" ]; then
    echo "error: bake input is empty" >&2; exit 1
fi

# --- cache key + bake-on-miss -------------------------------------------------
sha="$(sha256sum "$tmp_bake" | cut -c1-16)"
out="$cache_dir/prelude-${sha}-${lu_smt_version}.luart-cdcl"

if [ -f "$out" ]; then
    log "§3.5.H: cache hit — $out"
else
    log "§3.5.H: baking → $out"
    if ! "$lu_smt" --aot-bake --aot-include-cdcl --aot-output "$out" "$tmp_bake" 2>/dev/null; then
        echo "error: lu-smt --aot-bake failed" >&2; rm -f "$out"; exit 1
    fi
    log "§3.5.H: baked $(stat -c%s "$out" 2>/dev/null || echo '?') bytes"
fi

# --- §3.5.H: also bake the JIT replay trace from the warm-up query ------------
# Record the warm-up obligation's CDCL event stream + §3.5.E GF(2) signature
# with the bank active (matching the replay config), so a re-run of the *same*
# obligation can short-circuit to the recorded verdict (§3.5.F consult, gated
# on both --aot-load and --jit-trace-load — exactly the §3.5.I argv shape).
# Keyed on the full-transcript SHA so a query change invalidates it; the bank
# SHA (prelude prefix only) wouldn't.  Best-effort: a trace failure never
# breaks the bank export.
trace_out=""
if [ -s "$tmp_full" ] && grep -q '^(check-sat)' "$tmp_full"; then
    trace_sha="$(sha256sum "$tmp_full" | cut -c1-16)"
    trace_out="$cache_dir/trace-${trace_sha}-${lu_smt_version}.lutrace"
    if [ -f "$trace_out" ]; then
        log "§3.5.H: trace cache hit — $trace_out"
    else
        log "§3.5.H: recording JIT trace → $trace_out"
        # NB: lu-smt's exit code follows the SMT verdict (sat=0, unsat=1,
        # unknown=2), and a *useful* warm-up trace comes from an `unsat` →
        # exit 1.  So gate on the artefact (`-s`), not the exit code.
        "$lu_smt" --aot-load "$out" --jit-trace-emit "$trace_out" "$tmp_full" >/dev/null 2>&1 || true
        if [ -s "$trace_out" ]; then
            log "§3.5.H: traced $(stat -c%s "$trace_out" 2>/dev/null || echo '?') bytes"
        else
            log "§3.5.H: warn — JIT trace emit produced nothing; bank still usable, JIT inactive"
            rm -f "$trace_out"; trace_out=""
        fi
    fi
else
    log "§3.5.H: no (check-sat) in the warm-up — baking the bank only, no trace"
fi

# --- emit the activation line(s) ----------------------------------------------
# stdout carries ONLY the export line(s) so callers can `eval "$(...)"`.
echo "export VERUS_ADSMT_AOT_LUART=$out"
[ -n "$trace_out" ] && echo "export VERUS_ADSMT_JIT_TRACE=$trace_out"
log "§3.5.H: to activate, run:  eval \"\$(scripts/aot-bake-prelude.sh -q)\""
