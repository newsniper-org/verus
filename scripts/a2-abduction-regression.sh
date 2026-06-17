#!/usr/bin/env bash
# A2 "verify-or-explain" abduction regression harness.
#
# Exercises `verus -V adsmt -V request-abductive-on-unknown` end-to-end
# against the fixtures in scripts/a2-fixtures/, asserting the
# verify / abduct / no-abduct trichotomy and that each abduct category
# (sign, negativity, relational, boolean) surfaces the expected hypothesis.
#
# Per the project standing directive, this REBUILDS lu-smt from the adsmt
# local repo (~/AD1) on every run and points verus at that build via
# VERUS_ADSMT_PATH — it never uses the system /usr/bin/lu-smt (which lags
# the live engine). Override AD1 / VERUS by env if your layout differs.
#
# Usage:  scripts/a2-abduction-regression.sh
# Exit:   0 = all rows match expectation, non-zero = at least one mismatch.

set -u
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/.." && pwd)"
AD1="${AD1:-$HOME/AD1}"
VERUS="${VERUS:-$REPO/source/target-verus/release/verus}"
FIX="$HERE/a2-fixtures"
FLAGS="-V adsmt -V request-abductive-on-unknown"

echo "== rebuilding lu-smt from $AD1 (standing directive: never the system binary) =="
( cd "$AD1" && cargo build --release --features adsmt-cli/oxiz -p adsmt-cli ) || {
    echo "FATAL: lu-smt build failed"; exit 2; }
LU="$AD1/target/release/lu-smt"
[ -x "$LU" ] || { echo "FATAL: $LU not found"; exit 2; }
[ -x "$VERUS" ] || { echo "FATAL: verus not built at $VERUS (run vargo build --release)"; exit 2; }
echo "   lu-smt: $($LU --version)"
echo "   verus:  $VERUS"
echo

# run <fixture> -> prints the verus output; sets VERIFIED/HAS_ABDUCT globals
run() { VERUS_ADSMT_PATH="$LU" timeout 300 "$VERUS" $FLAGS "$FIX/$1" 2>&1; }

pass=0; fail=0
# check <name> <fixture> <kind> [expected-substring]
#   kind = verify   : must report ">=1 verified, 0 errors", no abductive verdict
#   kind = abduct   : must report an "abductive verdict" containing <expected-substring>
#   kind = noabduct : must error (0 verified) WITHOUT an "abductive verdict"
check() {
    local name="$1" fixture="$2" kind="$3" want="${4:-}"
    local out; out="$(run "$fixture")"
    local verified errors abduct
    verified="$(echo "$out" | grep -oE '[0-9]+ verified' | tail -1 | grep -oE '[0-9]+')"
    errors="$(echo "$out"   | grep -oE '[0-9]+ errors'   | tail -1 | grep -oE '[0-9]+')"
    abduct="$(echo "$out" | grep -c 'abductive verdict')"
    local ok=1 why=""
    case "$kind" in
        verify)
            { [ "${verified:-0}" -ge 1 ] && [ "${errors:-1}" -eq 0 ] && [ "$abduct" -eq 0 ]; } || { ok=0; why="want verify; got verified=$verified errors=$errors abduct=$abduct"; } ;;
        abduct)
            if [ "$abduct" -lt 1 ]; then ok=0; why="want abductive verdict; none emitted (verified=$verified errors=$errors)";
            elif ! echo "$out" | grep -qF "$want"; then ok=0; why="abductive verdict present but missing expected '$want'"; fi ;;
        noabduct)
            { [ "${errors:-0}" -ge 1 ] && [ "$abduct" -eq 0 ]; } || { ok=0; why="want error w/o abduct; got errors=$errors abduct=$abduct"; } ;;
    esac
    if [ "$ok" -eq 1 ]; then printf "  PASS  %-22s (%s%s)\n" "$name" "$kind" "${want:+ → $want}"; pass=$((pass+1));
    else printf "  FAIL  %-22s %s\n" "$name" "$why"; fail=$((fail+1));
         echo "$out" | grep -E 'verification results|abductive verdict|rank [0-9]' | sed 's/^/        | /'; fi
}

echo "== A2 verify-or-explain trichotomy + vocabulary =="
check "verify-arith"      verify-arith.rs      verify
check "abduct-sign"       abduct-sign.rs       abduct   "(>= x! 0)"
check "abduct-negativity" abduct-negativity.rs abduct   "(<= x! 0)"
check "abduct-relational" abduct-relational.rs abduct   "(> x! y!)"
check "abduct-boolean"    abduct-boolean.rs    abduct   "b!"
check "noabduct-false"    noabduct-false.rs    noabduct

echo
echo "== result: $pass passed, $fail failed =="
[ "$fail" -eq 0 ]
