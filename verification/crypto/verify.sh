#!/usr/bin/env bash
# Verify verification/crypto with Stainless 0.10.2 at the SPEC §7 budget and check the mutants.
#   * every VC of the modules (and of stainless.math.NonLinear) must be valid: 0 invalid, 0 unknown;
#   * the invalid VCs of invalid/<X>.scala must equal invalid/<X>.check (line:col;function;kind;invalid).
# Mutant files are invalid/*Mutants.scala. One Stainless run covers both. Env: STAINLESS (launcher), DAMLAUDIT_LOCK (flock file for a shared host),
# CRYPTO_TIMEOUT (default 10). Extra arguments go to Stainless.
set -euo pipefail
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$DIR/../.." && pwd)"
LOG="$(mktemp)"; trap 'rm -f "$LOG"' EXIT
mapfile -t srcs < <(find "$DIR" -maxdepth 1 -name '*.scala' | sort)
mapfile -t muts < <(find "$DIR/invalid" -name '*.scala' | sort)
cmd=("${STAINLESS:-stainless}" --solvers=smt-z3 "--timeout=${CRYPTO_TIMEOUT:-10}" --batched=true --vc-cache=false "$@"
  "$ROOT/frontends/library/stainless/math/NonLinear.scala" "${srcs[@]}" "${muts[@]}")
[[ -n "${DAMLAUDIT_LOCK:-}" ]] && cmd=(flock "$DAMLAUDIT_LOCK" "${cmd[@]}")
"${cmd[@]}" > "$LOG" 2>&1 || true
rows="$(sed 's/\x1b\[[0-9;]*m//g' "$LOG" | grep -E '^\[ *Info *\] ║ .*\.scala:[0-9]+:[0-9]+: ' || true)"
[[ -n "$rows" ]] || { cat "$LOG"; echo "FAIL: no verification table" >&2; exit 1; }
fail=0
bad="$(grep -E ' (invalid|timeout|unknown|crashed) ' <<<"$rows" | grep -v 'Mutants\.scala:' || true)"
[[ -z "$bad" ]] || { echo "FAIL: non-valid VCs in the modules:"; echo "$bad"; fail=1; }
for m in "${muts[@]}"; do
  f="$(basename "$m")"
  got="$(grep -E "[ /]$f:" <<<"$rows" | perl -ne 'print "$1;$2;$3;$4\n" if /\Q'"$f"'\E:(\d+:\d+): +(\S+) +(.+?) +(invalid|timeout|unknown|crashed) /' | sort -t: -k1,1n -k2,2n)"
  if ! diff <(sort -t: -k1,1n -k2,2n "${m%.scala}.check") <(echo "$got") >/dev/null; then
    echo "FAIL: $f does not match its .check"; diff <(sort -t: -k1,1n -k2,2n "${m%.scala}.check") <(echo "$got") || true; fail=1
  fi
done
sed 's/\x1b\[[0-9;]*m//g' "$LOG" | grep -E 'total:' | sed 's/  */ /g'
sed 's/\x1b\[[0-9;]*m//g' "$LOG" | grep -oE ' (valid|invalid) +U:[a-z0-9-]+ +[0-9.]+ ' | awk '{print $3}' | sort -n | tail -1 | sed 's/^/max VC time: /'
((fail == 0)) && echo "OK: modules valid, mutants match .check"
exit "$fail"
