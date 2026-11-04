#!/usr/bin/env bash
# Verify verification/crypto with Stainless 0.10.2 at the SPEC §7 budget and check the mutants.
#   * every VC of the modules (and of stainless.math.NonLinear) must be valid: 0 invalid, 0 unknown;
#   * per run, the Stainless totals (positionless VCs included) and exit code must be explained by the mutants;
#   * the invalid VCs of invalid/<X>.scala must equal invalid/<X>.check (line:col;function;kind;invalid).
# Mutant files are invalid/*Mutants.scala. One Stainless run covers both. Env: STAINLESS (launcher),
# DAMLAUDIT_LOCK (flock file held for the whole run, default ${TMPDIR:-/tmp}/stainless-verify.lock),
# JAVA_OPTS (default heap added when it has no -Xmx), VERIFY_SKIP_MEM_CHECK=1, CRYPTO_TIMEOUT (default 10).
# Extra arguments go to Stainless.
set -euo pipefail
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
. "$DIR/scripts/verify_lib.sh"
# One run at a time per host: two 13g JVMs do not fit, the second waits instead of OOMing both.
LOCK="${DAMLAUDIT_LOCK:-${TMPDIR:-/tmp}/stainless-verify.lock}"
if [[ -z "${VERIFY_LOCK_HELD:-}" ]]; then
  flock -n "$LOCK" true || echo "waiting for $LOCK (another verify run holds it)" >&2
  VERIFY_LOCK_HELD=1 exec flock "$LOCK" "$0" "$@"
fi
export JAVA_OPTS="$(java_opts_with_default_heap "${JAVA_OPTS:-}")"
if [[ "${VERIFY_SKIP_MEM_CHECK:-}" != 1 ]]; then
  heap="$(xmx_bytes "$JAVA_OPTS")"; avail="$(mem_available_kb)"
  mem_enough "$avail" "$heap" || { echo "FAIL: MemAvailable $((avail / 1024)) MiB < -Xmx $((heap / 1024 ** 2)) MiB + 1024 MiB; free memory or set VERIFY_SKIP_MEM_CHECK=1" >&2; exit 1; }
fi
ROOT="$(cd "$DIR/../.." && pwd)"
LOG="$(mktemp)"; trap 'rm -f "$LOG"' EXIT
python3 "$DIR/scripts/pratt_trace_gen.py" --check || { echo "FAIL: PrattTraces.scala is not reproduced by scripts/pratt_trace_gen.py" >&2; exit 1; }
mapfile -t srcs < <(find "$DIR" -maxdepth 1 -name '*.scala' | sort)
mapfile -t muts < <(find "$DIR/invalid" -name '*.scala' | sort)
# PrattTraces.scala alone is ~60k VCs, more than one JVM heap holds: it is verified in
# CRYPTO_TRACE_CHUNKS runs of its own (--functions), everything else in a first run.
TRACES="$DIR/PrattTraces.scala"
mapfile -t trace_fns < <(grep -oP '^  def \K\w+' "$TRACES")
mapfile -t other_fns < <(grep -hoP '^\s*(?:@\w+\s+)*def \K[^\s(\[:]+' "$ROOT/frontends/library/stainless/math/NonLinear.scala" \
  $(printf '%s\n' "${srcs[@]}" | grep -v PrattTraces.scala) "${muts[@]}" | sort -u)
chunks="${CRYPTO_TRACE_CHUNKS:-5}"
size=$(( (${#trace_fns[@]} + chunks - 1) / chunks ))
# inv: the class invariants Stainless synthesizes (no `def` in the source).
other_fns+=(inv)
groups=("$(IFS=,; echo "${other_fns[*]}")")
for ((i = 0; i < ${#trace_fns[@]}; i += size)); do groups+=("$(IFS=,; echo "${trace_fns[*]:i:size}")"); done
: > "$LOG"
fail=0
checks=("${muts[@]/%.scala/.check}")
for g in "${groups[@]}"; do
  one="$(mktemp)"
  cmd=("${STAINLESS:-stainless}" --solvers=smt-z3 "--timeout=${CRYPTO_TIMEOUT:-10}" --batched=true --vc-cache=false "--functions=$g" "$@"
    "$ROOT/frontends/library/stainless/math/NonLinear.scala" "${srcs[@]}" "${muts[@]}")
  rc=0; "${cmd[@]}" > "$one" 2>&1 || rc=$?
  if ! sed 's/\x1b\[[0-9;]*m//g' "$one" | grep -qE 'total:'; then
    cat "$one"
    traces=("$one"); [[ stainless-stack-trace.txt -nt "$one" ]] && traces+=(stainless-stack-trace.txt)
    if is_jvm_oom "${traces[@]}"; then echo "FAIL: JVM heap exhausted — raise -Xmx (JAVA_OPTS=$JAVA_OPTS)" >&2
    else echo "FAIL: a Stainless run produced no verification table" >&2; fi
    rm -f "$one"; exit 1
  fi
  totals_ok "$one" "$(expected_invalid "$g" "${checks[@]}")" "$rc" || fail=1
  cat "$one" >> "$LOG"; rm -f "$one"
done
rows="$(sed 's/\x1b\[[0-9;]*m//g' "$LOG" | grep -E '^\[ *Info *\] ║ .*\.scala:[0-9]+:[0-9]+: ' || true)"
[[ -n "$rows" ]] || { cat "$LOG"; echo "FAIL: no verification table" >&2; exit 1; }
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
awk '{t=$(NF-1); if (t+0 > m) {m=t+0; r=$0}} END {gsub(/  +/, " ", r); print "max VC time: " m " s —" r}' <<<"$rows"
((fail == 0)) && echo "OK: modules valid, mutants match .check"
exit "$fail"
