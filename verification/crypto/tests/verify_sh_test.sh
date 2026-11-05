#!/usr/bin/env bash
# Runs verify.sh end to end against recorded Stainless output (no JVM): bash verification/crypto/tests/verify_sh_test.sh
# CAN-3294 RX-2: pins the totals_ok call in verify.sh, not only the library function.
set -uo pipefail
T="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
fails=0
LOCK="$(mktemp)"; trap 'rm -f "$LOCK"' EXIT
run() { # name want_exit want_line fixture stainless_rc
  local out rc=0
  out="$(STAINLESS="$T/stub_stainless.sh" STUB_GROUP1="$T/fixtures/$4" STUB_RC="$5" VERIFY_SKIP_MEM_CHECK=1 \
    DAMLAUDIT_LOCK="$LOCK" bash "$T/../verify.sh" 2>&1)" || rc=$?
  if [[ "$rc" != "$2" ]] || ! grep -qF "$3" <<<"$out"; then
    echo "FAIL $1: want exit $2 and '$3', got exit $rc:"; echo "$out" | tail -5; fails=$((fails + 1))
  fi
}
run "clean"                 0 "OK: modules valid, mutants match .check"           group1-clean.txt 1
run "positionless invalid"  1 "FAIL: Stainless totals invalid=40, mutants expect 39" group1-positionless-invalid.txt 1
run "stainless exit 0"      1 "FAIL: Stainless exit code 0, expected 1"           group1-clean.txt 0
((fails == 0)) && echo "OK: verify.sh"
exit "$fails"
