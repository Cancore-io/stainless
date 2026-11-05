#!/usr/bin/env bash
# Unit test of scripts/verify_lib.sh (no Stainless run): bash verification/crypto/tests/verify_lib_test.sh
set -uo pipefail
. "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/scripts/verify_lib.sh"
fails=0
eq() { [[ "$2" == "$3" ]] || { echo "FAIL $1: want '$2' got '$3'"; fails=$((fails + 1)); }; }
G=$((1024 ** 3))
eq "xmx g"        $((13 * G))        "$(xmx_bytes '-Xss512M -Xms1g -Xmx13g')"
eq "xmx M"        $((512 * 1024 ** 2)) "$(xmx_bytes '-Xmx512M')"
eq "xmx last wins" $((12 * G))       "$(xmx_bytes '-Xmx3g -Dx=1 -Xmx12G')"
eq "xmx bytes"    1000               "$(xmx_bytes '-Xmx1000')"
eq "xmx k"        2048               "$(xmx_bytes '-Xmx2k')"
eq "xmx none"     ""                 "$(xmx_bytes '-Xss512M -Xms1g')"
eq "default added" "-Dfoo=1 -Xss512M -Xms1g -Xmx13g" "$(java_opts_with_default_heap '-Dfoo=1')"
eq "default empty" "-Xss512M -Xms1g -Xmx13g"        "$(java_opts_with_default_heap '')"
eq "user Xmx kept" "-Xmx3g"                          "$(java_opts_with_default_heap '-Xmx3g')"
eq "mem enough"    0 "$(mem_enough $((15 * 1024 ** 2)) $((13 * G)); echo $?)"
eq "mem short"     1 "$(mem_enough $((13 * 1024 ** 2)) $((13 * G)); echo $?)"
eq "meminfo parse" 15728640 "$(mem_available_kb <(printf 'MemTotal: 32000000 kB\nMemAvailable:   15728640 kB\n'))"
eq "oom yes" 0 "$(is_jvm_oom <(echo 'Exception in thread "main" java.lang.OutOfMemoryError: Java heap space'); echo $?)"
eq "oom no"  1 "$(is_jvm_oom <(echo 'total: 10 valid: 10'); echo $?)"
# CAN-3294 RX-1: the verdict reads Stainless totals and exit code, not only positioned rows.
tot() { printf '\e[32m[  Info  ] ║ total: %-4d valid: %-4d (0 from cache, 0 trivial) invalid: %-4d unknown: %-4d time:    1.00 ║\e[0m\n' "$@"; }
POSLESS="$(printf '[ Info  ] ║ modIsFloorMod  postcondition  invalid  U:smt-z3  @?:?:  0.1 ║\n'; tot 10 9 1 0)"
eq "totals clean"        0 "$(totals_ok <(tot 10 10 0 0) 0 0 >/dev/null; echo $?)"
eq "positionless invalid" 1 "$(totals_ok <(echo "$POSLESS") 0 1 >/dev/null; echo $?)"
eq "unknown > 0"          1 "$(totals_ok <(tot 10 9 0 1) 0 0 >/dev/null; echo $?)"
eq "expected mutants"     0 "$(totals_ok <(tot 12 9 3 0) 3 1 >/dev/null; echo $?)"
eq "extra invalid"        1 "$(totals_ok <(tot 12 8 4 0) 3 1 >/dev/null; echo $?)"
eq "missing mutant"       1 "$(totals_ok <(tot 12 10 2 0) 3 1 >/dev/null; echo $?)"
eq "rc masked"            1 "$(totals_ok <(tot 10 10 0 0) 0 1 >/dev/null; echo $?)"
eq "rc crash w/ mutants"  1 "$(totals_ok <(tot 12 9 3 0) 3 2 >/dev/null; echo $?)"
eq "no totals"            1 "$(totals_ok <(echo nothing) 0 0 >/dev/null; echo $?)"
eq "two tables summed"    1 "$(totals_ok <(tot 5 5 0 0; tot 5 4 0 1) 0 0 >/dev/null; echo $?)"
eq "rc 0 with invalid"    1 "$(totals_ok <(tot 12 9 3 0) 3 0 >/dev/null; echo $?)"
CHK="$(mktemp)"
printf '12:7;rhsSignedRem;postcondition;invalid\n20:5;addOffCurve;precond. (call add(x));invalid\n' > "$CHK"
eq "expected in group"    2 "$(expected_invalid 'foo,rhsSignedRem,addOffCurve' "$CHK")"
eq "expected other group" 0 "$(expected_invalid 'rhsSignedRemX,add' "$CHK")"
rm -f "$CHK"
((fails == 0)) && echo "OK: verify_lib" || { echo "$fails failure(s)"; exit 1; }
