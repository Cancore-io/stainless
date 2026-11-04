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
((fails == 0)) && echo "OK: verify_lib" || { echo "$fails failure(s)"; exit 1; }
