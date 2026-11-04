# Helpers sourced by verify.sh; tested by tests/verify_lib_test.sh.

# Same -Xss/-Xmx class as the fork CI (-Xss512M -Xmx12G); 13g by operator decision for CAN-2511:
# 3g ran out of heap at ~346/1732 VCs of the first group.
DEFAULT_HEAP_OPTS="-Xss512M -Xms1g -Xmx13g"

# Bytes of the last -Xmx in $1 (the JVM honours the last one); empty when there is none.
xmx_bytes() {
  local v
  v="$(grep -oE -- '-Xmx[0-9]+[kKmMgGtT]?' <<<"$1" | tail -n1)" || true
  [[ -n "$v" ]] || return 0
  v="${v#-Xmx}"
  local n="${v%[kKmMgGtT]}" unit="${v##*[0-9]}"
  case "$unit" in
    k|K) echo $((n * 1024)) ;; m|M) echo $((n * 1024 ** 2)) ;;
    g|G) echo $((n * 1024 ** 3)) ;; t|T) echo $((n * 1024 ** 4)) ;; *) echo "$n" ;;
  esac
}

java_opts_with_default_heap() {
  if [[ -n "$(xmx_bytes "$1")" ]]; then echo "$1"; else echo "${1:+$1 }$DEFAULT_HEAP_OPTS"; fi
}

mem_available_kb() { awk '/^MemAvailable:/ {print $2}' "${1:-/proc/meminfo}"; }

# Heap plus ~1 GiB for metaspace, code cache, thread stacks and z3.
mem_enough() { (( $1 * 1024 >= $2 + 1024 ** 3 )); }

is_jvm_oom() { grep -q 'java.lang.OutOfMemoryError' "$@" 2>/dev/null; }
