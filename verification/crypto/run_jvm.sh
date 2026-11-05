#!/usr/bin/env bash
# Execute the verified verification/crypto code on the JVM against the PR 1 oracle vectors.
# Compiles with the Scala compiler bundled in the Stainless 0.10.2 release (its library TASTy
# is a 3.10 nightly that a stock Scala 3.9 cannot read), so the JVM runs exactly what Stainless
# verified. ujson comes from coursier (`cs`).
# Env: STAINLESS_LIB  override the release lib directory (default: next to `stainless` on PATH).
set -euo pipefail
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$DIR/../.." && pwd)"
LIB="${STAINLESS_LIB:-$(dirname "$(readlink -f "$(command -v stainless)")")/lib}"
SCALA="$(ls "$LIB"/stainless-dotty-standalone-*.jar)"
DEPS="$(cs fetch com.lihaoyi:ujson_3:4.0.2 --classpath | tr ':' '\n' | grep -v '/org/scala-lang/' | paste -sd:)"
CP="$LIB/stainless-library.jar:$DEPS:$SCALA"
OUT="$(mktemp -d)"; trap 'rm -rf "$OUT"' EXIT
# PrattTraces.scala (~88k lines of @ghost proof traces checked by verify.sh) exceeds the JVM 64k
# constant-pool classfile limit; on the JVM ghostExpr(...) is a no-op and PrattJvm runs Pratt.certifies directly.
cat > "$OUT/PrattTracesStub.scala" <<'EOF'
package crypto
object PrattTraces {
  def secp256k1PChecked(): Unit = ()
  def secp256k1NChecked(): Unit = ()
  def p256PChecked(): Unit = ()
  def p256NChecked(): Unit = ()
}
EOF
mapfile -t srcs < <(find "$DIR" -maxdepth 1 -name '*.scala' ! -name 'PrattTraces.scala' | sort)
java -cp "$SCALA" dotty.tools.dotc.Main -experimental -language:experimental.qualifiedTypes -classpath "$CP" -d "$OUT" \
  "$ROOT/frontends/library/stainless/math/NonLinear.scala" "${srcs[@]}" "$OUT/PrattTracesStub.scala" "$DIR"/tests/*Jvm.scala
for t in "$DIR"/tests/*Jvm.scala; do
  java -Xss16m -cp "$OUT:$CP" "crypto.$(basename "$t" .scala)" "$ROOT/verification/crypto-oracle/vectors"
done
