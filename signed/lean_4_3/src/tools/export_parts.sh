#!/bin/bash
# usage (in src/): tools/export_parts.sh PARTS OUT JOBS
# Writes the Lean data of the upper half: for each part p = 000 .. 1228 (file PARTS/cert_t25_sub_<p>.json.gz; part p holds
# arc p, and parts p < 410 also the lower arc p + 2048, which --upper skips), OUT/P<p>/C64NData/ with Glob.lean, the arc
# module A<p>.lean, its subtree modules A<p>S<j>.lean and index.json. JOBS parts at a time; a finished part is skipped.
# Needs Python 3 with python-flint 0.9.0. Prints "exported N of 1229"; exits 1 unless N = 1229.
# ONLY="082 1092" (for a test) exports only the listed parts.
set -u
PARTS=$(cd "$1" && pwd); OUT=$2; J=$3
T=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
one() {
  p=$1
  [ -e "$OUT/P$p/exported" ] && return 0
  python3 -I -B "$T/gen_nest_data.py" modules "$PARTS/cert_t25_sub_$p.json.gz" "$OUT/P$p" --upper --max-recs 16000 \
    --index-offset $((10#$p)) > "$OUT/P$p.log" 2>&1 && touch "$OUT/P$p/exported"
  return 0
}
export -f one; export PARTS OUT T
if [ -n "${ONLY:-}" ]; then echo $ONLY | tr ' ' '\n'; else seq 0 1228 | awk '{printf "%03d\n", $1}'; fi | xargs -P "$J" -n 1 bash -c 'one "$0"'
n=$(ls "$OUT"/P*/exported 2>/dev/null | wc -l)
echo "exported $n of 1229"
[ "$n" = 1229 ]
