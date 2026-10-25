#!/bin/bash
# usage (in src/, after build_modules.sh): tools/assemble.sh OUT BUILD ASM JOBS
# 1. merges the per-part OUT/P<p>/C64NData/index.json into ASM/C64NData/index.json (sorted by arc) and checks that arcs 0 .. 1228
#    each appear exactly once;
# 2. writes the assembly with gen_main_nest_r2.py: C64NData/Hgn.lean, one module R<arc>.lean per arc (the subtree statements
#    SubOK, children first, and the arc's ext facts) and Main.lean (the 1,229 arcs, the cover check of [0, 1/2], the mirror lemma
#    for the lower half and the three statements);
# 3. compiles Hgn, then the R modules (largest arcs first, JOBS at a time), then Main, into BUILD/C64NData; logs in ASM/logs.
# Main imports every compiled module (~208,800 files): raise the open-file limit (done below if the hard limit allows) and
# vm.max_map_count (as root: sysctl -w vm.max_map_count=2000000) first. Memory: an R module up to ~9 GB, Main ~100 GB.
# NOMAIN=1 (for a test on a few parts): no arc check, Main written without the cover check and statements, and not compiled.
set -u
OUT=$(cd "$1" && pwd); BUILD=$(cd "$2" && pwd); ASM=$3; J=$4; NOMAIN=${NOMAIN:-0}
T=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$ASM/C64NData" "$ASM/logs"; ASM=$(cd "$ASM" && pwd)
ulimit -n "$(ulimit -Hn)"
python3 -I - "$OUT" "$ASM/C64NData/index.json" "$NOMAIN" <<'PYEOF' || exit 1
import glob, json, sys
L = []
for f in sorted(glob.glob(sys.argv[1] + "/P*/C64NData/index.json")):
    L += json.load(open(f))
L.sort(key=lambda a: a["arc"])
got = [a["arc"] for a in L]
miss = sorted(set(range(1229)) - set(got)); dup = sorted({x for x in got if got.count(x) > 1})
json.dump(L, open(sys.argv[2], "w"))
print("index: arcs", len(L), "subtrees", sum(len(a["subs"]) for a in L), "missing", len(miss), "duplicate", len(dup))
sys.exit(0 if sys.argv[3] == "1" or not (miss or dup) else 1)
PYEOF
if [ "$NOMAIN" = 1 ]; then python3 -I -B "$T/gen_main_nest_r2.py" "$ASM" --mirror --no-main; else python3 -I -B "$T/gen_main_nest_r2.py" "$ASM" --mirror; fi || exit 1
export LEAN_PATH=$(lake env printenv LEAN_PATH):$BUILD LEAN_NUM_THREADS=1 ASM BUILD
LEAN=$(lake env which lean); export LEAN
one() {
  m=$1; t0=$(date +%s%N)
  if $LEAN --root="$ASM" -DElab.async=false -o "$BUILD/C64NData/$m.olean" "$ASM/C64NData/$m.lean" > "$ASM/logs/$m.log" 2>&1; then st=OK; else st=FAIL; fi
  echo "$st $(( ($(date +%s%N) - t0) / 1000000 ))" >> "$ASM/logs/$m.log"
  return 0
}
export -f one
one Hgn; tail -1 "$ASM/logs/Hgn.log" | grep -q '^OK' || { echo "Hgn failed"; exit 1; }
sort -k2 -n -r "$ASM/r_modules.txt" | awk '{print $1}' | xargs -P "$J" -n 1 bash -c 'one "$0"'
bad=0; for m in $(awk '{print $1}' "$ASM/r_modules.txt"); do tail -1 "$ASM/logs/$m.log" | grep -q '^OK' || bad=$((bad + 1)); done
echo "R modules $(wc -l < "$ASM/r_modules.txt"), failed $bad"; [ "$bad" = 0 ] || exit 1
[ "$NOMAIN" = 1 ] && exit 0
one Main; tail -1 "$ASM/logs/Main.log" | grep -q '^OK' || { echo "Main failed"; exit 1; }
echo "Main OK"
