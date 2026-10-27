#!/bin/bash
# usage (in src/, after build_modules_k.sh): tools/assemble_k.sh OUT BUILD JOBS
# Writes and compiles the assembly in the fixed directory ASM = /k43/asm. Hgn, the R modules and Main import Mathlib, whose
# linter stores the path of a module's own source file in its compiled file, so a byte-for-byte rebuild of these files
# needs the same paths. ASM=<dir> may be set for a run that need not reproduce the published files.
# 1. merges the per-part OUT/P<p>/C64NData/index.json into ASM/m/C64NData/index.json (sorted by arc; arcs 0 .. 1228 each
#    exactly once; a copy as index.merged.json) and the okK_in fields of OUT/P<p>/C64NData/manifest_<p>.json into
#    ASM/m/C64NData/okk_in.json (module -> the file that holds its okK: C64NData.<M>, or the last KD file of a split
#    module);
# 2. writes C64NData/Hgn.lean, R<arc>.lean and Main.lean with gen_main_nest_k_v3.py --mirror, writes the native assembly
#    from the same index with gen_main_nest_r2.py --mirror into ASM/nref, and checks with check_k_vs_n_v3.py that the
#    kernel assembly states exactly what the native one states;
# 3. compiles Hgn, then the R modules (largest arcs first, JOBS at a time), then Main, each with
#      lean --root=ASM/m -DElab.async=false -o BUILD/C64NData/<X>.olean ASM/m/C64NData/<X>.lean
#    and LEAN_PATH = LIBPATH:BUILD (LIBPATH and LEAN as in build_modules_k.sh); logs in ASM/logs. The compiled assembly goes
#    next to the compiled data modules: Lean looks for all modules C64NData.* under the first search-path entry that has a
#    C64NData directory. Only the source path and the root enter the compiled files, not the output directory;
# 4. writes C64NData/Axioms.lean (#print axioms of constStatement, mainStatement and mainStatementEss), runs it into
#    ASM/logs/axioms.txt and checks it with check_axioms_k.py.
# Main imports every compiled module (about 211,500 data files plus the R modules): raise the open-file limit (done below
# if the hard limit allows) and vm.max_map_count (as root: sysctl -w vm.max_map_count=2000000) first. Memory, as in the
# native assembly: an R module up to ~9 GB, Main ~100 GB.
# NOMAIN=1 (for a test on a few parts): no arc check, Main written without the cover check and statements, not compiled.
set -u
OUT=$(cd "$1" && pwd); BUILD=$(cd "$2" && pwd); J=$3; NOMAIN=${NOMAIN:-0}; ASM=${ASM:-/k43/asm}
T=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$ASM/m/C64NData" "$ASM/nref/C64NData" "$ASM/logs" || exit 1
ASM=$(cd "$ASM" && pwd)
ulimit -n "$(ulimit -Hn)"
python3 -I - "$OUT" "$ASM/m/C64NData" "$NOMAIN" <<'PYEOF' || exit 1
import glob, json, os, sys
out, d, nomain = sys.argv[1], sys.argv[2], sys.argv[3] == "1"
L = []
for f in sorted(glob.glob(os.path.join(out, "P*", "C64NData", "index.json"))):
    L += json.load(open(f))
L.sort(key=lambda a: a["arc"])
got = [a["arc"] for a in L]
miss = sorted(set(range(1229)) - set(got)); dup = sorted({x for x in got if got.count(x) > 1})
json.dump(L, open(os.path.join(d, "index.json"), "w"))
json.dump(L, open(os.path.join(d, "index.merged.json"), "w"))
merged, bad = {}, 0
for p in sorted(glob.glob(os.path.join(out, "P*"))):
    for mf in glob.glob(os.path.join(p, "C64NData", "manifest_*.json")):
        for m, v in json.load(open(mf)).items():
            f = v["okK_in"]
            if m in merged and merged[m] != f:
                bad += 1
            merged[m] = f
json.dump(merged, open(os.path.join(d, "okk_in.json"), "w"))
mods = [a["name"] for a in L] + [sb["name"] for a in L for sb in a["subs"]]
nomod = [m for m in mods if m not in merged]
print("index: arcs", len(L), "subtrees", sum(len(a["subs"]) for a in L), "missing", len(miss), "duplicate", len(dup),
      "| okK_in: modules", len(merged), "in a KD file", sum(1 for m, f in merged.items() if f != "C64NData." + m),
      "conflicts", bad, "index modules without a manifest entry", len(nomod))
sys.exit(1 if bad or nomod or (not nomain and (miss or dup)) else 0)
PYEOF
if [ "$NOMAIN" = 1 ]; then NM=--no-main; else NM=; fi
python3 -I -B "$T/gen_main_nest_k_v3.py" "$ASM/m" --mirror $NM || exit 1
cp "$ASM/m/C64NData/index.json" "$ASM/nref/C64NData/index.json"
python3 -I -B "$T/gen_main_nest_r2.py" "$ASM/nref" --mirror $NM > /dev/null && python3 -I "$T/check_k_vs_n_v3.py" "$ASM/m" "$ASM/nref" \
  || { echo "the kernel assembly does not state what the native assembly states"; exit 1; }
LIBPATH=${LIBPATH:-$(lake env printenv LEAN_PATH)}; LEAN=${LEAN:-$(lake env which lean)}
export LEAN_PATH=$LIBPATH:$BUILD LEAN_NUM_THREADS=1 LEAN ASM BUILD
one() {
  m=$1; t0=$(date +%s%N)
  if $LEAN --root="$ASM/m" -DElab.async=false -o "$BUILD/C64NData/$m.olean" "$ASM/m/C64NData/$m.lean" > "$ASM/logs/$m.log" 2>&1
  then st=OK; else st=FAIL; fi
  echo "$st $(( ($(date +%s%N) - t0) / 1000000 ))" >> "$ASM/logs/$m.log"
  return 0
}
export -f one
one Hgn; tail -1 "$ASM/logs/Hgn.log" | grep -q '^OK' || { echo "Hgn failed"; exit 1; }
sort -k2 -n -r "$ASM/m/r_modules.txt" | awk '{print $1}' | xargs -P "$J" -n 1 bash -c 'one "$0"'
bad=0; for m in $(awk '{print $1}' "$ASM/m/r_modules.txt"); do tail -1 "$ASM/logs/$m.log" | grep -q '^OK' || bad=$((bad + 1)); done
echo "R modules $(wc -l < "$ASM/m/r_modules.txt"), failed $bad"; [ "$bad" = 0 ] || exit 1
[ "$NOMAIN" = 1 ] && exit 0
one Main; tail -1 "$ASM/logs/Main.log" | grep -q '^OK' || { echo "Main failed"; exit 1; }
printf 'import C64NData.Main\n\n#print axioms C64NData.constStatement\n#print axioms C64NData.mainStatement\n#print axioms C64NData.mainStatementEss\n' \
  > "$ASM/m/C64NData/Axioms.lean"
$LEAN --root="$ASM/m" -DElab.async=false "$ASM/m/C64NData/Axioms.lean" > "$ASM/logs/axioms.txt" 2>&1 || { echo "Axioms.lean failed"; exit 1; }
python3 -I "$T/check_axioms_k.py" "$ASM/logs/axioms.txt"
