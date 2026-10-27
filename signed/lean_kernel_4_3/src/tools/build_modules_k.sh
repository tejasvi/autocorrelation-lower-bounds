#!/bin/bash
# usage (in src/, after the library is compiled): tools/build_modules_k.sh OUT BUILD JOBS
# Compiles what export_parts_k.sh wrote. First C64NData/Glob.lean, once (the file is the same in every part; checked).
# Then, for all parts together, the files listed in OUT/P<p>/jobs.tsv, in three rounds:
#   1. the data modules (no dependencies);
#   2. the KD unit files of the split modules (each imports its data module);
#   3. the last KD file of each split module (the assembly and okK; it imports the data module and the unit files).
# Each round runs JOBS files at a time, largest estimate first, with the command of the original build
#   cd OUT/P<p> && lean -DElab.async=false -j1 --root=OUT/P<p> -o BUILD/C64NData/<X>.olean C64NData/<X>.lean
# and LEAN_PATH = LIBPATH:BUILD. LIBPATH defaults to `lake env printenv LEAN_PATH` and LEAN to `lake env which lean`, both
# run in the current directory. The data modules import only core Lean, C64Core and C64K files (never Mathlib), so their
# compiled files do not depend on the directories used.
# Memory: column 3 of jobs.tsv is the estimated peak memory of the file in GB (at most 21.9 GB), column 4 the estimated
# kernel seconds at full machine load. The memory estimates are often exceeded: in our build 11,602 files (5.5%) peaked
# above 22 GB, at most 70.8 GB (KD_A0170_2); of the files estimated at 21.9 GB the median peak was 16.3 GB and the 99.9th
# percentile 32.4 GB. This script sets no memory limit for a single file. Give it at least JOBS x 22 GB + 60 GB of RAM.
# If the machine still runs out of memory, the kernel stops some compiles, and their logs do not end with OK. Run the
# script again, with a smaller JOBS if needed: files whose log ends with OK are skipped, all others are compiled again.
# BUILD/logs/<X>.log ends with "OK ms" or "FAIL ms"; a file with an OK log is skipped. The last line of output is the
# number of failed or missing files, which must be 0.
set -u
OUT=$(cd "$1" && pwd); BUILD=$2; J=$3
mkdir -p "$BUILD/C64NData" "$BUILD/logs"; BUILD=$(cd "$BUILD" && pwd)
LIBPATH=${LIBPATH:-$(lake env printenv LEAN_PATH)}; LEAN=${LEAN:-$(lake env which lean)}
export LEAN_PATH=$LIBPATH:$BUILD LEAN_NUM_THREADS=1 LEAN OUT BUILD
first=$(ls -d "$OUT"/P* | grep -v '\.log$' | head -1)
for g in "$OUT"/P*/C64NData/Glob.lean; do cmp -s "$first/C64NData/Glob.lean" "$g" || { echo "Glob.lean differs: $g"; exit 1; }; done
if ! tail -1 "$BUILD/logs/Glob.log" 2>/dev/null | grep -q '^OK'; then
  t0=$(date +%s%N)
  if (cd "$first" && $LEAN -DElab.async=false -j1 --root="$first" -o "$BUILD/C64NData/Glob.olean" C64NData/Glob.lean) \
       > "$BUILD/logs/Glob.log" 2>&1; then st=OK; else st=FAIL; fi
  echo "$st $(( ($(date +%s%N) - t0) / 1000000 ))" >> "$BUILD/logs/Glob.log"
  [ $st = OK ] || { echo "Glob failed (see $BUILD/logs/Glob.log)"; exit 1; }
fi
one() {
  p=$1; x=$2
  tail -1 "$BUILD/logs/$x.log" 2>/dev/null | grep -q '^OK' && return 0
  t0=$(date +%s%N)
  if (cd "$OUT/$p" && $LEAN -DElab.async=false -j1 --root="$OUT/$p" -o "$BUILD/C64NData/$x.olean" "C64NData/$x.lean") \
       > "$BUILD/logs/$x.log" 2>&1; then st=OK; else st=FAIL; fi
  echo "$st $(( ($(date +%s%N) - t0) / 1000000 ))" >> "$BUILD/logs/$x.log"
  return 0
}
export -f one
# jobs.tsv: name, deps (comma list or -), est_gb, est_s, lean file, olean file; round = 1 (no deps), 2 (one), 3 (more)
for f in "$OUT"/P*/jobs.tsv; do
  p=$(basename "$(dirname "$f")")
  awk -F'\t' -v p="$p" '{n = ($2 == "-") ? 0 : split($2, a, ","); r = (n == 0) ? 1 : ((n == 1) ? 2 : 3); print r, $4, p, $1}' "$f"
done | sort -k1,1n -k2,2nr > "$BUILD/files.txt"
for r in 1 2 3; do
  awk -v r=$r '$1 == r {print $3, $4}' "$BUILD/files.txt" | xargs -P "$J" -n 2 bash -c 'one "$0" "$1"'
done
bad=0; while read -r r s p x; do tail -1 "$BUILD/logs/$x.log" 2>/dev/null | grep -q '^OK' || bad=$((bad + 1)); done < "$BUILD/files.txt"
echo "files $(wc -l < "$BUILD/files.txt")"
echo "$bad"
