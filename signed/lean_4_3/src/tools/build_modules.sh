#!/bin/bash
# usage (in src/, after `lake build C64Core C64Core.Load C64.Check.SoundMirror`): tools/build_modules.sh OUT BUILD JOBS
# Compiles the data written by export_parts.sh: C64NData/Glob.lean once (the same file in every part), then every data module
# (they are independent of each other), largest first, JOBS at a time, with the checker's compiled libraries loaded, into
# BUILD/C64NData/<module>.olean. BUILD/logs/<module>.log ends with "OK ms" or "FAIL ms"; a module with an OK log is skipped.
# The last line of output is the number of failed or missing modules, which must be 0.
set -u
OUT=$(cd "$1" && pwd); BUILD=$2; J=$3
mkdir -p "$BUILD/C64NData" "$BUILD/logs"; BUILD=$(cd "$BUILD" && pwd)
D=$(pwd)/.lake/build/lib/lean
export DYN="--load-dynlib=$D/LeanC64_C64Core_Ival.so --load-dynlib=$D/LeanC64_C64Core_Num.so --load-dynlib=$D/LeanC64_C64Core_Check.so --load-dynlib=$D/LeanC64_C64Core_Nest.so"
export LEAN_PATH=$(lake env printenv LEAN_PATH):$BUILD LEAN_NUM_THREADS=1 OUT BUILD
LEAN=$(lake env which lean); export LEAN
first=$(ls -d "$OUT"/P* | head -1)
for p in "$OUT"/P*/C64NData/Glob.lean; do cmp -s "$first/C64NData/Glob.lean" "$p" || { echo "Glob.lean differs: $p"; exit 1; }; done
[ -f "$BUILD/C64NData/Glob.olean" ] || $LEAN $DYN --root="$first" -o "$BUILD/C64NData/Glob.olean" "$first/C64NData/Glob.lean" > "$BUILD/logs/Glob.log" 2>&1 \
  || { echo "Glob failed (see $BUILD/logs/Glob.log)"; exit 1; }
one() {
  p=$1; m=$2
  tail -1 "$BUILD/logs/$m.log" 2>/dev/null | grep -q '^OK' && return 0
  t0=$(date +%s%N)
  if $LEAN $DYN --root="$OUT/$p" -o "$BUILD/C64NData/$m.olean" "$OUT/$p/C64NData/$m.lean" > "$BUILD/logs/$m.log" 2>&1; then st=OK; else st=FAIL; fi
  echo "$st $(( ($(date +%s%N) - t0) / 1000000 ))" >> "$BUILD/logs/$m.log"
  return 0
}
export -f one
for f in "$OUT"/P*/C64NData/A*.lean; do echo "$(stat -c %s "$f") $(basename "$(dirname "$(dirname "$f")")") $(basename "$f" .lean)"; done \
  | sort -n -r | awk '{print $2, $3}' > "$BUILD/modules.txt"
xargs -P "$J" -n 2 bash -c 'one "$0" "$1"' < "$BUILD/modules.txt"
bad=0; while read -r p m; do tail -1 "$BUILD/logs/$m.log" 2>/dev/null | grep -q '^OK' || bad=$((bad + 1)); done < "$BUILD/modules.txt"
echo "modules $(wc -l < "$BUILD/modules.txt")"
echo "$bad"
