#!/bin/bash
# usage (in src/): tools/export_parts_k.sh PARTS HINTS OUT JOBS
# Writes the kernel data modules of the upper half from the certificate parts and the hint files, without the compiled
# native data. For each part p = 000 .. 1228 (file PARTS/cert_t25_sub_<p>.json.gz; directory HINTS/P<p>/ from the hint
# archive), OUT/P<p>/ gets C64NData/Glob.lean, the K data modules C64NData/<M>.lean (C64NData/KD_<M>_<k>.lean for the
# split modules), C64NData/index.json, C64NData/manifest_<p>.json and jobs.tsv, as gen_nest_data_k_v2.py k writes them.
# HINTS/P<p>/<M>.hb holds the hints of module M, one line `HB <path> <step> <hex>` per hinted step, and one line
# `HBFAIL ...` per step whose hint search failed (the generator only counts those). HINTS/P<p>/ntimes.tsv gives, for each
# module, the compile time in ms of its native data module (the "OK <ms>" of its build log). The generator adds 0.3 of it to
# the estimate that decides whether a module is split, so it is passed on as logs OUT/ntimes/P<p>/<M>.log ("OK <ms>").
# JOBS parts at a time; a finished part is skipped. Needs Python 3 with python-flint 0.9.0 (PYFLINT=<dir> adds the
# directory of an unpacked wheel to the search path instead). Prints "exported N of 1229"; exits 1 unless N = 1229.
# ONLY="082 1092" (for a test) exports only the listed parts and exits 1 unless all of them are exported.
set -u
PARTS=$(cd "$1" && pwd); HINTS=$(cd "$2" && pwd); OUT=$3; J=$4
T=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$OUT/ntimes"; OUT=$(cd "$OUT" && pwd)
one() {
  p=$1
  [ -e "$OUT/P$p/exported" ] && return 0
  [ -s "$HINTS/P$p/ntimes.tsv" ] || { echo "no $HINTS/P$p/ntimes.tsv" > "$OUT/P$p.log"; return 0; }
  mkdir -p "$OUT/ntimes/P$p"
  awk -F'\t' -v d="$OUT/ntimes/P$p" '$2 != "-" {f = d "/" $1 ".log"; print "OK " $2 > f; close(f)}' "$HINTS/P$p/ntimes.tsv"
  python3 -I -B "$T/gen_nest_data_k_v2.py" k "$PARTS/cert_t25_sub_$p.json.gz" "$OUT/P$p" --upper --max-recs 16000 \
    --index-offset $((10#$p)) --part-id "$p" --hints "$HINTS/P$p" --ntimes "$OUT/ntimes/P$p" ${PYFLINT:+--pyflint "$PYFLINT"} \
    > "$OUT/P$p.log" 2>&1 && touch "$OUT/P$p/exported"
  return 0
}
export -f one; export PARTS HINTS OUT T PYFLINT
if [ -n "${ONLY:-}" ]; then L=$(echo $ONLY | tr ' ' '\n'); else L=$(seq 0 1228 | awk '{printf "%03d\n", $1}'); fi
echo "$L" | xargs -P "$J" -n 1 bash -c 'one "$0"'
want=$(echo "$L" | grep -c .)
n=0; for p in $L; do [ -e "$OUT/P$p/exported" ] && n=$((n + 1)); done
echo "exported $n of $want"
[ "$n" = "$want" ]
