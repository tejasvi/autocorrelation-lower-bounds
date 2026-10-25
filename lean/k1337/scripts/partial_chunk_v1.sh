#!/bin/bash
# partial_chunk_v1.sh SID C JOB... (K1337 tailfix; run as root on the fleet VM of SID, script on stdin:
# `sudo bash -s SID C JOB... < partial_chunk_v1.sh`; DRY=1 as first arg pair "DRY 1" is not used: set env DRY=1 on the
# remote side instead). Chunk C of SID waits only on the tail job(s) JOB. This ships every OTHER module of chunk C with the
# node's own upchunk commands (k39node3b.sh 112-118: .files, .sha256, .times, tar of build/ members) to
# ${RESULTS_URL}/k39/tailfix_partial/SID/ (never the fleet prefix): chunk_C.{tar,sha256,meta.jsonl,times,
# mods,excluded.txt,excluded_meta.jsonl}, then chunk_C.PARTIAL (marker, last). Refuses unless every remaining module has
# rc=0 (all.rc or prev_ok.txt, the uploader's test) and an .olean, and the counts add up. Work files in out/tailfix_c<C>/.
set -u
SID=$1; C=$2; shift 2; JOBS="$*"; DRY=${DRY:-0}
O=/k39/out; RP=${RESULTS_URL}/k39/tailfix_partial/$SID; T=$O/tailfix_c$C
cd $O || exit 1
[ -n "$JOBS" ] && [ -f chunk_$C.mods ] && [ -f chunk_$C.meta.jsonl ] || { echo "FAIL inputs"; exit 1; }
[ -e chunk_$C.DONE ] && { echo "FAIL chunk $C already shipped by the node"; exit 1; }
mkdir -p $T
python3 -I - $O/chunk_$C.meta.jsonl $T $JOBS <<'PY' || { echo "FAIL meta split"; exit 2; }
import json, sys
fn, T, jobs = sys.argv[1], sys.argv[2], set(sys.argv[3:])
keep, xmeta, xmods, found = [], [], [], set()
for line in open(fn):
    d = json.loads(line)
    if d["j"] in jobs:
        found.add(d["j"]); xmeta.append(line); xmods += d["m"]
    else:
        keep.append(line)
if found != jobs:
    sys.exit("jobs not in chunk meta: " + " ".join(sorted(jobs - found)))
open(f"{T}/meta_keep.jsonl", "w").write("".join(keep))
open(f"{T}/excluded_meta.jsonl", "w").write("".join(xmeta))
open(f"{T}/excluded.txt", "w").write("".join(m + "\n" for m in xmods))
PY
grep -vxF -f $T/excluded.txt chunk_$C.mods > $T/mods.txt
n_all=$(wc -l < chunk_$C.mods); n_x=$(wc -l < $T/excluded.txt); n=$(wc -l < $T/mods.txt)
[ $((n + n_x)) -eq $n_all ] || { echo "FAIL counts $n + $n_x != $n_all"; exit 3; }
[ -f prev_ok.txt ] && PO=prev_ok.txt || { : > $T/prev_none.txt; PO=$T/prev_none.txt; }
read no nb < <(awk -v F=$T/mods.txt -v P=$PO 'FILENAME == F {want[$1] = 1; next}
  FILENAME == P {if ($1 in want) ok[$1] = 1; next}
  ($1 in want) {if ($2 == "rc=0") ok[$1] = 1; else bad[$1] = 1}
  END {nb = 0; for (m in bad) if (!(m in ok)) nb++; no = 0; for (m in ok) no++; print no, nb}' $T/mods.txt $PO all.rc)
[ "$nb" = 0 ] && [ "$no" = "$n" ] || { echo "FAIL rc: ok $no bad $nb of $n"; exit 4; }
sed 's#\.#/#g; s#$#.olean#' $T/mods.txt > $T/files.txt
(cd build && xargs -a $T/files.txt sha256sum) > $T/sha256.txt || { echo "FAIL sha256 (missing olean?)"; exit 5; }
(cd build && sed 's#\.olean$#.time#' $T/files.txt | xargs -I{} sh -c 'echo "{} $(cat {})"') > $T/times.txt
[ $(wc -l < $T/sha256.txt) -eq $n ] && [ $(wc -l < $T/times.txt) -eq $n ] || { echo "FAIL list lengths"; exit 5; }
if [ "$DRY" = 1 ]; then
  b=$(tar -cf - -C build -T $T/files.txt | wc -c)
  echo "DRY partial chunk $C of $SID: $n modules ($b tar bytes), $n_x excluded ($JOBS); nothing uploaded"; exit 0
fi
tar -cf - -C build -T $T/files.txt | gcloud storage cp - $RP/chunk_$C.tar > /dev/null 2>> $T/upload.log || { echo "FAIL tar upload"; exit 6; }
cp $T/sha256.txt $T/chunk_$C.sha256; cp $T/meta_keep.jsonl $T/chunk_$C.meta.jsonl; cp $T/times.txt $T/chunk_$C.times
cp $T/mods.txt $T/chunk_$C.mods; cp $T/excluded.txt $T/chunk_$C.excluded.txt; cp $T/excluded_meta.jsonl $T/chunk_$C.excluded_meta.jsonl
gcloud storage cp $T/chunk_$C.sha256 $T/chunk_$C.meta.jsonl $T/chunk_$C.times $T/chunk_$C.mods $T/chunk_$C.excluded.txt \
  $T/chunk_$C.excluded_meta.jsonl $RP/ > /dev/null 2>> $T/upload.log || { echo "FAIL list upload"; exit 7; }
echo "partial chunk $C of $SID: $n modules shipped, $n_x excluded ($JOBS), $(date -u +%FT%TZ)" > $T/chunk_$C.PARTIAL
gcloud storage cp $T/chunk_$C.PARTIAL $RP/ > /dev/null 2>> $T/upload.log || { echo "FAIL marker upload"; exit 8; }
cat $T/chunk_$C.PARTIAL
