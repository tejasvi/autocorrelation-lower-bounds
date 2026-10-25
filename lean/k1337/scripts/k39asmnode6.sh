#!/bin/bash
# k39asmnode6.sh STAGE... (v6 = v5 with the bundle file names as delivered [TF_SUMS tailfix6.sha256, TF_TAR
# tailfix6_modules.tar, TF_META meta_tailfix6.jsonl, TF_MAN MANIFEST6.tsv; 6 cured jobs]; never edit in place;
# v5 = v4 whose tailfix stage reads the single re-export bundle k39/tailfix/ [tailfix_modules.tar,
# meta_tailfix.jsonl, MANIFEST.tsv, tailfix.sha256; checked by tools4/tailfix_bundle_check.py, per-job lists by
# tools4/tailfix_job_files.py] and publishes the per-job sha256 lists to k39/tailfix_lists/; never edit in place;
# v4: + stage tailfix [the re-segmented v1 rebuilds of the K1337 tail jobs: per line of
# /data/w/tailfix_jobs.tsv, the fleet's partial chunk + the re-export's rebuild of that job, one source per job, checked by
# tools4/tailfix_check.py] and stage plandry [k39asm plan into a fresh plan_dry_<time>/, never cached]; plan runs only
# after a plandry OK over the same meta set; scan never rm -rf (an independent review preceded the tailfix merge);
# v3: psrc takes any 6 items' Params.lean; v2: setup idempotent, psrc stage; never edit in place):
# the K1337 assembly VM (224 vCPUs, 2.9 TB, data disk on /data).
# Stages, each writes /data/w/state/<stage>.done ("OK ..."/"FAIL ..."), skipped once OK:
#   setup    bundle (toolchain, Mathlib, Autocorr; kit c36lean.tar.zst) + K39 library (k39lib.tar) + tools
#   psrc     KC1337/Params.lean from the fleet (s00), equal to three other items' copies
#   params   KC1337.Params built here (same text as the fleet's, checked)
#   fetch    every finished chunk not yet here: chunk_<c>.tar extracted into out/build, its olean sha256 list checked,
#            its metadata kept (run again until all 950 chunks of the 95 items are in)
#   touch    5% test: one module importing every check module of the chunks present (up to TOUCH_MAX modules); /usr/bin/time
#            max RSS and the page-cache residency (fincore) of those oleans before/after -> touch.txt (extrapolate x 1/share)
#   plan     k39asm.py over all metadata: G modules, Top, Main, Forms (approved template)
#   build    G modules in parallel (NJ), then Top, Main, Forms, each under /usr/bin/time
#   scan     kscan over every KC1337 olean (64 parts) + kscan_ext39 on the external references; #print axioms is not run
#   results  plan, Main, Forms, scan outputs, olean sha256 lists, times -> ${RESULTS_URL}/k39/results/
set -u
W=${K1337_ASM_W:-/data/w}; K=${RESULTS_URL}/k39;   # K1337_ASM_W: a scratch copy for tests
K=${K1337_ASM_K:-$K}; F=$K/fleet; RS=${K1337_ASM_RS:-$K/results}
# a test copy (K1337_ASM_W set) must write its stage files to its own results prefix, never the real one
if [ -n "${K1337_ASM_W:-}" ] && { [ -z "${K1337_ASM_RS:-}" ] || [ -z "${K1337_ASM_LISTS:-}" ]; }; then echo "test dir without K1337_ASM_RS/K1337_ASM_LISTS: refused"; exit 4; fi
mkdir -p $W/state $W/log
NJ=${NJ:-$(( $(getconf _NPROCESSORS_ONLN) - 8 ))}
T=$W/.elan/toolchains/leanprover--lean4---v4.35.0-rc3; P=$W/lean_c133_prod; D=$P/.lake/build/lib/lean
LP=$W/out/build:$W/k39lib:$D
for p in Cli batteries Qq aesop proofwidgets importGraph LeanSearchClient plausible mathlib; do LP=$LP:$P/.lake/packages/$p/.lake/build/lib/lean; done
export LEAN_PATH=$LP:$T/lib/lean LEAN_NUM_THREADS=1 OMP_NUM_THREADS=1 AUTOCORR_CHECKER=$W/tools T
ulimit -n $(ulimit -Hn); ulimit -s unlimited
ok() { grep -q "^OK" $W/state/$1.done 2>/dev/null; }
done_() { echo "$2" > $W/state/$1.done; echo "=== $1 $(date -u +%FT%TZ) $2"; gcloud storage cp $W/state/$1.done $RS/state/$1.done > /dev/null 2>&1; case "$2" in OK*) ;; *) exit 1;; esac; }
lb() { o=build/$(echo $1 | tr . /); mkdir -p $(dirname $o); /usr/bin/time -f "%e %U %S %M" -o $o.time $T/bin/lean -DElab.async=false -o $o.olean $(echo $1 | tr . /).lean > $o.log 2>&1; echo "$1 rc=$?"; }
export -f lb
for S in "$@"; do
  [ "$S" != fetch ] && [ "$S" != plandry ] && ok $S && { echo "=== $S already OK"; continue; }
  echo "=== $S start $(date -u +%FT%TZ) avail $(awk '/MemAvailable/ {printf "%.0f GB", $2/1e6}' /proc/meminfo), /data free $(df -BG --output=avail /data | tail -1 | tr -d ' ')"
  case $S in
  setup)
    cd $W
    if [ ! -f .bundle_ok ]; then
      gcloud storage cp ${RESULTS_URL}/kit/c36lean.tar.zst . > $W/log/setup.log 2>&1 && zstd -dc c36lean.tar.zst | tar -x && rm -f c36lean.tar.zst && touch .bundle_ok \
        || done_ setup "FAIL bundle"
    fi
    gcloud storage cp $K/kit2/k39lib.tar $K/kit3/asmtools.tar . >> $W/log/setup.log 2>&1 || done_ setup "FAIL download"
    rm -rf k39lib && mkdir -p k39lib && tar -xf k39lib.tar -C k39lib && tar -xf asmtools.tar || done_ setup "FAIL unpack"
    done_ setup "OK $($T/bin/lean --version | head -1 | cut -c1-40); NJ $NJ";;
  psrc)
    cd $W && mkdir -p out/KC1337 && gcloud storage ls "$F/*/Params.lean" > psrc_list.txt 2>/dev/null
    [ "$(wc -l < psrc_list.txt)" -ge 4 ] || done_ psrc "FAIL fewer than 4 items have uploaded Params.lean"
    gcloud storage cp $(head -1 psrc_list.txt) out/KC1337/Params.lean >> $W/log/setup.log 2>&1 || done_ psrc "FAIL Params source"
    for u in $(tail -n +2 psrc_list.txt | head -5); do gcloud storage cat $u 2>/dev/null | cmp -s - out/KC1337/Params.lean || done_ psrc "FAIL Params differs: $u"; done
    done_ psrc "OK Params.lean $(sha256sum < out/KC1337/Params.lean | cut -c1-16) from $(head -1 psrc_list.txt | sed 's#.*/fleet/##') = 5 other items' copies";;
  params)
    cd $W/out && r=$(lb KC1337.Params) && [ "$r" = "KC1337.Params rc=0" ] || done_ params "FAIL (build/KC1337/Params.log)"
    done_ params "OK $(cat build/KC1337/Params.time)";;
  fetch)
    cd $W && mkdir -p chunks meta && touch fetched.txt
    gcloud storage ls "$F/*/chunk_*.DONE" 2>/dev/null | sed 's#\.DONE$##' > avail.txt
    n0=$(wc -l < fetched.txt)
    grep -vxF -f fetched.txt avail.txt > todo.txt
    cat todo.txt | xargs -P 16 -I{} bash -c 'set -o pipefail; c={}; id=$(basename $(dirname $c))_$(basename $c); gcloud storage cat $c.tar | tar -x -C '$W'/out/build && gcloud storage cp $c.sha256 '$W'/chunks/$id.sha256 > /dev/null 2>&1 && gcloud storage cp $c.meta.jsonl '$W'/meta/$id.meta.jsonl > /dev/null 2>&1 && (cd '$W'/out/build && sha256sum -c --quiet '$W'/chunks/$id.sha256) && echo $c >> '$W'/fetched.txt || echo "FAILED $c" >> '$W'/log/fetch_fail.txt'
    [ -s $W/log/fetch_fail.txt ] && done_ fetch "FAIL $(wc -l < $W/log/fetch_fail.txt) chunks (log/fetch_fail.txt)"
    done_ fetch "OK $(wc -l < fetched.txt) of 950 chunks here (+$(( $(wc -l < fetched.txt) - n0 )))";;
  touch)
    cd $W/out && cat $W/meta/*.meta.jsonl | python3 -c "
import sys, json
mods = [m for l in sys.stdin for m in json.loads(l)['m']]
mx = int(sys.argv[1]); mods = mods[:mx]
open('touch_mods.txt', 'w').write(''.join(m + '\n' for m in mods))
open('KC1337/TouchTest.lean', 'w').write('import KC1337.Params\n' + ''.join(f'import {m}\n' for m in mods) + '\n#eval (1 : Nat)\n')
" ${TOUCH_MAX:-400000}
    sed 's#\.#/#g; s#^#build/#; s#$#.olean#' touch_mods.txt > touch_files.txt
    tb=$(cat touch_files.txt | xargs -P 32 -n 2000 stat -c %s | awk '{s+=$1} END {print s}')
    echo 3 | sudo tee /proc/sys/vm/drop_caches > /dev/null
    /usr/bin/time -f "%e %U %S %M %F" -o touch.time $T/bin/lean -DElab.async=false KC1337/TouchTest.lean > touch.log 2>&1 || done_ touch "FAIL (out/touch.log)"
    rb=$(cat touch_files.txt | xargs -P 32 -n 2000 fincore -b -n -o RES 2>/dev/null | awk '{s+=$1} END {print s}')
    share=$(python3 -c "print($(wc -l < touch_mods.txt) / $(cat $W/meta/*.meta.jsonl | python3 -c 'import sys,json; print(sum(len(json.loads(l)[\"m\"]) for l in sys.stdin))'))")
    echo "touch: modules $(wc -l < touch_mods.txt), olean bytes $tb, resident after import $rb, time (e U S maxrssKB majflt) $(cat touch.time)" > touch.txt
    done_ touch "OK $(cat touch.txt)";;
  tailfix)
    cd $W && mkdir -p chunks meta tailfix && touch fetched.txt && : > log/tailfix_fail.txt
    [ -s tailfix_jobs.tsv ] || done_ tailfix "FAIL no tailfix_jobs.tsv"
    B=$W/tailfix/bundle; TFS=${TF_SUMS:-tailfix6.sha256}; TFT=${TF_TAR:-tailfix6_modules.tar}; TFM=${TF_META:-meta_tailfix6.jsonl}; TFN=${TF_MAN:-MANIFEST6.tsv}
    if [ ! -e $B/OK ]; then
      mkdir -p $B/x && gcloud storage cp "$K/tailfix/*" $B/ > /dev/null 2>&1 || done_ tailfix "FAIL bundle download"
      tar -xf $B/$TFT -C $B/x || done_ tailfix "FAIL bundle tar"
      python3 -I $W/tools4/tailfix_bundle_check.py $B $TFS $TFT $TFM $TFN > $B/check.txt 2>&1 || done_ tailfix "FAIL bundle: $(tail -1 $B/check.txt)"
      echo "$(date -u +%FT%TZ) $(tail -1 $B/check.txt)" > $B/OK
    fi
    nt=0; nf=0
    while read -r sid c job src <&3; do
      [ -n "$sid" ] || continue
      id=${sid}_chunk_$c; fc=$F/$sid/chunk_$c; TP=$K/tailfix_partial/$sid; TF=$K/tailfix/$sid; d=tailfix/$id
      if [ "$src" = fleet ]; then
        grep -qxF "$fc" fetched.txt && [ ! -e $d/MERGED ] && grep -q "\"j\": \"$job\"" meta/$id.meta.jsonl \
          && { nf=$((nf+1)); continue; }
        echo "$id: fleet chunk of $job not fetched (or merged from tailfix)" >> log/tailfix_fail.txt; continue
      fi
      [ "$src" = tailfix ] || { echo "$id: source $src?" >> log/tailfix_fail.txt; continue; }
      [ -e $d/MERGED ] && { nt=$((nt+1)); continue; }
      grep -qxF "$fc" fetched.txt && { echo "$id: the fleet chunk is here, so $job stays fleet" >> log/tailfix_fail.txt; continue; }
      gcloud storage cat $TP/chunk_$c.PARTIAL > /dev/null 2>&1 || { echo "$id: PARTIAL marker missing" >> log/tailfix_fail.txt; continue; }
      mkdir -p $d
      gcloud storage cp $TP/chunk_$c.sha256 $TP/chunk_$c.meta.jsonl $TP/chunk_$c.mods $TP/chunk_$c.excluded.txt \
        $TP/chunk_$c.excluded_meta.jsonl $TP/chunk_$c.times $TP/chunk_$c.PARTIAL $d/ > /dev/null 2>&1 \
        || { echo "$id: list download" >> log/tailfix_fail.txt; continue; }
      python3 -I $W/tools4/tailfix_job_files.py $B/x $B/$TFM $job $W/$d > $d/files_check.txt 2>&1 \
        || { echo "$id: $(tail -1 $d/files_check.txt)" >> log/tailfix_fail.txt; continue; }
      (set -o pipefail; gcloud storage cat $TP/chunk_$c.tar | tar -x -C $W/out/build) \
        && (set -o pipefail; cd $B/x/build && tar -cf - -T $W/$d/files.txt | tar -x -C $W/out/build) || { echo "$id: tar" >> log/tailfix_fail.txt; continue; }
      (cd $W/out/build && sha256sum -c --quiet $W/$d/chunk_$c.sha256 && sha256sum -c --quiet $W/$d/sha256) \
        || { echo "$id: sha256" >> log/tailfix_fail.txt; continue; }
      python3 -I $W/tools4/tailfix_check.py $W/$d $job $W/out/build > $d/check.txt 2>&1 \
        || { echo "$id: $(tail -1 $d/check.txt)" >> log/tailfix_fail.txt; continue; }
      cat $d/chunk_$c.meta.jsonl $d/job_meta.jsonl > meta/$id.meta.jsonl
      cp $d/chunk_$c.sha256 chunks/$id.sha256 && cp $d/sha256 chunks/$id.tailfix.sha256
      echo "$fc" >> fetched.txt; echo "$(date -u +%FT%TZ) $(cat $d/check.txt)" > $d/MERGED; nt=$((nt+1))
    done 3< tailfix_jobs.tsv
    [ -s log/tailfix_fail.txt ] && done_ tailfix "FAIL $(wc -l < log/tailfix_fail.txt) jobs (log/tailfix_fail.txt)"
    ls chunks/*.tailfix.sha256 > /dev/null 2>&1 && { gcloud storage cp chunks/*.tailfix.sha256 ${K1337_ASM_LISTS:-$K/tailfix_lists}/ > /dev/null 2>&1 \
      || done_ tailfix "FAIL publishing the tailfix sha256 lists"; }
    done_ tailfix "OK $nt jobs from tailfix, $nf kept from the fleet; $(wc -l < fetched.txt) of 950 chunks here";;
  plandry)
    cd $W && pd=plan_dry_$(date -u +%Y%m%dT%H%M%S) && mkdir $pd || done_ plandry "FAIL mkdir"
    nm=$(ls meta/*.meta.jsonl | wc -l); [ "$nm" = 950 ] || done_ plandry "FAIL $nm meta files, not 950"
    mh=$(cat $(ls meta/*.meta.jsonl) | sha256sum | cut -c1-16)
    python3 tools/k39asm.py plan $pd KC1337 Autocorr.KC1337 39 1337 1000 $(ls meta/*.meta.jsonl) --forms tools/C1337_Forms.lean > log/$pd.log 2>&1 \
      || done_ plandry "FAIL $(tail -c 300 log/$pd.log)"
    done_ plandry "OK meta $mh ($nm files) $pd: $(tail -1 log/$pd.log)";;
  plan)
    cd $W && mh=$(cat $(ls meta/*.meta.jsonl) | sha256sum | cut -c1-16)
    grep -q "^OK meta $mh " state/plandry.done 2>/dev/null || done_ plan "FAIL no plandry OK over this meta set ($mh)"
    cd $W && python3 tools/k39asm.py plan out KC1337 Autocorr.KC1337 39 1337 1000 $(ls meta/*.meta.jsonl) --forms tools/C1337_Forms.lean > log/plan.log 2>&1 \
      || done_ plan "FAIL $(tail -c 300 log/plan.log)"
    done_ plan "OK $(tail -1 log/plan.log)";;
  build)
    cd $W/out && grep '\.G' modules.txt | xargs -P $NJ -I{} bash -c 'lb {}' > g.rc
    nbad=$(grep -vc "rc=0" g.rc); [ "$nbad" = 0 ] || done_ build "FAIL $nbad G modules (out/g.rc)"
    for m in $(grep -v '\.G' modules.txt); do r=$(lb $m); [ "$r" = "$m rc=0" ] || done_ build "FAIL $m"; done
    done_ build "OK $(grep -c '\.G' modules.txt) G modules + Top + Main + Forms; Top $(cat build/KC1337/Top.time); Forms $(cat build/KC1337/Forms.time)";;
  scan)
    cd $W/out && { mkdir nscan || done_ scan "FAIL out/nscan exists (move it aside by hand)"; } && find build/KC1337 -name '*.olean' | sort > nscan/all.txt
    split -n l/64 -d -a 2 nscan/all.txt nscan/part_
    for f in nscan/part_??; do (LEAN_PATH=$T/lib/lean $T/bin/lean --run $W/tools/kscan.lean $f $f.out Autocorr.KC1337. > $f.log 2>&1; echo "rc=$?" >> $f.log) & done; wait
    [ "$(grep -h 'rc=0' nscan/part_*.log | wc -l)" = 64 ] || done_ scan "FAIL kscan runs"
    v=$(grep -h "^modules" nscan/part_*.out | awk '{v+=$6} END {print v+0}'); m=$(grep -h "^modules" nscan/part_*.out | awk '{m+=$2; c+=$4} END {print m+0, c+0}')
    for f in nscan/part_*.out; do sed -n '/^external/,$p' $f | tail -n +2; done | sort -u > nscan/external.txt
    KSCAN_EXT=$W/out/nscan/external.txt $T/bin/lean $W/tools/kscan_ext39.lean > nscan/ext.txt 2>&1
    grep -q "missing 0" nscan/ext.txt && grep -q "axioms of the external references: \[" nscan/ext.txt || done_ scan "FAIL kscan_ext39"
    [ "$v" = 0 ] || done_ scan "FAIL kscan violations $v"
    done_ scan "OK modules/constants $m, violations 0; $(tail -1 nscan/ext.txt)";;
  results)
    cd $W/out && mkdir -p res && cp $W/plan.json KC1337/Main.lean KC1337/Forms.lean KC1337/Top.lean nscan/ext.txt nscan/external.txt res/ 2>/dev/null
    cp $W/out/plan.json res/ 2>/dev/null; cat nscan/part_*.out | grep "^modules" > res/kscan_modules.txt; cat $W/state/*.done > res/stages.txt
    cat $W/chunks/*.sha256 | gzip -c > res/k1337_check_oleans.sha256.gz
    (cd build && find KC1337 -maxdepth 1 -name '*.olean' | sort | xargs sha256sum) > res/k1337_top_oleans.sha256
    gcloud storage cp res/* $RS/ > $W/log/results.log 2>&1 || done_ results "FAIL upload"
    done_ results "OK uploaded to $RS/";;
  esac
done
echo "=== asm end $(date -u +%FT%TZ)"
