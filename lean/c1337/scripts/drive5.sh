#!/bin/bash
# drive5.sh [STAGE...] (drive3.sh with tools/export_shard_v2.py: gc.freeze() before the pass-2 fork pool; drive3's export OOMed in pass 2): Lean N proof of C1 >= 1337/1000 from the c1337 certificate on one VM (run under coreh_guard_v2).
# Stages, in order; each writes /scratch/c1337/state/<stage>.done ("OK ..." or "FAIL ...") and is skipped once OK:
#   fetch    178 D-log tars + run/meta.json + the VMs' jobs_*.sha256 lists from the certificate bucket; extract to cert/jobs
#   scan     sha256 + size + gzip + tree-only (U/T) count of every job file; the file set must equal the certificate's list
#   ufill    the frozen dump verifier (34da7947, VT_DUMP_DIR) fills the tree-only leaves; filled copies replace the originals
#   export   export_shard.py --pack --group-check --fast --group-leaves 1000 --main  (CheckerXF + GroupCheckX)
#   jobmap   per group module, the jobs it checks (from the generated jobIds manifests, before the build removes the
#            sources); must cover every job file (5,033,964 incl. root.jsonl.gz) exactly once with its input sha256
#   forms    forms.py C1337 39 1337 1000; generated statements diffed against the reviewed proposal (kit/)
#   build    build_dag.py (native, 6 checker dynlibs), memory admission (start a module only with >= 150 GB available,
#            kill the youngest below 50 GB; no per-module address-space cap: Main and Forms map the whole closure),
#            sources removed as built
#   axioms   #print axioms of the three theorems; nscan_xf over every module (strict); nscan_ext_xf on the external refs
#   results  summary + statements + axioms + scans + sha lists + logs -> $RESULTS_URL/
set -u
C=/scratch/c1337; P=/scratch/c36/lean_c133_prod; T=/scratch/c36/.elan/toolchains/leanprover--lean4---v4.35.0-rc3
D=$P/.lake/build/lib/lean; KIT=/scratch/c36/kit; B=${CERT_URL:?set CERT_URL to the certificate location}; R=${RESULTS_URL:?set RESULTS_URL to the results location}
LP=$(for p in Cli batteries Qq aesop proofwidgets importGraph LeanSearchClient plausible mathlib; do printf "%s:" $P/.lake/packages/$p/.lake/build/lib/lean; done)$D:$T/lib/lean
export PATH=$T/bin:$PATH AUTOCORR_CHECKER=/scratch/c36 LEAN_NUM_THREADS=1 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
ulimit -n $(ulimit -Hn)
[ "$(ulimit -Sn)" -ge 65536 ] || { echo "FAIL open-file limit $(ulimit -Sn)"; exit 1; }
NJ=$(( $(getconf _NPROCESSORS_ONLN) - 20 ))
[ "$NJ" -ge 16 ] || { echo "FAIL worker count $NJ"; exit 1; }
mkdir -p $C/state $C/log $C/cert/jobs $C/tars
DYN=""; for l in Checker Decode CheckerX DecodeX GroupCheckX CheckerXF; do DYN="$DYN --dynlib $D/Autocorr_AutocorrCert_$l.so"; done
ok() { grep -q "^OK" $C/state/$1.done 2>/dev/null; }
done_() { echo "$2" > $C/state/$1.done; echo "=== $1 $(date -u +%FT%TZ) $2"; case "$2" in OK*) ;; *) exit 1;; esac; }
start() { echo "=== $1 start $(date -u +%FT%TZ) avail $(awk '/MemAvailable/ {printf "%.0f GB", $2/1e6}' /proc/meminfo), /scratch free $(df -BG --output=avail /scratch | tail -1 | tr -d ' ')"; }
STAGES=${*:-fetch scan ufill export jobmap forms build axioms results}
for S in $STAGES; do
  ok $S && { echo "=== $S already OK"; continue; }
  start $S
  case $S in
  fetch)
    gcloud storage cp $B/run/meta.json $C/cert/meta.json > $C/log/fetch.log 2>&1 || done_ fetch "FAIL meta"
    [ "$(sha256sum $C/cert/meta.json | cut -c1-8)" = 5fa65703 ] || done_ fetch "FAIL meta sha"
    gcloud storage cat "$B/summaries/*/jobs_*.sha256" > $C/expected_jobs.sha256 2>> $C/log/fetch.log || done_ fetch "FAIL job lists"
    gcloud storage cp "$B/dlogs/*.tar" $C/tars/ >> $C/log/fetch.log 2>&1 || done_ fetch "FAIL tar download"
    n=$(ls $C/tars/*.tar | wc -l); [ "$n" = 178 ] || done_ fetch "FAIL $n tars"
    ls $C/tars/*.tar | xargs -P 48 -I{} sh -c 'tar xf {} -C /scratch/c1337/cert && rm -f {}' >> $C/log/fetch.log 2>&1 || done_ fetch "FAIL extract"
    done_ fetch "OK $(ls $C/cert/jobs | wc -l) job files, expected list $(wc -l < $C/expected_jobs.sha256) lines";;
  scan)
    python3 -I $KIT/scan.py $C/cert $C/expected_jobs.sha256 $C/scan $NJ > $C/log/scan.log 2>&1 || done_ scan "FAIL $(tail -c 300 $C/log/scan.log)"
    done_ scan "OK $(tail -1 $C/log/scan.log)";;
  ufill)
    U=$C/ucert; F=$C/filled; rm -rf $U && mkdir -p $U/jobs $F $C/u_orig
    cp $C/cert/meta.json $U/
    cut -f1 $C/scan/ujobs.txt | while read f; do ln -s $C/cert/jobs/$f $U/jobs/$f; done
    nu=$(ls $U/jobs | wc -l)
    if [ "$nu" -gt 0 ]; then
      VT_DUMP_DIR=$F python3 -I /scratch/c36/verify_tree_dump_34da7947.py $U --workers $(( nu < NJ ? nu : NJ )) --summary $C/ufill_summary.jsonl \
        > $C/log/ufill.log 2>&1 || done_ ufill "FAIL verifier rc $? (log/ufill.log)"
      for f in $(ls $U/jobs); do
        [ -s $F/$f ] || done_ ufill "FAIL no filled file $f"
        zcat $F/$f | grep -q '^\["[UT]"' && done_ ufill "FAIL tree-only record left in $f"
      done
      for f in $(ls $U/jobs); do mv $C/cert/jobs/$f $C/u_orig/$f && cp $F/$f $C/cert/jobs/$f; done
      (cd $C/cert/jobs && sha256sum $(ls $U/jobs) > $C/filled_replaced.sha256)
    fi
    done_ ufill "OK $nu jobs filled";;
  export)
    cd $P && python3 -I tools/export_shard_v2.py $C/cert C1337 --workers $NJ --pack --group-check --fast --group-leaves 1000 --main \
      > $C/log/export.log 2>&1 || done_ export "FAIL $(tail -c 300 $C/log/export.log)"
    done_ export "OK $(tail -1 $C/log/export.log)";;
  jobmap)
    python3 -I $KIT/jobmap.py $P/Autocorr/C1337 $C/jobmap.tsv $C/expected_jobs.sha256 $C/filled_replaced.sha256 \
      > $C/log/jobmap.log 2>&1 || done_ jobmap "FAIL $(tail -c 300 $C/log/jobmap.log)"
    done_ jobmap "OK $(tail -1 $C/log/jobmap.log)";;
  forms)
    cd $P && python3 -I tools/forms.py C1337 39 1337 1000 > $C/log/forms.log 2>&1 || done_ forms "FAIL forms.py"
    cmp -s Autocorr/C1337/Forms.lean $KIT/C1337_Forms.lean || done_ forms "FAIL Forms.lean differs from the reviewed proposal"
    python3 -I $KIT/check_bound.py Autocorr/C1337/Main.lean Autocorr/C1337/Forms.lean $KIT/C1337_bound_expected.lean \
      > $C/log/check_bound.log 2>&1 || done_ forms "FAIL Main/Forms bound differs from the reviewed proposal (log/check_bound.log)"
    done_ forms "OK statements equal the reviewed proposal";;
  build)
    cd $P && python3 -I tools/build_dag.py $P C1337 --jobs $NJ --lean-path $LP --mem-gb 100000 --main-mem-gb 100000 \
      --min-avail-gb 150 --kill-avail-gb 50 --main Autocorr.C1337.Main --log $C/log/build.jsonl --rm-src $DYN \
      > $C/log/build.log 2>&1 || done_ build "FAIL $(tail -c 300 $C/log/build.log)"
    done_ build "OK $(grep '^built' $C/log/build.log | tail -1)";;
  axioms)
    cd $C && printf 'import Autocorr.C1337.Forms\n#print axioms Autocorr.C1337.autocorr_lower\n#print axioms Autocorr.C1337.autocorr_lower_ess\n#print axioms Autocorr.C1337.autocorr_lower_real\n' > ax.lean
    LEAN_PATH=$LP lean ax.lean > $C/log/axioms_raw.txt 2>&1 || done_ axioms "FAIL #print axioms"
    python3 -I $KIT/axsum.py $C/log/axioms_raw.txt > $C/axioms_summary.txt || done_ axioms "FAIL axiom summary"
    S2=$C/nscan; rm -rf $S2 && mkdir -p $S2
    find $D/Autocorr/C1337 -name '*.olean' | sort > $S2/all.txt
    split -n l/64 -d -a 2 $S2/all.txt $S2/part_
    for f in $S2/part_??; do (LEAN_PATH=$T/lib/lean lean --run $P/tools/nscan_xf.lean $f $f.out Autocorr.C1337. > $f.log 2>&1; echo "rc=$?" >> $f.log) & done; wait
    v=$(grep -h "^modules" $S2/part_*.out | awk '{v+=$6} END {print v+0}'); m=$(grep -h "^modules" $S2/part_*.out | awk '{m+=$2} END {print m+0}')
    [ "$(grep -h 'rc=0' $S2/part_*.log | wc -l)" = 64 ] || done_ axioms "FAIL nscan_xf runs"
    for f in $S2/part_*.out; do sed -n '/^external/,$p' $f | tail -n +2; done | sort -u > $S2/external.txt
    KSCAN_EXT=$S2/external.txt LEAN_PATH=$LP lean $P/tools/nscan_ext_xf.lean > $S2/ext.txt 2>&1
    grep -q "missing 0" $S2/ext.txt && grep -q "axioms of the external references: \[" $S2/ext.txt || done_ axioms "FAIL nscan_ext_xf"
    [ "$v" = 0 ] || done_ axioms "FAIL nscan_xf violations $v"
    done_ axioms "OK $(head -1 $C/axioms_summary.txt); nscan_xf modules $m violations 0; $(tail -1 $S2/ext.txt)";;
  results)
    cd $C && mkdir -p out && cp axioms_summary.txt log/axioms_raw.txt scan/scan.json out/ && cp $P/Autocorr/C1337/Main.lean $P/Autocorr/C1337/Forms.lean out/ 2>/dev/null
    gzip -c scan/inputs.sha256 > out/inputs.sha256.gz; [ -f filled_replaced.sha256 ] && cp filled_replaced.sha256 out/
    gzip -c jobmap.tsv > out/jobmap.tsv.gz
    (cd $D && find Autocorr/C1337 -name '*.olean' | sort | xargs -P 64 -n 2000 sha256sum | sort -k2) | gzip -c > out/c1337_oleans.sha256.gz
    tar czf out/logs.tgz log state nscan/*.out nscan/ext.txt 2>/dev/null
    cat state/*.done > out/stages.txt; df -h /scratch > out/disk.txt
    gcloud storage cp -r out/* $R/ > $C/log/results_upload.log 2>&1 || done_ results "FAIL upload"
    done_ results "OK uploaded to $R";;
  esac
done
echo "=== drive end $(date -u +%FT%TZ)"
