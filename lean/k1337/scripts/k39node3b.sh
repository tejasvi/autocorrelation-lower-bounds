#!/bin/bash
# k39node3b.sh SET "TAR1 TAR2 ..." (v3b = v3 whose uploader reports a failed chunk at once and keeps shipping the other chunks; v3 = v2 with pipelined chunks; never edit in place): one K1337 fleet VM (kernel-only
# C1 >= 1337/1000, checker K39). Stages setup/fetch/export/params, state files, bucket layout and every per-chunk output
# are exactly v2's (k39node.sh v2); only the chunks stage is scheduled differently:
#   chunks  the same 10 chunks of the sorted job list (chunk_<c>.meta.jsonl / .mods: v2's files are reused if present,
#           else written by v2's code). ONE build queue over all chunks not DONE in the bucket (chunk order; inside a chunk
#           the largest estimated jobs first), NJ in parallel, so the next chunk's modules start while a slow module of an
#           earlier chunk still runs. Modules with "rc=0" from an earlier run on this VM (chunk_<c>.rc of v2, all.rc of v3)
#           whose .olean and .time exist are not rebuilt. A background uploader ships each chunk once all its modules have
#           rc=0, with v2's commands (chunk_<c>.tar, .sha256, .meta.jsonl, .times, .DONE; DONE time = s since the v3 chunks
#           stage started). Any module rc != 0, or a module without a result after the queue ends -> that chunk is not
#           shipped and state/chunks.done says FAIL at once (bucket too); the other chunks still ship; the stage ends FAIL.
# Also disables Ubuntu's MOTD release check (check-new-release spins without internet when ssh logins start it).
# K39_MAXJOBS (test only) limits the job list.  Final marker: s<SET>/DONE.
set -u
SET=$1; TARS=$2; PART=${K39_PART:-0/1}; PI=${PART%/*}; PN=${PART#*/}
SID=s$SET; [ "$PN" -gt 1 ] && SID=s${SET}_${PI}of${PN}
W=/k39; B=${CERT_URL}; R=${RESULTS_URL}/k39/fleet/$SID; K=${RESULTS_URL}/k39
TC=$W/tc; NJ=$(( $(getconf _NPROCESSORS_ONLN) - 4 ))
export LEAN_PATH=$W/out/build:$W/lib:$TC/lib/lean LEAN_NUM_THREADS=1 OMP_NUM_THREADS=1 AUTOCORR_CHECKER=$W/tools TC
mkdir -p $W/state $W/log $W/cert
ulimit -n $(ulimit -Hn)
ok() { grep -q "^OK" $W/state/$1.done 2>/dev/null; }
done_() { echo "$2" > $W/state/$1.done; echo "=== $1 $(date -u +%FT%TZ) $2"; gcloud storage cp $W/state/$1.done $R/state/$1.done > /dev/null 2>&1; case "$2" in OK*) ;; *) exit 1;; esac; }
lb() { o=build/$(echo $1 | tr . /); mkdir -p $(dirname $o); /usr/bin/time -f "%e %U %S %M" -o $o.time $TC/bin/lean -DElab.async=false -o $o.olean $(echo $1 | tr . /).lean > $o.log 2>&1; echo "$1 rc=$?"; }
export -f lb
for S in setup fetch export params chunks; do
  ok $S && { echo "=== $S already OK"; continue; }
  echo "=== $S start $(date -u +%FT%TZ) avail $(awk '/MemAvailable/ {printf "%.0f GB", $2/1e6}' /proc/meminfo), disk free $(df -BG --output=avail $W | tail -1 | tr -d ' ')"
  case $S in
  setup)
    apt-get -qq update > /dev/null 2>&1; DEBIAN_FRONTEND=noninteractive apt-get -y -qq install zstd time > /dev/null 2>&1
    cd $W && gcloud storage cp $K/kit/toolchain.tar.zst $K/kit/oleans.tar $K/kit3/tools3.tar . > $W/log/setup.log 2>&1 || done_ setup "FAIL kit download"
    mkdir -p tc lib && zstd -dc toolchain.tar.zst | tar -x -C tc && tar -xf oleans.tar -C lib && tar -xf tools3.tar && rm -f toolchain.tar.zst \
      || done_ setup "FAIL kit unpack"
    done_ setup "OK $NJ workers, $($TC/bin/lean --version | head -1 | cut -c1-40)";;
  fetch)
    cd $W && : > $W/log/fetch.log
    for t in $TARS; do
      srv=$(basename $t .tar)
      gcloud storage cat $B/dlogs/$t 2>> $W/log/fetch.log | tar -x -C $W/cert || done_ fetch "FAIL tar $t"
      gcloud storage cat $B/summaries/$srv/jobs_$srv.sha256 > $W/log/man_$srv.sha256 2>> $W/log/fetch.log || done_ fetch "FAIL manifest $srv"
      (cd $W/cert/jobs && split -n l/32 -d $W/log/man_$srv.sha256 $W/log/mpart_ && ls $W/log/mpart_* | xargs -P 32 -I{} sh -c 'sha256sum -c --quiet {} || echo BAD {}' ; rm -f $W/log/mpart_*) \
        > $W/log/shacheck_$srv.txt 2>&1
      grep -q "BAD\|FAILED" $W/log/shacheck_$srv.txt && done_ fetch "FAIL sha256 $srv ($(grep -c FAILED $W/log/shacheck_$srv.txt) files)"
    done
    gcloud storage cp $B/run/meta.json $W/cert/meta.json >> $W/log/fetch.log 2>&1 && [ "$(sha256sum $W/cert/meta.json | cut -c1-8)" = 5fa65703 ] || done_ fetch "FAIL meta"
    mkdir -p $W/filled && gcloud storage cat ${RESULTS_URL}/results/filled/c1337_filled_jobs.tar 2>> $W/log/fetch.log | tar -x -C $W/filled \
      || done_ fetch "FAIL filled tar"
    gcloud storage cp ${RESULTS_URL}/results/filled/c1337_filled_jobs.sha256 $W/filled/ >> $W/log/fetch.log 2>&1 || done_ fetch "FAIL filled list"
    (cd $W/filled && sha256sum -c --quiet c1337_filled_jobs.sha256) > $W/log/filled_check.txt 2>&1 || done_ fetch "FAIL filled sha256"
    nf=0; for f in $(ls $W/filled/jobs); do [ -e $W/cert/jobs/$f ] && { cp $W/filled/jobs/$f $W/cert/jobs/$f; nf=$((nf + 1)); }; done
    rm -rf $W/filled/jobs
    done_ fetch "OK $(ls $W/cert/jobs | wc -l) job files from $(echo $TARS | wc -w) tars, sha256 checked, $nf filled copies";;
  export)
    cd $W && ls cert/jobs | sort > jobs_all.txt
    [ "$PN" -gt 1 ] && { awk -v i=$PI -v n=$PN '(NR - 1) % n == i' jobs_all.txt > j.tmp && mv j.tmp jobs_all.txt; }
    [ -n "${K39_MAXJOBS:-}" ] && { head -$K39_MAXJOBS jobs_all.txt > j.tmp && mv j.tmp jobs_all.txt; }
    python3 tools/k39export.py cert out KC1337 Autocorr.KC1337 jobs_all.txt --workers $NJ > $W/log/export.log 2>&1 \
      || done_ export "FAIL $(tail -c 300 $W/log/export.log)"
    done_ export "OK $(tail -1 $W/log/export.log)";;
  params)
    cd $W/out && r=$(lb KC1337.Params) && [ "$r" = "KC1337.Params rc=0" ] || done_ params "FAIL (out/build/KC1337/Params.log)"
    done_ params "OK $(cat build/KC1337/Params.time)";;
  chunks)
    cd $W/out
    chmod -x /etc/update-motd.d/91-release-upgrade 2>/dev/null
    if ! ls chunk_9.mods chunk_9.meta.jsonl > /dev/null 2>&1; then
      python3 -c "
import json
rows = [json.loads(l) for l in open('KC1337/meta_jobs_all.txt.jsonl')]
rows.sort(key=lambda r: r['j'])
n = len(rows)
for c in range(10):
    part = rows[c * n // 10:(c + 1) * n // 10]
    open(f'chunk_{c}.meta.jsonl', 'w').write(''.join(json.dumps(r) + '\n' for r in part))
    open(f'chunk_{c}.mods', 'w').write(''.join(m + '\n' for r in part for m in r['m']))
"
    fi
    gcloud storage cp KC1337/Params.lean $R/Params.lean > /dev/null 2>&1
    gcloud storage ls "$R/chunk_*.DONE" > done_list.txt 2>/dev/null
    touch all.rc; rm -f build_end up_fail.txt
    cat chunk_*.rc all.rc 2>/dev/null | awk '$2 == "rc=0" {print $1}' | sort -u > prev_rc0.txt
    python3 -c "
import json, os
done = open('done_list.txt').read()
prev = set(l.strip() for l in open('prev_rc0.txt') if l.strip())
queue, todo, ok = [], [], []
for c in range(10):
    if f'chunk_{c}.DONE' in done:
        continue
    todo.append(str(c))
    mods = []
    for l in open(f'chunk_{c}.meta.jsonl'):
        r = json.loads(l)
        for m in r['m']:
            mods.append((-r.get('e', 0) / len(r['m']), m))
    for _, m in sorted(mods):
        p = 'build/' + m.replace('.', '/')
        if m in prev and os.path.exists(p + '.olean') and os.path.exists(p + '.time'):
            ok.append(m)
        else:
            queue.append(m)
open('queue.txt', 'w').write(''.join(m + '\n' for m in queue))
open('prev_ok.txt', 'w').write(''.join(m + '\n' for m in ok))
open('todo_chunks.txt', 'w').write(' '.join(todo) + '\n')
print(f'v3 queue: {len(queue)} modules to build, {len(ok)} kept from an earlier run, chunks to ship: {\" \".join(todo)}')
" || done_ chunks "FAIL v3 queue"
    t0=$(date +%s)
    upchunk() {
      c=$1
      sed 's#\.#/#g; s#$#.olean#' chunk_$c.mods > chunk_$c.files
      (cd build && xargs -a ../chunk_$c.files sha256sum) > chunk_$c.sha256 || return 1
      (cd build && sed 's#\.olean$#.time#' ../chunk_$c.files | xargs -I{} sh -c 'echo "{} $(cat {})"') > chunk_$c.times
      tar -cf - -C build -T chunk_$c.files | gcloud storage cp - $R/chunk_$c.tar > /dev/null 2>> $W/log/upload.log || return 2
      gcloud storage cp chunk_$c.sha256 chunk_$c.meta.jsonl chunk_$c.times $R/ > /dev/null 2>> $W/log/upload.log || return 3
      echo "chunk $c: $(wc -l < chunk_$c.mods) modules, $(( $(date +%s) - t0 )) s" > chunk_$c.DONE
      gcloud storage cp chunk_$c.DONE $R/chunk_$c.DONE > /dev/null 2>> $W/log/upload.log || return 4
      echo "=== chunk $c $(date -u +%FT%TZ) $(cat chunk_$c.DONE) (v3b)"
    }
    failstate() {
      echo "$1" >> up_fail.txt; echo "$1" > $W/state/chunks.done
      gcloud storage cp $W/state/chunks.done $R/state/chunks.done > /dev/null 2>&1
    }
    uploader() {
      pend=$(cat todo_chunks.txt)
      while [ -n "$pend" ]; do
        fin=0; [ -f build_end ] && fin=1
        left=""
        for c in $pend; do
          read no nb n < <(awk -v F=chunk_$c.mods 'FILENAME == F {want[$1] = 1; n++; next}
            FILENAME == "prev_ok.txt" {if ($1 in want) ok[$1] = 1; next}
            ($1 in want) {if ($2 == "rc=0") ok[$1] = 1; else bad[$1] = 1}
            END {nb = 0; for (m in bad) if (!(m in ok)) nb++; no = 0; for (m in ok) no++; print no, nb, n}' chunk_$c.mods prev_ok.txt all.rc)
          if [ "$nb" -gt 0 ]; then
            failstate "FAIL chunk $c: $nb modules failed (out/all.rc)"
          elif [ "$no" = "$n" ]; then
            awk -v F=chunk_$c.mods 'FILENAME == F {want[$1] = 1; next} ($1 in want) {print $1 " rc=0"}' chunk_$c.mods prev_ok.txt > chunk_$c.rc.tmp
            awk -v F=chunk_$c.mods 'FILENAME == F {want[$1] = 1; next} ($1 in want)' chunk_$c.mods all.rc >> chunk_$c.rc.tmp
            mv chunk_$c.rc.tmp chunk_$c.rc
            upchunk $c || failstate "FAIL upload chunk $c (step $?)"
          elif [ $fin = 1 ]; then
            failstate "FAIL chunk $c: $(( n - no )) modules without a result (out/all.rc)"
          else
            left="$left $c"
          fi
        done
        pend=$(echo $left)
        [ -n "$pend" ] && sleep 20
      done
      [ -s up_fail.txt ] && return 1
      return 0
    }
    uploader > $W/log/uploader.log 2>&1 &
    upid=$!
    xargs -P $NJ -I{} bash -c 'lb {}' < queue.txt >> all.rc
    touch build_end
    wait $upid; urc=$?
    cat $W/log/uploader.log
    [ $urc = 0 ] || done_ chunks "$(head -1 up_fail.txt 2>/dev/null || echo "FAIL uploader rc $urc") ($(wc -l < up_fail.txt 2>/dev/null || echo 0) failure lines in out/up_fail.txt)"
    done_ chunks "OK 10 chunks (v3b)";;
  esac
done
echo "set $SID: $(cat $W/state/*.done | tr '\n' ';')" > $W/DONE && gcloud storage cp $W/DONE $R/DONE > /dev/null 2>&1
echo "=== node end $(date -u +%FT%TZ)"
