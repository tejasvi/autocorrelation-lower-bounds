#!/bin/bash
# keep_src2.sh (keep_src.sh v1 + a disk guard; never edit in place): keeps the C1337 sources for the independent audit.
# drive3.sh's build stage deletes each module's source once it is built (build_dag --rm-src: every module but Main, so
# Forms.lean too). Runs next to the driver, outside it, and never writes into the project:
#   1. right after the export stage (jobmap and forms run before the build), hard-links the generated source tree into
#      /scratch/c1337/src_keep/C1337 (same filesystem: no data copied; the build's deletions then free nothing);
#   2. after the forms stage, replaces Main.lean and Forms.lean there by real copies (Forms.lean diffed with the kit copy);
#   3. sha256 of every kept source (nice 19, idle I/O, in chunks) -> c1337_sources.sha256.gz; uploads it, Main.lean,
#      Forms.lean and this log to $RESULTS_URL/keep/;
#   4. disk guard until build.done is OK: below 500 GB free on /scratch it removes the kept links, so the build's own
#      deletions free space as planned ("KEEP DROPPED"); the sources can then be regenerated from the kept inputs
#      (export_shard, same flags) and checked against c1337_sources.sha256.gz.
# Log /scratch/c1337/log/keep_src.log: "KEEP OK" after step 3, then "KEEP END", "KEEP DROPPED" or "KEEP FAIL".
set -u
C=/scratch/c1337; SRC=/scratch/c36/lean_c133_prod/Autocorr/C1337; K=/scratch/c1337/src_keep; KIT=/scratch/c36/kit
R=${RESULTS_URL:?set RESULTS_URL to the results location}/keep; L=$C/log/keep_src.log; END=$(( $(date +%s) + 72000 ))
MINFREE=${KEEP_MINFREE:-500}
export LC_ALL=C
log() { echo "$(date -u +%FT%TZ) $*" >> $L; }
fail() { log "KEEP FAIL $*"; exit 1; }
st() { head -c 2 $C/state/$1.done 2>/dev/null; }
freeg() { df -BG --output=avail /scratch | tail -1 | tr -dc 0-9; }
drop() {
  log "KEEP DROPPED: /scratch free $1G < ${MINFREE}G; removing the kept links so the build's deletions free space"
  rm -rf --one-file-system -- /scratch/c1337/src_keep/C1337
  log "KEEP DROPPED removed; /scratch free $(freeg)G"
  gcloud storage cp $L $R/ >> $C/log/keep_upload.log 2>&1
  exit 2
}
chk() { local f; f=$(freeg); [ "$f" -lt "$MINFREE" ] && drop $f; return 0; }
log "keep_src2 start (pid $$), waiting for export.done; /scratch free $(freeg)G"
while [ "$(st export)" != OK ]; do
  [ "$(st export)" = FA ] && fail "export stage failed; nothing kept"
  [ "$(date +%s)" -lt $END ] || fail "20 h without export.done"
  sleep 2
done
pre=no; [ -e $C/log/build.jsonl ] && pre=yes
[ -d $SRC ] || fail "no $SRC"
[ -e $K/C1337 ] && fail "$K/C1337 exists already"
mkdir -p $K && cp -al $SRC $K/C1337 || fail "cp -al"
n0=$(find $SRC -name '*.lean' | wc -l); n1=$(find $K/C1337 -name '*.lean' | wc -l)
ng=$(find $K/C1337 -path "$K/C1337/G*/G*.lean" | wc -l); nb=0; [ -e $C/log/build.jsonl ] && nb=$(grep -c . $C/log/build.jsonl)
log "linked: kept $n1 .lean ($ng group modules), project now $n0; build log before the link: $pre, lines now: $nb; source bytes $(du -s -B1G --apparent-size $K/C1337 | cut -f1)G; /scratch free $(freeg)G"
log "export: $(cat $C/state/export.done)"
[ "$pre" = no ] && [ "$nb" = 0 ] && [ "$n1" = "$n0" ] || fail "the build may have deleted sources before the link"
while [ "$(st forms)" != OK ]; do
  [ "$(st jobmap)" = FA ] && fail "jobmap stage failed (group sources kept; Main/Forms not copied)"
  [ "$(st forms)" = FA ] && fail "forms stage failed (group sources kept; Main/Forms not copied)"
  [ "$(date +%s)" -lt $END ] || fail "20 h without forms.done"
  sleep 5
done
for f in Main.lean Forms.lean; do cp -p --remove-destination $SRC/$f $K/C1337/$f || fail "copy $f"; done
cmp -s $K/C1337/Forms.lean $KIT/C1337_Forms.lean || fail "kept Forms.lean differs from the reviewed proposal"
log "Main.lean $(sha256sum < $K/C1337/Main.lean | cut -c1-16), Forms.lean $(sha256sum < $K/C1337/Forms.lean | cut -c1-16) (= kit copy)"
(cd $K && find C1337 -name '*.lean' | sort) > $C/keep_list.txt || fail "file list"
n2=$(wc -l < $C/keep_list.txt); : > $C/c1337_sources.sha256
for ((i = 1; i <= n2; i += 2000)); do
  chk
  sed -n "${i},$((i + 1999))p" $C/keep_list.txt | (cd $K && nice -n 19 ionice -c3 xargs -r -P 8 -n 250 sha256sum) \
    >> $C/c1337_sources.sha256 || fail "sha256 of list lines $i.."
done
sort -k2 $C/c1337_sources.sha256 | gzip -c > $C/c1337_sources.sha256.gz || fail "sha256 list"
ns=$(zcat $C/c1337_sources.sha256.gz | wc -l); [ "$ns" = "$n2" ] || fail "sha256 list has $ns lines, kept $n2"
gcloud storage cp $C/c1337_sources.sha256.gz $K/C1337/Main.lean $K/C1337/Forms.lean $R/ > $C/log/keep_upload.log 2>&1 \
  || fail "upload (log/keep_upload.log)"
log "KEEP OK $n2 sources kept in $K/C1337 ($ng group modules + Zo/Main/Forms), list c1337_sources.sha256.gz $(sha256sum < $C/c1337_sources.sha256.gz | cut -c1-16), uploaded to $R/; disk guard on (min ${MINFREE}G)"
gcloud storage cp $L $R/ >> $C/log/keep_upload.log 2>&1
until [ "$(st build)" = OK ]; do
  chk
  [ "$(date +%s)" -lt $END ] || { log "KEEP END 20 h deadline before build.done OK; guard off, sources kept; free $(freeg)G"; exit 0; }
  sleep 30
done
log "KEEP END build OK; sources kept in $K/C1337; /scratch free $(freeg)G"
gcloud storage cp $L $R/ >> $C/log/keep_upload.log 2>&1
