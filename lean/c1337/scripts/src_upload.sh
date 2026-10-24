#!/bin/bash
# src_upload.sh (v1; never edit in place): copies the kept C1337 sources (/scratch/c1337/src_keep/C1337, hard links made by
# keep_src2 right after the export) to $RESULTS_URL/keep/src/ as one tar per top-level entry
# (G?? directories, Zo/Main/Forms), 4 at a time, nice 19 / idle I/O, with a sha256 per tar (SHA256SUMS), so that the audit's
# source copies survive the VM even if keep_src2's 500 GB disk floor drops the links. Read-only on the sources.
# Log /scratch/c1337/log/src_upload.log; last line "UPLOAD OK ..." or "UPLOAD FAIL ...".
set -u
K=/scratch/c1337/src_keep/C1337; R=${RESULTS_URL:?set RESULTS_URL to the results location}/keep/src; L=/scratch/c1337/log/src_upload.log; S=/scratch/c1337/src_upload
[ -d $K ] || { echo "UPLOAD FAIL no $K" >> $L; exit 1; }
mkdir -p $S && cd $K && ls | sort > $S/entries.txt
echo "$(date -u +%FT%TZ) start: $(wc -l < $S/entries.txt) entries" >> $L
export R S
xargs -P 4 -I{} nice -n 19 ionice -c3 bash -c 'set -o pipefail; tar -cf - {} | tee >(sha256sum | cut -c1-64 > $S/{}.sha) | gcloud storage cp - $R/{}.tar > /dev/null 2>> $S/err.txt && echo {} >> $S/done.txt || echo {} >> $S/fail.txt' < $S/entries.txt
sleep 2
[ -s $S/fail.txt ] && { echo "$(date -u +%FT%TZ) UPLOAD FAIL $(wc -l < $S/fail.txt) entries ($S/fail.txt)" >> $L; exit 1; }
for e in $(cat $S/entries.txt); do echo "$(cat $S/$e.sha)  $e.tar"; done > $S/SHA256SUMS
gcloud storage cp $S/SHA256SUMS $R/SHA256SUMS > /dev/null 2>> $S/err.txt || { echo "$(date -u +%FT%TZ) UPLOAD FAIL sums" >> $L; exit 1; }
echo "$(date -u +%FT%TZ) UPLOAD OK $(wc -l < $S/done.txt) tars to $R/ (SHA256SUMS $(sha256sum < $S/SHA256SUMS | cut -c1-16))" >> $L
