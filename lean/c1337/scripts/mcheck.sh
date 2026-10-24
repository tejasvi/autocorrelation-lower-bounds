#!/bin/bash
# mcheck.sh (v1; never edit in place): read-only check asked by main, run after the results stage and outside the driver:
# out/inputs.sha256.gz (every fetched job file, hashed by the scan stage before the U fill) against the per-VM manifests
# $CERT_URL/summaries/<vm>/jobs_<vm>.sha256, joined on job id (kit/mcheck.py). Writes one line to
# /scratch/c1337/out/manifest_check.txt, uploads it to the results folder and prints it. Changes nothing else.
set -u
C=/scratch/c1337; B=${CERT_URL:?set CERT_URL to the certificate location}; R=${RESULTS_URL:?set RESULTS_URL to the results location}; M=$C/mcheck
[ -s $C/out/inputs.sha256.gz ] || { echo "FAIL no $C/out/inputs.sha256.gz (results stage not done)"; exit 1; }
[ -e $M ] && { echo "FAIL $M exists (an earlier run): read $C/out/manifest_check.txt"; exit 1; }
mkdir -p $M
gcloud storage cp "$B/summaries/*/jobs_*.sha256" $M/ > $C/log/mcheck.log 2>&1 || { echo "FAIL manifest download (log/mcheck.log)"; exit 1; }
out=$(python3 -I /scratch/c36/kit/mcheck.py $C/out/inputs.sha256.gz $M 2>> $C/log/mcheck.log); rc=$?
line="$(date -u +%FT%TZ) MANIFEST CHECK (rc $rc): ${out:-no output, see log/mcheck.log}"
echo "$line" > $C/out/manifest_check.txt
gcloud storage cp $C/out/manifest_check.txt $R/manifest_check.txt >> $C/log/mcheck.log 2>&1 || line="$line [UPLOAD FAILED]"
echo "$line"
exit $rc
