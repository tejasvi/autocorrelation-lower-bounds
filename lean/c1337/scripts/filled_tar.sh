#!/bin/bash
# filled_tar.sh (v1; never edit in place): packs the 2,412 filled job files for the record. Outside the driver;
# read-only on the inputs (writes only /scratch/c1337/filled_upload). Uploads to $RESULTS_URL/filled/:
#   c1337_filled_jobs.tar     the 2,412 U-filled job files exactly as the Lean proof reads them (/scratch/c1337/cert/jobs/NAME),
#                             members jobs/NAME.jsonl.gz as in the certificate's D-log tars (extract over them to rebuild the input)
#   c1337_filled_jobs.sha256  their sha256 in sha256sum format, "sha256  jobs/NAME.jsonl.gz" (sha256sum -c after extracting)
#   c1337_filled_certificate.sha256.gz  every Lean input file (5,033,964: the certificate's job files with the 2,412 filled
#                             copies in place), "sha256 size NAME.jsonl.gz" sorted by name, the format of c39t's list;
#                             built from the scan stage's hashes with the 2,412 filled entries replaced
#   SHA256SUMS                sha256 of the three files
# Checks: the list equals filled_replaced.sha256 and the verifier outputs in filled/; the tar's members and bytes match the list;
# the uploaded tar's sha256 equals the local one. Last line "FILLED OK ..." or "FAIL ...".
set -u
export LC_ALL=C
C=/scratch/c1337; R=${RESULTS_URL:?set RESULTS_URL to the results location}/filled; O=/scratch/c1337/filled_upload; T=c1337_filled_jobs
F=c1337_filled_certificate.sha256
fail() { echo "FAIL $*"; exit 1; }
[ -e $O ] && fail "$O exists (an earlier run)"
mkdir -p $O
awk '{print "jobs/" $2}' $C/filled_replaced.sha256 | sort > $O/names.txt
n=$(wc -l < $O/names.txt); [ "$n" = 2412 ] || fail "$n names in filled_replaced.sha256"
(cd $C/cert && xargs -a $O/names.txt sha256sum) > $O/$T.sha256 || fail "sha256 of cert/jobs"
cmp -s <(sed 's#  #  jobs/#' $C/filled_replaced.sha256 | sort -k2) $O/$T.sha256 || fail "cert/jobs copies differ from filled_replaced.sha256"
(cd $C/filled && sed 's#  jobs/#  #' $O/$T.sha256 | sha256sum -c --quiet) || fail "verifier outputs in filled/ differ from cert/jobs"
tar -C $C/cert --sort=name --format=gnu --owner=0 --group=0 --numeric-owner -cf $O/$T.tar -T $O/names.txt || fail "tar"
tar -tf $O/$T.tar | cmp -s - $O/names.txt || fail "tar member list"
mkdir $O/x && tar -C $O/x -xf $O/$T.tar && (cd $O/x && sha256sum -c --quiet $O/$T.sha256) || fail "tar content"
rm -rf --one-file-system -- /scratch/c1337/filled_upload/x
while read -r sha p; do echo "$sha $(stat -c %s $C/cert/$p) ${p#jobs/}"; done < $O/$T.sha256 > $O/repl.txt
python3 -I - $C/scan/inputs.sha256 $O/repl.txt $O/$F <<'EOF' || fail "full list"
import sys
inp, repl, out = sys.argv[1:4]
r = {}
for line in open(repl):
    sha, size, name = line.split()
    r[name] = (sha, size)
rows = []; hit = 0
for line in open(inp):
    sha, size, name = line.split()
    if name in r:
        sha, size = r[name]; hit += 1
    rows.append((name, sha, size))
rows.sort()
if len(rows) != 5033964 or hit != len(r) or len({x[0] for x in rows}) != len(rows):
    sys.exit(f"rows {len(rows)} replaced {hit} of {len(r)}")
with open(out, "w") as fh:
    fh.writelines(f"{sha} {size} {name}\n" for name, sha, size in rows)
EOF
gzip -n -9 $O/$F || fail "gzip"
for x in $T.tar $T.sha256 $F.gz; do echo "$(sha256sum < $O/$x | cut -c1-64)  $x"; done > $O/SHA256SUMS
gcloud storage cp $O/$T.tar $O/$T.sha256 $O/$F.gz $O/SHA256SUMS $R/ > $C/log/filled_upload.log 2>&1 || fail "upload (log/filled_upload.log)"
tsha=$(head -1 $O/SHA256SUMS | cut -c1-64); rsha=$(gcloud storage cat $R/$T.tar | sha256sum | cut -c1-64)
[ "$rsha" = "$tsha" ] || fail "uploaded tar sha256 $rsha"
echo "FILLED OK $n files; uploaded to $R/ (tar read back equal):"
for x in $T.tar $T.sha256 $F.gz SHA256SUMS; do echo "  $x $(stat -c %s $O/$x) bytes sha256 $(sha256sum < $O/$x | cut -c1-64)"; done
