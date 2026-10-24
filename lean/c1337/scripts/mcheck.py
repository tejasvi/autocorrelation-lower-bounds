#!/usr/bin/env python3
"""mcheck.py INPUTS_SHA256_GZ MANIFEST_DIR: read-only check of the fetched job files against the certificate's per-VM
manifests. INPUTS_SHA256_GZ is the scan stage's list ("sha256 size name" for every fetched job file, hashed before the U
fill); MANIFEST_DIR holds the jobs_<vm>.sha256 files ("sha256  name") from summaries/<vm>/ of the certificate bucket.
Joins on the job id (the file name) and prints one line: manifests, compared, equal, differ, missing (in a manifest, not
fetched), extra (fetched, in no manifest), duplicate ids (across manifests). Exit 0 only if at least one manifest was
read and differ, missing, extra and duplicate ids are all 0."""
import gzip, os, sys

inp, mdir = sys.argv[1:3]
key = lambda name: os.path.basename(name.lstrip("*"))
got = {}
with gzip.open(inp, "rt") as fh:
    for line in fh:
        p = line.split()
        if p:
            got[key(p[-1])] = p[0]
man = {}; dup = 0; nman = 0
for fn in sorted(os.listdir(mdir)):
    if not (fn.startswith("jobs_") and fn.endswith(".sha256")):
        continue
    nman += 1
    with open(os.path.join(mdir, fn)) as fh:
        for line in fh:
            p = line.split()
            if not p:
                continue
            k = key(p[-1])
            if k in man:
                dup += 1
            man[k] = p[0]
both = [k for k in man if k in got]
equal = sum(1 for k in both if man[k] == got[k])
differ = len(both) - equal
missing = len(man) - len(both)
extra = sum(1 for k in got if k not in man)
print(f"manifests {nman}, compared {len(both)}, equal {equal}, differ {differ}, missing {missing}, extra {extra}, "
      f"duplicate ids {dup}")
sys.exit(0 if nman and not (differ or missing or extra or dup) else 1)
