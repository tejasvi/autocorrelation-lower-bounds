#!/usr/bin/env python3
"""tailfix_check.py DIR JOB BUILD (K1337 tailfix merge check, run by k39asmnode4.sh tailfix; nothing trusted).
DIR holds, for one tail chunk: the fleet's partial chunk lists (chunk_<c>.meta.jsonl, .mods, .excluded.txt,
.excluded_meta.jsonl, .sha256) and the tailfix rebuild of JOB (meta.jsonl, sha256). Checks that the merged chunk takes JOB
from the tailfix rebuild only and everything else from the fleet only:
  - the fleet line of JOB is in excluded_meta, exactly once, and in no partial meta line;
  - the tailfix line of JOB (exactly one) has the fleet line's j, r and l, and the same multiset of delegated hashes;
  - the tailfix line's module list m equals the modules of the tailfix sha256 list;
  - the partial modules equal the union of the partial meta lines' m, equal the partial sha256 list, and miss every tailfix
    module and every excluded fleet module;
  - in BUILD the olean files of JOB's directory whose name starts with J<JOB> are exactly the tailfix modules.
Writes DIR/job_meta.jsonl (the tailfix line) and prints one OK line; exits 1 with the first failed check otherwise."""
import json, os, sys, glob
d, job, build = sys.argv[1], sys.argv[2], sys.argv[3]
def fail(m):
    print("FAIL", m); sys.exit(1)
def lines(fn):
    return [json.loads(l) for l in open(fn) if l.strip()]
def modset_of_sha(fn):
    out = []
    for l in open(fn):
        p = l.split()
        if len(p) != 2 or not p[1].endswith(".olean"):
            fail(f"bad sha256 line in {fn}: {l[:80]}")
        out.append(p[1][:-6].replace("/", "."))
    return out
c = [f for f in os.listdir(d) if f.endswith(".excluded_meta.jsonl")]
if len(c) != 1:
    fail("expected one *.excluded_meta.jsonl")
pre = os.path.join(d, c[0][:-len(".excluded_meta.jsonl")])
xm = [r for r in lines(pre + ".excluded_meta.jsonl") if r["j"] == job]
if len(xm) != 1:
    fail(f"fleet line of {job} in excluded_meta: {len(xm)} times")
fl = xm[0]
pm = lines(pre + ".meta.jsonl")
if any(r["j"] == job for r in pm):
    fail("job still in the partial meta")
tl = [r for r in lines(os.path.join(d, "meta.jsonl")) if r["j"] == job]
if len(tl) != 1:
    fail(f"tailfix line of {job}: {len(tl)} times")
tl = tl[0]
for k in ("j", "r", "l"):
    if tl[k] != fl[k]:
        fail(f"{k} differs: tailfix {tl[k]} fleet {fl[k]}")
flat = lambda r: sorted(h for seg in r["s"] for h in seg)
if flat(tl) != flat(fl):
    fail("delegated hash multiset differs")
tmods = modset_of_sha(os.path.join(d, "sha256"))
if sorted(tmods) != sorted(tl["m"]) or len(set(tmods)) != len(tmods):
    fail("tailfix m != tailfix sha256 modules")
pmods = [l.strip() for l in open(pre + ".mods") if l.strip()]
um = sorted(m for r in pm for m in r["m"])
if sorted(pmods) != um:
    fail("partial mods != union of partial meta m")
if sorted(modset_of_sha(pre + ".sha256")) != sorted(pmods):
    fail("partial sha256 modules != partial mods")
xmods = [l.strip() for l in open(pre + ".excluded.txt") if l.strip()]
if sorted(xmods) != sorted(fl["m"]):
    fail("excluded list != fleet line m")
sp = set(pmods)
if sp & set(tmods) or sp & set(xmods):
    fail("partial chunk contains a module of the job")
jd = os.path.dirname(os.path.join(build, tl["m"][0].replace(".", "/")))
have = sorted(os.path.basename(p)[:-6] for p in glob.glob(os.path.join(jd, f"J{job}*.olean")))
want = sorted(m.split(".")[-1] for m in tmods)
if have != want:
    fail(f"build has {have} for the job, tailfix provides {want}")
open(os.path.join(d, "job_meta.jsonl"), "w").write(json.dumps(tl) + "\n")
print(f"OK {job}: fleet {len(fl['m'])} modules / {len(fl['s'])} segments -> tailfix {len(tmods)} modules / {len(tl['s'])} "
      f"segments; r {tl['r']} l {tl['l']}; {len(flat(tl))} delegated hashes equal; partial chunk {len(pmods)} modules")
