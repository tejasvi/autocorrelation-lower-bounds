#!/usr/bin/env python3
"""hedge_check.py DIR JOB V1BUILD V2BUILD BUNDLE (K1337 v2-hedge merge check, nothing trusted). DIR holds the
fleet's partial chunk lists of JOB's chunk (chunk_<c>.meta.jsonl, .mods, .excluded.txt, .excluded_meta.jsonl, .sha256); BUNDLE
is the v2 re-export bundle (k39/hedge_v2/) (meta_jobs3_orig.jsonl, hedge_job_oleans.sha256). Checks, one source per job:
  - the fleet line of JOB is in excluded_meta exactly once and in no partial meta line, and equals the bundle's original
    line for JOB (same j, r, s, l, m: the v2 job keeps the fleet segmentation);
  - the v2 modules of JOB in the bundle's olean list are exactly m with KC1337. -> KC1337v2., and they exist in V2BUILD;
  - V1BUILD has no olean of JOB at all (no v1 version can enter the assembly);
  - the partial modules equal the union of the partial meta lines' m and the partial sha256 list, and miss JOB's modules.
Writes DIR/job_meta.jsonl (the fleet line) and DIR/job_v2.sha256 (JOB's lines of the bundle olean list); prints one OK line."""
import json, os, sys, glob
d, job, v1b, v2b, B = sys.argv[1:6]
def fail(m):
    print("FAIL", m); sys.exit(1)
lines = lambda fn: [json.loads(l) for l in open(fn) if l.strip()]
pre = [f for f in os.listdir(d) if f.endswith(".excluded_meta.jsonl")]
if len(pre) != 1:
    fail("expected one *.excluded_meta.jsonl")
pre = os.path.join(d, pre[0][:-len(".excluded_meta.jsonl")])
fl = [r for r in lines(pre + ".excluded_meta.jsonl") if r["j"] == job]
if len(fl) != 1:
    fail(f"fleet line of {job} in excluded_meta: {len(fl)} times")
fl = fl[0]
pm = lines(pre + ".meta.jsonl")
if any(r["j"] == job for r in pm):
    fail("job still in the partial meta")
bl = [r for r in lines(os.path.join(B, "meta_jobs3_orig.jsonl")) if r["j"] == job]
if len(bl) != 1:
    fail(f"bundle meta line of {job}: {len(bl)}")
for k in ("j", "r", "s", "l", "m"):
    if bl[0][k] != fl[k]:
        fail(f"bundle original line differs from the fleet line in {k}")
want = sorted("KC1337v2." + m[len("KC1337."):] for m in fl["m"])
jl = [l for l in open(os.path.join(B, "hedge_job_oleans.sha256")) if f"/J{job}" in l.split()[1]]
have = sorted(l.split()[1][:-6].replace("/", ".") for l in jl)
if have != want:
    fail(f"bundle v2 modules {have} != mapped m {want}")
for l in jl:
    if not os.path.isfile(os.path.join(v2b, l.split()[1])):
        fail(f"missing in v2build: {l.split()[1]}")
jd = os.path.dirname(os.path.join(v1b, fl["m"][0].replace(".", "/")))
v1 = glob.glob(os.path.join(jd, f"J{job}*.olean"))
if v1:
    fail(f"v1 olean(s) of the job in the v1 build tree: {[os.path.basename(p) for p in v1]}")
pmods = [l.strip() for l in open(pre + ".mods") if l.strip()]
if sorted(pmods) != sorted(m for r in pm for m in r["m"]):
    fail("partial mods != union of partial meta m")
if sorted(l.split()[1][:-6].replace("/", ".") for l in open(pre + ".sha256")) != sorted(pmods):
    fail("partial sha256 modules != partial mods")
if set(pmods) & set(fl["m"]):
    fail("partial chunk contains a module of the job")
open(os.path.join(d, "job_meta.jsonl"), "w").write(json.dumps(fl) + "\n")
open(os.path.join(d, "job_v2.sha256"), "w").write("".join(jl))
print(f"OK {job}: fleet line == bundle original line (r {fl['r']}, l {fl['l']}, {len(fl['s'])} segments); v2 modules {len(have)}; "
      f"no v1 olean; partial chunk {len(pmods)} modules")
