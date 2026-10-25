#!/usr/bin/env python3
"""tailfix_job_files.py X META JOB D (K1337 tailfix merge helper, nothing trusted): from the extracted
bundle X (build/KC1337/C<xx>/J<jid>[_p<k>].olean + .time) and its meta lines META, writes for JOB into D: meta.jsonl (the
job's line, exactly one required), files.txt (the job's olean paths relative to the build root, from the line's m list),
sha256 (node chunk format "<sha>  KC1337/...olean", computed here) and times (node format "KC1337/....time wall user sys
maxrss"). Fails if a module of m has no olean or no .time in X/build, or if X/build holds another olean of the job."""
import json, os, sys, glob, hashlib
X, meta, job, D = sys.argv[1:5]
ls = [json.loads(l) for l in open(meta) if l.strip()]
tl = [r for r in ls if r["j"] == job]
if len(tl) != 1:
    print(f"FAIL {job}: {len(tl)} meta lines"); sys.exit(1)
tl = tl[0]
os.makedirs(D, exist_ok=True)
files = [m.replace(".", "/") + ".olean" for m in tl["m"]]
jd = os.path.dirname(os.path.join(X, "build", files[0]))
extra = sorted(set(os.path.relpath(p, os.path.join(X, "build")) for p in glob.glob(os.path.join(jd, f"J{job}*.olean"))) - set(files))
if extra:
    print(f"FAIL {job}: bundle has oleans outside m: {extra}"); sys.exit(1)
sha, tim = [], []
for f in files:
    p = os.path.join(X, "build", f)
    t = p[:-6] + ".time"
    if not os.path.isfile(p) or not os.path.isfile(t):
        print(f"FAIL {job}: missing {f} or its .time"); sys.exit(1)
    h = hashlib.sha256(open(p, "rb").read()).hexdigest()
    sha.append(f"{h}  {f}\n"); tim.append(f"{f[:-6]}.time {open(t).read().strip()}\n")
open(os.path.join(D, "meta.jsonl"), "w").write(json.dumps(tl) + "\n")
open(os.path.join(D, "files.txt"), "w").write("".join(f + "\n" for f in files))
open(os.path.join(D, "sha256"), "w").write("".join(sha))
open(os.path.join(D, "times"), "w").write("".join(tim))
print(f"OK {job}: {len(files)} modules, {len(tl['s'])} segments")
