#!/usr/bin/env python3
"""tailfix_bundle_check.py B SUMS TAR META MAN (K1337 tailfix merge, nothing trusted): the re-export bundle,
downloaded into B and its TAR extracted into B/x. Checks: every line of SUMS ("<sha>  <file>") verifies in B and SUMS covers
TAR, META and MAN; TAR members are only KC1337/C<xx>/J<jid>[_p<k>].lean and build/KC1337/C<xx>/J<jid>[_p<k>].{olean,time};
META has one line per job (unique j); MAN has one row per META job with new_rc all rc=0, new_modules == the line's m and
new_olean_sha256 == the sha256 of B/x/build/<module>.olean; every olean in B/x/build belongs to one META line's m."""
import json, os, sys, hashlib, re, tarfile, csv, glob
B, SUMS, TAR, META, MAN = sys.argv[1:6]
def fail(m):
    print("FAIL", m); sys.exit(1)
sh = lambda p: hashlib.sha256(open(p, "rb").read()).hexdigest()
listed = {}
for l in open(os.path.join(B, SUMS)):
    p = l.split()
    if len(p) != 2:
        fail(f"bad SUMS line {l[:60]}")
    listed[p[1]] = p[0]
for f in (TAR, META, MAN):
    if f not in listed:
        fail(f"{f} not in {SUMS}")
for f, h in listed.items():
    if "/" in f or not os.path.isfile(os.path.join(B, f)) or sh(os.path.join(B, f)) != h:
        fail(f"SUMS does not verify: {f}")
pat = re.compile(r"^(KC1337/C[0-9a-f]{2}/J[0-9a-f]{32}(_p\d+)?\.lean|build/KC1337/C[0-9a-f]{2}/J[0-9a-f]{32}(_p\d+)?\.(olean|time))$")
with tarfile.open(os.path.join(B, TAR)) as t:
    names = t.getnames()
    bad = [n for n in names if not pat.match(n)] + [m.name for m in t.getmembers() if not (m.isfile())]
if bad:
    fail(f"unexpected tar members: {bad[:3]}")
ls = [json.loads(l) for l in open(os.path.join(B, META)) if l.strip()]
jobs = [r["j"] for r in ls]
if len(set(jobs)) != len(jobs):
    fail("job twice in META")
rows = list(csv.DictReader(open(os.path.join(B, MAN)), delimiter="\t"))
byj = {r["job"]: r for r in rows}
if sorted(byj) != sorted(jobs) or len(rows) != len(jobs):
    fail("MAN jobs != META jobs")
allm = set()
for r in ls:
    row = byj[r["j"]]
    nm = row["new_modules"].split(",")
    if nm != r["m"]:
        fail(f"{r['j']}: MAN new_modules != META m")
    if any(x != "rc=0" for x in row["new_rc"].split(",")):
        fail(f"{r['j']}: new_rc {row['new_rc']}")
    hs = row["new_olean_sha256"].split(",")
    if len(hs) != len(nm):
        fail(f"{r['j']}: {len(hs)} olean shas for {len(nm)} modules")
    for m, h in zip(nm, hs):
        p = os.path.join(B, "x", "build", m.replace(".", "/") + ".olean")
        if not os.path.isfile(p) or sh(p) != h:
            fail(f"{m}: olean missing or sha differs from MAN")
        allm.add(m)
have = {os.path.relpath(p, os.path.join(B, "x", "build"))[:-6].replace("/", ".") for p in glob.glob(os.path.join(B, "x", "build", "KC1337", "*", "*.olean"))}
if have != allm:
    fail(f"oleans outside META m: {sorted(have - allm)[:3]}, missing: {sorted(allm - have)[:3]}")
print(f"OK bundle {SUMS} {sh(os.path.join(B, SUMS))[:8]}: {len(ls)} jobs, {len(allm)} modules, all rc=0, MAN olean shas match")
