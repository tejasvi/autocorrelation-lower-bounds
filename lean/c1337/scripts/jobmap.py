"""jobmap.py PKGDIR OUT.tsv EXPECTED_SHA_LIST [REPLACED_SHA_LIST]: per group module, the jobs it checks (from each generated module's `jobIds`
manifest, read before the build removes the sources): "module  job_id  sha256" lines. Exit 0 only if every job of
EXPECTED_SHA_LIST ("sha256  name"; entries of REPLACED_SHA_LIST, the U-filled copies, take precedence) appears
exactly once, with the same sha256, and nothing else appears."""
import os, re, sys, glob
from multiprocessing import Pool

pkgdir, out, expf = sys.argv[1:4]
repf = sys.argv[4] if len(sys.argv) > 4 and os.path.exists(sys.argv[4]) else None
pat = re.compile(r'^def jobIds : List \(String × String\) := \[(.*)\]$', re.M)
pair = re.compile(r'\("([0-9a-zA-Z_]+)", "([0-9a-f]{64})"\)')


def one(f):
    with open(f, encoding="utf-8") as fh:
        head = fh.read(8 << 20)
    m = pat.search(head)
    if not m:
        return f, None
    ns = re.search(r"^namespace (\S+)\.G([0-9a-f]+|root)$", head, re.M)
    return f, (ns.group(0).split()[1] if ns else os.path.basename(f), pair.findall(m.group(1)))


if __name__ == "__main__":
    files = sorted(glob.glob(os.path.join(pkgdir, "G*", "G*.lean")))
    with Pool(64) as pool:
        res = pool.map(one, files, chunksize=64)
    exp = {}
    for line in open(expf):
        p = line.split()
        if len(p) >= 2:
            exp[os.path.basename(p[-1]).replace(".jsonl.gz", "")] = p[0]
    if repf:
        for line in open(repf):
            p = line.split()
            if len(p) >= 2:
                exp[os.path.basename(p[-1]).replace(".jsonl.gz", "")] = p[0]
    seen = {}; bad = []; nomani = [f for f, r in res if r is None]
    with open(out, "w") as fh:
        for f, r in res:
            if r is None:
                continue
            mod, pairs = r
            for jid, h in pairs:
                fh.write(f"{mod}\t{jid}\t{h}\n")
                if jid in seen:
                    bad.append(("twice", jid))
                seen[jid] = h
    missing = [j for j in exp if j not in seen]
    extra = [j for j in seen if j not in exp]
    differ = [j for j in seen if j in exp and exp[j] != seen[j]]
    print(f"modules {len(files)} without manifest {len(nomani)} jobs {len(seen)} expected {len(exp)} missing {len(missing)} "
          f"extra {len(extra)} sha-differ {len(differ)} twice {len(bad)}")
    sys.exit(0 if not (nomani or missing or extra or differ or bad) else 1)
