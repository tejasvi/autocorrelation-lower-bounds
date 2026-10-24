"""scan.py CERTDIR EXPECTED_SHA_LIST OUTDIR WORKERS: one pass over every job file of the extracted certificate.
For each file: sha256 + size of the gz bytes, a complete decompression, and the count of tree-only records (lines that
start with ["U" or ["T"). Writes OUTDIR/inputs.sha256 ("sha256 size name", sorted), OUTDIR/ujobs.txt (files with tree-only
records), OUTDIR/scan.json (totals). Compares the files with EXPECTED_SHA_LIST ("sha256  name" lines, the union of the
certificate VMs' jobs_*.sha256 lists): exit 0 only if the two sets of (name, sha256) are equal."""
import os, sys, gzip, json, hashlib
from multiprocessing import Pool

cd, expf, out, workers = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
J = os.path.join(cd, "jobs")


def one(name):
    p = os.path.join(J, name)
    b = open(p, "rb").read()
    h = hashlib.sha256(b).hexdigest()
    try:
        txt = gzip.decompress(b)
        ok = True
    except Exception:
        txt, ok = b"", False
    u = sum(1 for line in txt.split(b"\n") if line.startswith(b'["U"') or line.startswith(b'["T"'))
    return name, h, len(b), ok, u


if __name__ == "__main__":
    names = sorted(n for n in os.listdir(J) if n.endswith(".jsonl.gz"))
    with Pool(workers) as pool:
        res = pool.map(one, names, chunksize=256)
    os.makedirs(out, exist_ok=True)
    with open(os.path.join(out, "inputs.sha256"), "w") as fh:
        for n, h, s, ok, u in res:
            fh.write(f"{h} {s} {n}\n")
    bad_gz = [r[0] for r in res if not r[3]]
    uj = [r for r in res if r[4] > 0]
    with open(os.path.join(out, "ujobs.txt"), "w") as fh:
        for r in uj:
            fh.write(f"{r[0]}\t{r[4]}\n")
    exp = {}
    for line in open(expf):
        parts = line.split()
        if len(parts) >= 2:
            name = os.path.basename(parts[-1])
            if name in exp and exp[name] != parts[0]:
                exp[name] = "CONFLICT"
            else:
                exp[name] = parts[0]
    have = {r[0]: r[1] for r in res}
    missing = sorted(set(exp) - set(have))
    extra = sorted(set(have) - set(exp))
    differ = sorted(n for n in have if n in exp and exp[n] != have[n])
    tot = dict(files=len(res), bytes=sum(r[2] for r in res), bad_gzip=len(bad_gz), ujobs=len(uj), urecords=sum(r[4] for r in uj),
               expected=len(exp), missing=len(missing), extra=len(extra), differ=len(differ),
               examples=dict(missing=missing[:5], extra=extra[:5], differ=differ[:5], bad_gzip=bad_gz[:5]))
    json.dump(tot, open(os.path.join(out, "scan.json"), "w"), indent=1)
    print(json.dumps(tot))
    sys.exit(0 if not (bad_gz or missing or extra or differ) else 1)
