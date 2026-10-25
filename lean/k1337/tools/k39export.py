"""k39export.py: K39 fleet export (kernel-only C1 proof, one check module per job). Nothing here is trusted.

usage: k39export.py CERTDIR OUTDIR PKG NS LIST [--workers W] [--seg-leaves S] [--seg-per-mod M]
  CERTDIR  meta.json + jobs/*.jsonl.gz (filled jobs: records I, K, D, L, S)
  OUTDIR   root of the Lean tree; writes OUTDIR/PKG/Params.lean and one module per job,
           OUTDIR/PKG/C<jid[:2]>/J<jid>.lean (module PKG.C<jid[:2]>.J<jid>; a job with more than M segments continues in
           J<jid>_p<k>, whose first segment starts from jsin_<jid>_p<k>, a copy of the previous part's last stack),
           declarations in namespace NS
  LIST     job file names to export (one per line)
Per job (records encoded by kb39.job39: K39 format, D records completed, every leaf re-checked exactly):
    def jb_<jid> : Nat × Nat                                   the job's root box
    def js_<jid>_<i> : List (Nat × Nat)                        the DFS stack after segment i (not after the last)
    def jq_<jid>_<i>_<j> : Nat × Nat                           the box of the j-th delegated subtree of segment i
    def jd_<jid>_<i> : Nat                                     the records of segment i
    theorem jc_<jid>_<i> : segCheck P a b nrec jd (sin) (jq.. :: rest) = true := by decide +kernel
and one JSON line in OUTDIR/PKG/meta_<LISTNAME>.jsonl: {"j": jid, "r": H(root path), "s": [[H(path) of each delegated
subtree] per segment], "l": leaves, "m": module, "e": export seconds}; H = blake2b-80 of repr(path key).  The assembly
(k39asm.py) composes the jobs: jfull_<jid> := .seg _ _ jc_<jid>_1 (.cons jfull_<child> (... .nil)), where the child of a
delegated path is the job whose root path has that hash (the kernel checks jq = the child's jb, both literals).
"""
import sys, os, json, time, argparse, hashlib
from fractions import Fraction as Fr
from multiprocessing import get_context

sys.set_int_max_str_digits(0)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kb39 as KB           # noqa: E402  (init, job39; kc_jobs helpers via KB.KJ)
import kc_export as KE      # noqa: E402
import verify               # noqa: E402

A = {}


def H(pk):
    return hashlib.blake2b(repr(pk).encode(), digest_size=10).hexdigest()


def winit(certdir, outdir, pkg, ns, seg_leaves, spm):
    meta = json.load(open(os.path.join(certdir, "meta.json")))
    n = meta["n"]; lam = Fr(meta["lam"])
    spec = verify.Spec(n)
    rowkeys = [tuple(spec.validate_key(tuple(k))) for k in meta["rowkeys"]]
    KB.init(n, rowkeys, lam)
    A.update(certdir=certdir, outdir=outdir, pkg=pkg, ns=ns, seg=seg_leaves, a=lam.numerator, b=lam.denominator,
             nB=spec.nB, spm=spm)


def modpath(pkg, jid, k=0):
    nm = f"J{jid}" if k == 0 else f"J{jid}_p{k}"
    return f"{pkg}.C{jid[:2]}.{nm}", os.path.join(pkg, f"C{jid[:2]}", f"{nm}.lean")


def one(name):
    t0 = time.time()
    jid = name[:-len(".jsonl.gz")]
    pk, rootbox, segs, nl, fname = KB.job39(os.path.join(A["certdir"], "jobs", name), A["seg"])
    pkg, ns, a, b, nB, spm = A["pkg"], A["ns"], A["a"], A["b"], A["nB"], A["spm"]
    w = 32 * nB
    hdr = f"import {pkg}.Params\n\nset_option Elab.async false\n\nnamespace {ns}\n\nopen AutocorrK\n\nnoncomputable section\n"
    mods, sm = [], []
    nparts = (len(segs) + spm - 1) // spm
    for k in range(nparts):
        mod, rel = modpath(pkg, jid, k)
        lo, hi = k * spm + 1, min(len(segs), (k + 1) * spm)
        out = [hdr, f"\n-- job {fname}: {nl} leaves, {len(segs)} segments; part {k} of {nparts}: segments {lo}..{hi}\n"]
        if k == 0:
            out.append(f"def jb_{jid} : Nat × Nat := {KB.KJ.lbox(rootbox)}\n")
            sin = f"[jb_{jid}]"
        else:
            stk = segs[lo - 2][3]          # the stack after the previous part's last segment
            lit = KB.KJ.pack([(l_ | (u_ << w), 2 * w) for l_, u_ in stk])
            out.append(f"def jsin_{jid}_p{k} : List (Nat × Nat) := AutocorrK.unpk {w} {len(stk)} (nat_b64% \"{KB.KJ.b64(lit)}\")\n")
            sin = f"jsin_{jid}_p{k}"
        for i in range(lo, hi + 1):
            nrec, data, dels, stk = segs[i - 1]
            if i < len(segs):
                lit = KB.KJ.pack([(l_ | (u_ << w), 2 * w) for l_, u_ in stk])
                out.append(f"def js_{jid}_{i} : List (Nat × Nat) := AutocorrK.unpk {w} {len(stk)} (nat_b64% \"{KB.KJ.b64(lit)}\")\n")
                rest = f"js_{jid}_{i}"
            else:
                assert not stk
                rest = "[]"
            qs = []
            for j, (c, bx) in enumerate(dels):
                out.append(f"def jq_{jid}_{i}_{j} : Nat × Nat := {KB.KJ.lbox(bx)}\n")
                qs.append(f"jq_{jid}_{i}_{j}")
            sout = "".join(f"{q} :: " for q in qs) + rest
            out.append(f"def jd_{jid}_{i} : Nat := nat_b64% \"{KB.KJ.b64(data)}\"\n")
            out.append(f"theorem jc_{jid}_{i} : AutocorrK.segCheck P {a} {b} {nrec} jd_{jid}_{i} {sin} ({sout}) = true := "
                       f"by decide +kernel\n")
            sm.append([H(c) for c, _ in dels])
            sin = rest
        out.append(f"\nend\n\nend {ns}\n")
        fn = os.path.join(A["outdir"], rel)
        os.makedirs(os.path.dirname(fn), exist_ok=True)
        with open(fn + ".tmp", "w") as fh:
            fh.write("".join(out))
        os.replace(fn + ".tmp", fn)
        mods.append(mod)
    return {"j": jid, "r": H(pk), "s": sm, "l": nl, "m": mods, "e": round(time.time() - t0, 3)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("certdir"); ap.add_argument("outdir"); ap.add_argument("pkg"); ap.add_argument("ns"); ap.add_argument("list")
    ap.add_argument("--workers", type=int, default=1)
    ap.add_argument("--seg-leaves", type=int, default=1)
    ap.add_argument("--seg-per-mod", type=int, default=64, help="segments per check module (a bigger job gets several)")
    args = ap.parse_args()
    names = [l.strip() for l in open(args.list) if l.strip()]
    meta = json.load(open(os.path.join(args.certdir, "meta.json")))
    n = meta["n"]; lam = Fr(meta["lam"])
    spec = verify.Spec(n)
    rowkeys = [tuple(spec.validate_key(tuple(k))) for k in meta["rowkeys"]]
    kp, _ = KE.kp_constants(n, rowkeys)
    base = os.path.join(args.outdir, args.pkg)
    os.makedirs(base, exist_ok=True)
    params = f"""import AutocorrK39.Stk
import AutocorrK39.Table
import AutocorrK39.Load

/-! Constants of the K39 kernel checker for n = {n} and their one-time kernel check against `mkSpec {n}`. -/

set_option Elab.async false

namespace {args.ns}

noncomputable def P : AutocorrK.KP := ⟨{kp['n']}, {kp['nB']}, {kp['oZ']}, {kp['oP']}, {kp['oG']}, {kp['NC1']}, {kp['NR']},
  nat_b64% "{KB.KJ.b64(kp['T'])}", nat_b64% "{KB.KJ.b64(kp['symP'])}", nat_b64% "{KB.KJ.b64(kp['symN'])}",
  nat_b64% "{KB.KJ.b64(kp['intTab'])}", {kp['nInt']}, nat_b64% "{KB.KJ.b64(kp['canonTab'])}"⟩

theorem kpok : AutocorrK.kpOK (Autocorr.Cert.mkSpec {n}) P = true := by decide +kernel

end {args.ns}
"""
    KB.KJ.write_file(os.path.join(base, "Params.lean"), params)
    t0 = time.time()
    mf = os.path.join(base, f"meta_{os.path.basename(args.list)}.jsonl")
    nfail = 0; nleaves = 0
    iargs = (args.certdir, args.outdir, args.pkg, args.ns, args.seg_leaves, args.seg_per_mod)
    with open(mf, "w") as fh:
        if args.workers > 1:
            with get_context("fork").Pool(args.workers, initializer=winit, initargs=iargs) as pool:
                it = pool.imap_unordered(safe, names, chunksize=4)
                for r in it:
                    fh.write(json.dumps(r) + "\n")
                    nfail += "error" in r; nleaves += r.get("l", 0)
        else:
            winit(*iargs)
            for nm in names:
                r = safe(nm)
                fh.write(json.dumps(r) + "\n")
                nfail += "error" in r; nleaves += r.get("l", 0)
    print(f"{len(names)} jobs, {nleaves} leaves, {nfail} failed, {time.time() - t0:.1f}s", flush=True)
    sys.exit(1 if nfail else 0)


def safe(name):
    try:
        return one(name)
    except Exception as e:
        return {"j": name, "error": repr(e)[:400]}


if __name__ == "__main__":
    main()
