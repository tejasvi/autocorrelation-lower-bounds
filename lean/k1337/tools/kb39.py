"""kb39.py: K39 kernel-checker export for a bench (and the record encoder for a later production exporter).

usage: kb39.py CERTDIR OUTDIR PKG [--jobs LIST] [--group-leaves G] [--seg-leaves S] [--mb-dense N]
  CERTDIR  meta.json + jobs/*.jsonl.gz (filled certificate jobs: records I, K, D, L, S)
  OUTDIR   root of the Lean tree; modules are written to OUTDIR/PKG/ (PKG.Params, PKG.C<i>, PKG.MB)
  --jobs   file with the job file names to export (default: all)
Writes Params.lean (the KP constants of n and `kpok`, the one-time kernel check of kpOK against mkSpec n), check
modules C<i>.lean (per job: root box, per segment the data literal and `segCheck ... = true := by decide +kernel`;
no assembly modules: a bench measures the checks) and, with --mb-dense N, MB.lean: N k-block cuts of the sample, each
evaluated alone by `denseStep` with a continuation that forces the accumulators.  Prints per-job statistics as JSON
lines to OUTDIR/PKG/stats.jsonl.

Record format (AutocorrK39.loop): 88-bit chunks; a row dual `row (15) | sign (1) | |Y| (72)`; a two-block cut
`32767 (15) | 0 | d (7) | e (7) | s0 a0 (22) | s1 a1 (22) | s2 a2 (22) | M (64)` in two chunks; a k-block cut
`32766 (15) | 0 | k (7) | s0 (1) | a0 (21) | M (64) | k x (b (7) | s (1) | a (21))` in ceil((109 + 29k)/88) chunks.
D records (compressed leaves) are completed here (verify_cmp.complete_duals: P, G, ZA duals) and the leaf is re-checked
exactly on the rounded duals (kc_ref.kc_accept).  Nothing here is trusted.
"""
import sys, os, json, gzip, argparse, time
from fractions import Fraction as Fr

sys.set_int_max_str_digits(0)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kc_jobs as KJ        # noqa: E402  (b64, pack, fprop, fchild, pk_box, path_key, split_big, lbox; checker path)
import kc_ref               # noqa: E402
import kc_export as KE      # noqa: E402
import verify               # noqa: E402
import verify_cmp           # noqa: E402

G = {}
SB = 30


def init(n, rowkeys, lam):
    spec = verify.Spec(n)
    G["tree"] = spec.tree
    G["ks"] = kc_ref.KSpec(n)
    G["vspec"] = verify_cmp.Spec(n)
    G["imp"] = verify_cmp.Implied(G["vspec"], rowkeys)
    G["rowkeys"] = rowkeys
    G["rindex"] = {k: i for i, k in enumerate(rowkeys)}
    assert len(rowkeys) < 32766
    G["lam"] = lam
    G["root"], _ = KJ.fprop(spec.tree, [0.0] * spec.nB, [1.0] * spec.nB)
    G["nB"] = spec.nB


def nch_dense(k):
    return (109 + 29 * k + 87) // 88


def enc_cut(key, M):
    """(value, width) of a cut record."""
    assert 0 < M < (1 << 64)
    if key[0] == "sq":
        _, v0, d, v1, e, v2 = key
        assert d < 128 and e < 128
        x = 32767 | (d << 16) | (e << 23)
        for off, v in ((30, v0), (52, v1), (74, v2)):
            assert abs(v) < (1 << 21)
            x |= ((1 if v < 0 else 0) | (abs(v) << 1)) << off
        return x | (M << 96), 176
    _, v0, terms = key
    k = len(terms)
    assert 3 <= k <= 126 and abs(v0) < (1 << 21)
    x = 32766 | (k << 16) | ((1 if v0 < 0 else 0) << 23) | (abs(v0) << 24) | (M << 45)
    for i, (b, v) in enumerate(terms):
        assert 0 <= b < 128 and abs(v) < (1 << 21)
        x |= (b | ((1 if v < 0 else 0) << 7) | (abs(v) << 8)) << (109 + 29 * i)
    return x, 88 * nch_dense(k)


def job39(f, seg_leaves, stats=None, dense_out=None):
    """As kc_jobs.kc_job, in the K39 format, with D records. Returns (root path key, root box, segments, nleaves,
    file); a segment is (nrec, data, delegated path keys, boxes of the stack at its end (head first))."""
    tree, root, ks, rindex, lam = G["tree"], G["root"], G["ks"], G["rindex"], G["lam"]
    rowkeys, vspec, imp = G["rowkeys"], G["vspec"], G["imp"]
    with gzip.open(f, "rt") as fh:
        h = json.loads(fh.readline())
        recs = [json.loads(line) for line in fh]
    path = [(int(b), Fr(s), int(side)) for b, s, side in h["path"]]
    reg = root
    for b, s, side in path:
        reg, _ = KJ.fchild(tree, reg, b, float(s), side)
        if reg is None:
            raise AssertionError(f"empty job root {f}")
    stack = [(reg, path)]
    segs = []
    parts, nrec, nl_seg, dels = [], 0, 0, []
    nleaves = 0
    cuts = {}
    last = max((i for i, r in enumerate(recs) if r[0] != "K"), default=-1)
    st = dict(leaves=0, rows=0, aux=0, cuts2=0, cutsk=0, kterms=0, chunks=0, maxcnt=0, minmargin=None)

    def resolve(ex):
        out = []
        for t in ex:
            key = t[0]
            if type(key) is int:
                key = cuts[key]
            vspec.sq_row(key)            # validates the key
            out.append((key, Fr(t[1])))
        return out
    for i, rec in enumerate(recs):
        if rec[0] == "K":
            if len(rec) != 3 or type(rec[1]) is not int or rec[1] in cuts:
                raise AssertionError(f"bad K record in {f}")
            vspec.sq_row(rec[2])
            cuts[rec[1]] = rec[2]
            continue
        rg, pth = stack.pop()
        kind = rec[0]
        nrec += 1
        if kind == "I":
            b, s = rec[1], Fr(rec[2])
            c0, k0 = KJ.fchild(tree, rg, b, float(s), 0)
            c1, k1 = KJ.fchild(tree, rg, b, float(s), 1)
            if c0 is None or c1 is None:
                raise AssertionError(f"empty child in {f}: not supported by the kernel checker")
            sv = s * (1 << SB)
            assert sv.denominator == 1 and 0 < sv.numerator < (1 << 31) and b < 128 and k0 < 16 and k1 < 16
            parts.append(((b << 2) | (sv.numerator << 9) | (k0 << 40) | (k1 << 44), 48))
            stack.append((c0, pth + [(b, s, 0)])); stack.append((c1, pth + [(b, s, 1)]))
        elif kind in ("L", "D"):
            Lf = [Fr(x) for x in rg[0]]; Uf = [Fr(x) for x in rg[1]]
            if kind == "L":
                if len(rec) not in (4, 5):
                    raise AssertionError(f"bad L record in {f}")
                idx, vals = rec[2], [Fr(v) for v in rec[3]]
                ex = resolve(rec[4]) if len(rec) == 5 else []
                naux = 0
            else:
                if len(rec) not in (5, 6) or type(rec[2]) is not int or len(rec[3]) != len(rec[4]):
                    raise AssertionError(f"bad D record in {f}")
                idx = list(rec[3]); vals = [Fr(v, 2 ** rec[2]) for v in rec[4]]
                ex = resolve(rec[5]) if len(rec) == 6 else []
                aux = verify_cmp.complete_duals(vspec, (Lf, Uf), rowkeys, imp, list(zip(idx, vals)), ex)
                naux = len(aux)
                idx = idx + [r for r, _ in aux]; vals = vals + [y for _, y in aux]
            duals = KJ.split_big(kc_ref.kc_duals(ks, rowkeys, idx, vals))
            cdu = kc_ref.kc_cut_duals(ex)
            ok, lb = kc_ref.kc_accept(ks, lam, Lf, Uf, duals + cdu)
            if not ok:
                raise AssertionError(f"KC re-check failed in {f}: {float(lb)}")
            cparts = [enc_cut(key, M) for key, M in cdu]
            cnt = len(duals) + sum(w // 88 for _, w in cparts)
            assert cnt < 16384
            parts.append((1 | (cnt << 2), 16))
            for key, Y in duals:
                assert 0 < abs(Y) < (1 << 72)
                parts.append((rindex[key] | ((1 if Y < 0 else 0) << 15) | (abs(Y) << 16), 88))
            parts.extend(cparts)
            st["leaves"] += 1; st["rows"] += len(duals); st["aux"] += naux; st["chunks"] += cnt
            st["maxcnt"] = max(st["maxcnt"], cnt)
            mg = float(lb - lam)
            st["minmargin"] = mg if st["minmargin"] is None else min(st["minmargin"], mg)
            for key, M in cdu:
                if key[0] == "sq":
                    st["cuts2"] += 1
                else:
                    st["cutsk"] += 1; st["kterms"] += len(key[2])
                    if dense_out is not None:
                        dense_out.append(enc_cut(key, M)[0])
            nleaves += 1; nl_seg += 1
        elif kind == "S":
            parts.append((2, 2))
            dels.append((KJ.path_key(pth), KJ.pk_box(rg)))
        else:
            raise AssertionError(f"record {kind} not supported by the kernel checker ({f})")
        if (nl_seg >= seg_leaves and i < last) or i == last:
            segs.append((nrec, KJ.pack(parts), dels, [KJ.pk_box(r) for r, _ in reversed(stack)]))
            parts, nrec, nl_seg, dels = [], 0, 0, []
    if stack:
        raise AssertionError(f"nodes left in {f}")
    if stats is not None:
        stats.update(st)
    return KJ.path_key(path), KJ.pk_box(reg), segs, nleaves, os.path.basename(f)


def module_text(pkg, jobs_out, a, b, nB):
    """A check module: per job, the root box and its segments' checks."""
    out = [f"import {pkg}.Params\n\nset_option Elab.async false\n\nnamespace {pkg}\n\nopen AutocorrK\n\nnoncomputable section\n"]
    for k, (pk, rootbox, segs, nl, fname) in jobs_out:
        out.append(f"\n-- job {fname}: {nl} leaves, {len(segs)} segments\n")
        out.append(f"def jb{k} : Nat × Nat := {KJ.lbox(rootbox)}\n")
        sin = f"[jb{k}]"
        for i, (nrec, data, dels, stk) in enumerate(segs, 1):
            if i < len(segs):
                w = 32 * nB
                lit = KJ.pack([(lo | (up << w), 2 * w) for lo, up in stk])
                out.append(f"def js{k}_{i} : List (Nat × Nat) := AutocorrK.unpk {w} {len(stk)} (nat_b64% \"{KJ.b64(lit)}\")\n")
                rest = f"js{k}_{i}"
            else:
                assert not stk
                rest = "[]"
            dq = []
            for j, (c, bx) in enumerate(dels):
                out.append(f"def jq{k}_{i}_{j} : Nat × Nat := {KJ.lbox(bx)}\n")
                dq.append(f"jq{k}_{i}_{j}")
            sout = "".join(f"{q} :: " for q in dq) + rest
            out.append(f"def jd{k}_{i} : Nat := nat_b64% \"{KJ.b64(data)}\"\n")
            out.append(f"theorem jc{k}_{i} : AutocorrK.segCheck P {a} {b} {nrec} jd{k}_{i} {sin} ({sout}) = true := "
                       f"by decide +kernel\n")
            sin = rest
    out.append(f"\nend\n\nend {pkg}\n")
    return "".join(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("certdir")
    ap.add_argument("outdir")
    ap.add_argument("pkg")
    ap.add_argument("--jobs", default=None)
    ap.add_argument("--group-leaves", type=int, default=40)
    ap.add_argument("--seg-leaves", type=int, default=1)
    ap.add_argument("--mb-dense", type=int, default=0)
    ap.add_argument("--skip-errors", action="store_true", help="bench: log a job that fails to export and go on")
    args = ap.parse_args()
    meta = json.load(open(os.path.join(args.certdir, "meta.json")))
    n = meta["n"]; lam = Fr(meta["lam"])
    spec = verify.Spec(n)
    rowkeys = [tuple(spec.validate_key(tuple(k))) for k in meta["rowkeys"]]
    init(n, rowkeys, lam)
    if args.jobs:
        names = [l.strip() for l in open(args.jobs) if l.strip()]
    else:
        names = sorted(os.listdir(os.path.join(args.certdir, "jobs")))
    base = os.path.join(args.outdir, args.pkg)
    os.makedirs(base, exist_ok=True)
    a, b = lam.numerator, lam.denominator
    kp, _ = KE.kp_constants(n, rowkeys)
    params = f"""import AutocorrK39.Stk
import AutocorrK39.Table
import AutocorrK39.Load

/-! Constants of the K39 kernel checker for n = {n} and their one-time kernel check against `mkSpec {n}`. -/

set_option Elab.async false

namespace {args.pkg}

noncomputable def P : AutocorrK.KP := ⟨{kp['n']}, {kp['nB']}, {kp['oZ']}, {kp['oP']}, {kp['oG']}, {kp['NC1']}, {kp['NR']},
  nat_b64% "{KJ.b64(kp['T'])}", nat_b64% "{KJ.b64(kp['symP'])}", nat_b64% "{KJ.b64(kp['symN'])}",
  nat_b64% "{KJ.b64(kp['intTab'])}", {kp['nInt']}, nat_b64% "{KJ.b64(kp['canonTab'])}"⟩

theorem kpok : AutocorrK.kpOK (Autocorr.Cert.mkSpec {n}) P = true := by decide +kernel

end {args.pkg}
"""
    KJ.write_file(os.path.join(base, "Params.lean"), params)
    t0 = time.time()
    group, gl, gi, dense = [], 0, 0, []
    sf = open(os.path.join(base, "stats.jsonl"), "w")
    for j, name in enumerate(names):
        st = {}
        t1 = time.time()
        try:
            res = job39(os.path.join(args.certdir, "jobs", name), args.seg_leaves, st,
                        dense if len(dense) < args.mb_dense else None)
        except Exception as e:
            if not args.skip_errors:
                raise
            sf.write(json.dumps({"file": name, "error": repr(e)[:300]}) + "\n"); sf.flush()
            continue
        st["file"] = name; st["export_s"] = round(time.time() - t1, 3); st["module"] = f"C{gi:03d}"
        sf.write(json.dumps(st) + "\n"); sf.flush()
        group.append((j, res)); gl += res[3]
        if gl >= args.group_leaves:
            KJ.write_file(os.path.join(base, f"C{gi:03d}.lean"), module_text(args.pkg, group, a, b, spec.nB))
            group, gl, gi = [], 0, gi + 1
    if group:
        KJ.write_file(os.path.join(base, f"C{gi:03d}.lean"), module_text(args.pkg, group, a, b, spec.nB))
        gi += 1
    if args.mb_dense:
        src = [f"import {args.pkg}.Params\n\nset_option Elab.async false\n\nnamespace {args.pkg}\n\n"]
        for i, x in enumerate(dense[:args.mb_dense]):
            src.append(f"theorem md{i} : AutocorrK.denseStep P (nat_b64% \"{KJ.b64(x)}\") "
                       f"(fun _ rp rn _ _ _ an => Nat.ble 0 (Nat.add rp (Nat.add rn an))) 0 0 0 0 0 0 = true := "
                       f"by decide +kernel\n")
        src.append(f"\nend {args.pkg}\n")
        KJ.write_file(os.path.join(base, "MB.lean"), "".join(src))
    print(f"{len(names)} jobs, {gi} check modules, {min(len(dense), args.mb_dense)} dense micro checks, "
          f"{time.time() - t0:.1f}s", flush=True)


if __name__ == "__main__":
    main()
