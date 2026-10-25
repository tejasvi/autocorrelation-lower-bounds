"""k39asm.py: assembly of the K39 kernel-only proof from the per-job check modules (nothing here is trusted).

usage: k39asm.py plan OUTDIR PKG NS N A B META... [--smax L] [--gmax J] [--forms TEMPLATE]
  META     the k39export.py metadata files (JSON lines: j, r, s, l, m = the job's check modules)
Links every delegated path hash to the job whose root path has that hash (exactly once each, exactly one job without
parent = the root job "root"), takes as TOP the jobs whose subtree has more than --smax leaves or --gmax jobs, packs the
frontier subtrees (a non-top job with a top parent, with all its descendants) into G modules of at most --gmax jobs, and
writes:
  PKG/G<i>.lean   imports Params and the check module of each of its jobs; per job, children first,
                  theorem jfull_<jid> : AutocorrK.StkK P A B [jb_<jid>] := .seg _ _ jc_<jid>_1 (.cons jfull_<child> ...)
  PKG/Top.lean    imports every G module and the top jobs' check modules; jfull_<jid> of the top jobs, children first
  PKG/Main.lean   the bound from jfull_root (AutocorrK.stkK_sound, AutocorrK.halfClaim_of_rootK), with the interface of
                  the native Main (halfClaim over the rational lam, ofReal_lam, autocorr_lower)
  PKG/Forms.lean  TEMPLATE (the approved native Forms) with its import and namespace renamed
  plan.json       counts; modules.txt the build order (G modules, Top, Main, Forms)
"""
import sys, os, json, time, argparse
from array import array
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kc_jobs as KJ        # noqa: E402  (fprop, b64)
import verify               # noqa: E402


def log(*a):
    print(time.strftime("%H:%M:%S"), *a, flush=True)


def jfull_term(jid, segs, kid):
    term, closes = "", 0
    for i, dl in enumerate(segs, 1):
        term += f".seg _ _ jc_{jid}_{i} (" + "".join(f".cons jfull_{kid[h]} (" for h in dl)
        closes += len(dl) + 1
    return term + ".nil" + ")" * closes


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd"); ap.add_argument("outdir"); ap.add_argument("pkg"); ap.add_argument("ns")
    ap.add_argument("n", type=int); ap.add_argument("a", type=int); ap.add_argument("b", type=int)
    ap.add_argument("meta", nargs="+")
    ap.add_argument("--smax", type=int, default=400000)
    ap.add_argument("--gmax", type=int, default=20000)
    ap.add_argument("--forms", default=None)
    args = ap.parse_args()
    t0 = time.time()
    jid, root, segs, nl, mod = [], [], [], array("I"), []
    seen = {}
    errors = []
    for fn in args.meta:
        for line in open(fn):
            d = json.loads(line)
            if "error" in d:
                errors.append(("export error", d["j"], d["error"][:200])); continue
            if d["j"] in seen:
                errors.append(("job twice", d["j"])); continue
            seen[d["j"]] = len(jid)
            jid.append(d["j"]); root.append(d["r"]); segs.append(d["s"]); nl.append(d["l"]); mod.append(d["m"])
    N = len(jid)
    byroot = {}
    for k in range(N):
        if root[k] in byroot:
            errors.append(("root path twice", jid[k], jid[byroot[root[k]]]))
        byroot[root[k]] = k
    parent = array("i", [-1]) * N
    kidj = {}                       # delegated path hash -> child job id
    for k in range(N):
        for dl in segs[k]:
            for h in dl:
                c = byroot.get(h)
                if c is None:
                    errors.append(("delegated path without job", jid[k], h)); continue
                if parent[c] != -1:
                    errors.append(("path delegated twice", jid[c])); continue
                parent[c] = k; kidj[h] = jid[c]
    roots = [k for k in range(N) if parent[k] == -1]
    if [jid[k] for k in roots] != ["root"]:
        errors.append(("roots", len(roots), [jid[k] for k in roots[:5]]))
    if errors:
        json.dump(errors[:2000], open(os.path.join(args.outdir, "plan_errors.json"), "w"), indent=0)
        log("ERRORS", len(errors), errors[:5]); sys.exit(1)
    r0 = roots[0]
    kids = [[] for _ in range(N)]
    for k in range(N):
        if parent[k] >= 0:
            kids[parent[k]].append(k)
    order = []                      # post-order
    st = [(r0, False)]
    while st:
        k, done = st.pop()
        if done:
            order.append(k); continue
        st.append((k, True))
        for c in kids[k]:
            st.append((c, False))
    assert len(order) == N, "tree not connected"
    subl = array("Q", nl); subj = array("Q", [1]) * N
    for k in order:
        p = parent[k]
        if p >= 0:
            subl[p] += subl[k]; subj[p] += subj[k]
    top = bytearray(N)
    for k in range(N):
        if subl[k] > args.smax or subj[k] > args.gmax:
            top[k] = 1
    if not top[r0]:
        top[r0] = 1                 # the root job always goes to Top (Main refers to it there)
    frontier = [k for k in range(N) if not top[k] and (parent[k] < 0 or top[parent[k]])]
    pos = {k: i for i, k in enumerate(order)}
    # pack frontier subtrees (largest first) into G modules of at most gmax jobs
    bins = []
    for r in sorted(frontier, key=lambda r: -subj[r]):
        for bn in bins:
            if bn[0] + subj[r] <= args.gmax:
                bn[0] += subj[r]; bn[1].append(r); break
        else:
            bins.append([subj[r], [r]])
    base = os.path.join(args.outdir, args.pkg)
    os.makedirs(base, exist_ok=True)
    hdr = f"set_option Elab.async false\nset_option maxRecDepth 100000\n\nnamespace {args.ns}\n\nopen AutocorrK\n\nnoncomputable section\n"
    gmods = []
    for gi, (cnt, rs) in enumerate(bins):
        members = []
        for r in rs:                # the subtree of r, children first
            sub = []
            stk = [(r, False)]
            while stk:
                k, done = stk.pop()
                if done:
                    sub.append(k); continue
                stk.append((k, True))
                for c in kids[k]:
                    stk.append((c, False))
            members.extend(sub)
        src = [f"import {args.pkg}.Params\n"] + [f"import {m}\n" for k in members for m in mod[k]] + ["\n", hdr]
        for k in members:
            src.append(f"\ntheorem jfull_{jid[k]} : AutocorrK.StkK P {args.a} {args.b} [jb_{jid[k]}] :=\n"
                       f"  {jfull_term(jid[k], segs[k], kidj)}\n")
        src.append(f"\nend\n\nend {args.ns}\n")
        name = f"{args.pkg}.G{gi:05d}"
        KJ.write_file(os.path.join(base, f"G{gi:05d}.lean"), "".join(src))
        gmods.append(name)
    tops = [k for k in order if top[k]]
    src = ([f"import {args.pkg}.Params\n"] + [f"import {g}\n" for g in gmods] + [f"import {m}\n" for k in tops for m in mod[k]]
           + ["\n", hdr])
    for k in tops:
        src.append(f"\ntheorem jfull_{jid[k]} : AutocorrK.StkK P {args.a} {args.b} [jb_{jid[k]}] :=\n"
                   f"  {jfull_term(jid[k], segs[k], kidj)}\n")
    src.append(f"\nend\n\nend {args.ns}\n")
    KJ.write_file(os.path.join(base, "Top.lean"), "".join(src))
    spec = verify.Spec(args.n)
    _, K0 = KJ.fprop(spec.tree, [0.0] * spec.nB, [1.0] * spec.nB)
    UP = sum((1 << 30) << (32 * b) for b in range(spec.nB))
    n, a, b, ns = args.n, args.a, args.b, args.ns
    q = f"{a} / {b}"
    main_src = f"""import {args.pkg}.Top
import AutocorrK39.Sound.Run
import Autocorr.Reduction

/-!
# C₁ ≥ {a}/{b}: the certificate (n = {n}) checked by the Lean kernel (K39 checker, no native code)

{N} jobs, {sum(nl)} leaves; one core-only module per job, every segment of its DFS log a `decide +kernel` check of
`AutocorrK.segCheck`, composed by `AutocorrK.StkK` in {len(gmods)} G modules and `Top`.
-/

open MeasureTheory ENNReal Set

namespace {ns}

noncomputable def UP : ℕ := nat_b64% "{KJ.b64(UP)}"

theorem hupP : ∀ b < P.nB, AutocorrK.get32 UP b = 2 ^ 30 := by decide +kernel

theorem root_eq : AutocorrK.propK P {K0} 0 UP = jb_root := by decide +kernel

theorem kpf : AutocorrK.KPFacts (Autocorr.Cert.mkSpec {n}) P := AutocorrK.kpFacts kpok

theorem halfClaimK : HalfClaim {n} ((({a} : ℕ) : ℝ) / (({b} : ℕ) : ℝ)) := by
  have h := (AutocorrK.stkK_sound kpf (by norm_num) (by norm_num) jfull_root).head
  rw [← root_eq] at h
  have hup : ∀ b < (Autocorr.Cert.mkSpec {n}).nB, AutocorrK.get32 UP b = 2 ^ 30 := by
    rw [← kpf.nB]; exact hupP
  have hn : (Autocorr.Cert.mkSpec {n}).n = {n} := by rw [← kpf.n]; rfl
  have := AutocorrK.halfClaim_of_rootK kpf hup h
  rwa [hn] at this

theorem halfClaim : HalfClaim {n} ((({q} : ℚ)) : ℝ) := by
  rw [show ((({q} : ℚ)) : ℝ) = (({a} : ℕ) : ℝ) / (({b} : ℕ) : ℝ) by push_cast; norm_num]
  exact halfClaimK

lemma ofReal_lam : ENNReal.ofReal ((({q} : ℚ)) : ℝ) = ({q} : ℝ≥0∞) := by
  rw [show ((({q} : ℚ)) : ℝ) = ({a} : ℝ) / {b} by norm_num, ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

/-- `C₁ ≥ {a}/{b}`: for every measurable `f : ℝ → [0, ∞]`,
`{a}/{b} · (∫_{{-1/4}}^{{1/4}} f)² ≤ sup_{{t ∈ [-1/2, 1/2]}} ∫ f(t - x) f(x) dx`. -/
theorem autocorr_lower (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ({q} : ℝ≥0∞) * (∫⁻ x in Icc (-1/4 : ℝ) (1/4), f x) ^ 2 ≤
      ⨆ t ∈ Icc (-1/2 : ℝ) (1/2), ∫⁻ x, f (t - x) * f x := by
  rw [← ofReal_lam]
  exact autocorr_lower_of_halfClaim (by norm_num) (by norm_num) halfClaim f hf

end {ns}
"""
    KJ.write_file(os.path.join(base, "Main.lean"), main_src)
    mods = gmods + [f"{args.pkg}.Top", f"{args.pkg}.Main"]
    if args.forms:
        t = open(args.forms).read()
        old_ns = [l.split()[1] for l in t.splitlines() if l.startswith("namespace ")][0]
        old_imp = [l.split()[1] for l in t.splitlines() if l.startswith("import ") and l.endswith(".Main")][0]
        t = t.replace(f"import {old_imp}\n", f"import {args.pkg}.Main\n").replace(old_imp, f"{args.pkg}.Main")
        t = t.replace(f"namespace {old_ns}\n", f"namespace {ns}\n").replace(f"end {old_ns}\n", f"end {ns}\n")
        KJ.write_file(os.path.join(base, "Forms.lean"), t)
        mods.append(f"{args.pkg}.Forms")
    open(os.path.join(args.outdir, "modules.txt"), "w").write("".join(m + "\n" for m in mods))
    plan = {"jobs": N, "leaves": int(sum(nl)), "top_jobs": len(tops), "frontier": len(frontier), "g_modules": len(gmods),
            "largest_g_jobs": max((bn[0] for bn in bins), default=0), "smax": args.smax, "gmax": args.gmax, "K0": K0,
            "secs": round(time.time() - t0)}
    json.dump(plan, open(os.path.join(args.outdir, "plan.json"), "w"), indent=1)
    log("plan", json.dumps(plan))


if __name__ == "__main__":
    main()
