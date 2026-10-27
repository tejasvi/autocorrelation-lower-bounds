#!/usr/bin/env python3
"""Kernel-only (K) data modules for the 4/3 nested certificate.

The module split, module names, statements and data terms are those of the native exporter n/gen_nest_data_run3.py
(with n/gen_lean_data.py): this file imports it and reuses Ctx/Enc/arc_term/sub_stmt, so a K module states exactly the
native module's statement (rX by python-flint 0.9.0, as in the native build). Per module, the K proof is a
list of unit theorems by `decide +kernel`:
  * W leaf at path p (T = records + hard-arc steps): head (headAt), hinted segments of SEG steps (two theorems each:
    `segFT` with the hints by decide, then `segF` through C64KChk.segF_of_segFT_len; a segment without a complete hint
    list is a plain `segF` theorem), and the rest after T steps (restF); joined by rest_of_seg / partAny_wit_of.
  * all-empty subtrees: KCover `.sub` units on the maximal subtrees without W nodes with at most ESUB empty leaves;
  * every other node outside a `.sub` unit (ivsplit, split, ext, an empty leaf): `.loc` partOK.
  okK : checkSubNK glob <args> node = true by C64KChk.checkSubNK_of_coverL (linear cover check covL); arc roots:
  checkArcNK glob arc = true through karc_eq : arc = .N .. knode.
Modules whose estimated kernel time exceeds --split-s are split: the unit theorems go to C64NData/KD_<M>_<i>.lean
(independent files, at most --split-s each); a last KD file holds only the assembly and okK (namespace C64NData.<M>).
K data modules import C64Core.Nest, C64Core.Load, C64NData.Glob, C64K.KHintGlue and C64K.KCoverL (core Lean only;
never C64K.KNestSim or C64K.KPieceSome). Glob.lean holds only `def glob`.

Modes (CERT = one part file cert_t25_sub_<P>.json.gz; the flags of the native build: --upper --max-recs 16000
--index-offset P):
  hg   CERT OUT [flags]           OUT/hg/HG_<M>.lean (or HG_<M>__<k>.lean: W paths in groups of at most --hg-steps
                                  1000 steps) and OUT/hg/ORDER (longest first): run against the compiled native data
                                  modules; output lines `HB [p] j <hex>` per W1 step
  k    CERT OUT --hints DIR       (hints DIR/<M>.hb and DIR/<M>__<k>.hb) OUT/<root>/<X>.lean (data modules + KD files),
                                  OUT/<root>/Glob.lean (root C64NData only), OUT/<root>/index.json (the native index
                                  piece), OUT/<root>/manifest_<P>.json, OUT/jobs.tsv
  cost CERT OUT                   no files: one JSON line per part (est_s, est_gb per module), hints assumed complete
  Options: --seg0 80 --seg 20 --seg2 20 (segment steps for W leaves with 0 / 1 / >= 2 tubes) --esub 8 --split-s 28800
           --chunk 64 --root C64NData (tests: another root, e.g. C64NDataK)
           --ntimes DIR (build logs <M>.log of the native data modules, with 'OK <ms>': adds the data elaboration to
           est_s)
           --pyflint DIR (sys.path entry with python-flint, e.g. an unpacked wheel)
"""
import argparse, json, os, re, sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))


def _setup_path():
    for i, a in enumerate(sys.argv):
        if a == "--pyflint" and i + 1 < len(sys.argv):
            sys.path.insert(0, sys.argv[i + 1])
    sys.path.insert(0, os.path.join(HERE, "n"))


_setup_path()
import gen_nest_data_run3 as G      # noqa: E402

EQ = G.EQ
TWO_EQ = 2 ** EQ

# ---- capture the encoder objects (the N planner and term writer unchanged; only the sub nodes are recorded) ----
_ENCS = []
_BaseEnc = G.Enc


class KEnc(_BaseEnc):
    def __init__(self, *a, **k):
        super().__init__(*a, **k)
        self.sub_nodes = []
        _ENCS.append(self)

    def tree(self, node, tubes, boxes, top=False):
        if not top and id(node) in self.ext:       # = the first branch of G.Enc.tree, plus the node record
            saved, self.cur = self.cur, []
            term = self.tree(node, tubes, boxes, top=True)
            kids, self.cur = self.cur, saved
            self.subs.append((list(tubes), list(boxes), term, G.count_recs(node), kids))
            self.sub_nodes.append(node)
            self.cur.append(len(self.subs) - 1)
            return ".ext"
        return _BaseEnc.tree(self, node, tubes, boxes, top)


G.Enc = KEnc


def shape(enc, node, tubes, top=False):
    """the module tree as G.Enc.tree writes it: kinds, children in NTree order, W record counts, tube intervals"""
    if not top and id(node) in enc.ext:
        return {"k": "X", "c": []}
    if "ivsplit" in node:
        k = node["ivsplit"]
        nm, q0, q1, ts, ms = tubes[k]
        qm = F(node["at"])
        lo = list(tubes); lo[k] = (nm, q0, qm, ts, ms)
        hi = list(tubes); hi[k] = (nm, qm, q1, ts, ms)
        a, b = node["kids"]
        return {"k": "I", "c": [shape(enc, a, lo), shape(enc, b, hi)]}
    if "split" in node:
        return {"k": "S", "c": [shape(enc, kd, tubes) for kd in node["kids"]]}
    if node["type"] == "empty":
        return {"k": "E", "c": [], "tubes": [(tb[1], tb[2]) for tb in tubes]}
    assert node["type"] == "W"
    items = sorted(node["tile_arcs"], key=lambda a: F(a["hard"][0]) if isinstance(a, dict) else F(a[0]))
    n = 0; kids = []
    for a in items:
        if isinstance(a, dict):
            q0, q1 = a["hard"]
            nt = (node["tile"], F(q0), F(q1), node["wrep_t"], node["wrep_m"])
            kids.append(shape(enc, a["child"], tubes + [nt]))
        else:
            n += 1
    return {"k": "W", "n": n, "h": len(kids), "c": kids, "tubes": [(tb[1], tb[2]) for tb in tubes]}


def annotate(sh):
    for c in sh["c"]:
        annotate(c)
    sh["hasW"] = sh["k"] == "W" or any(c["hasW"] for c in sh["c"])
    sh["ne"] = (1 if sh["k"] == "E" else 0) + sum(c["ne"] for c in sh["c"])


def walk(sh, path=()):
    """(path, node) in C64KChk.paths order (depth first, children by index)"""
    yield path, sh
    for i, c in enumerate(sh["c"]):
        yield from walk(c, path + (i,))


def lazy_bad(tubes):
    """tubes failing the end-point part of C64KChk.tsLazyOK (q0 < q1 <= 2^EQ): those stay eager"""
    return sum(1 for q0, q1 in tubes if not (G.grid(q0, EQ) < G.grid(q1, EQ) <= TWO_EQ))


def pl(path):
    return "[" + ", ".join(map(str, path)) + "]"


# ---- cost model: estimated kernel seconds per theorem at full machine load (lazy t-pieces); peak GB per theorem ----
HEAD_S = {0: 9.0, 1: 21.0, 2: 40.0}
CTX_S = {0: 3.0, 1: 6.0, 2: 10.0}
REC_H = {0: 0.35, 1: 3.4, 2: 4.0}
E_LEAF_S, E_LEAF_EAGER_S, LOC_S = 10.5, 22.0, 0.3
DATA_GB = 3.0                            # elaboration of the data term
GB_BASE, GB_PER_S = 1.5, 0.12        # peak RSS of a theorem from its estimated seconds


def tget(d, t):
    return d[t] if t in d else d[2] * (1 + 0.5 * (t - 2))


def peak_gb(s):
    return GB_BASE + GB_PER_S * s


def load_hints(path):
    """the hints of a module: DIR/<M>.hb and the pieces DIR/<M>__<k>.hb of a split hint pass"""
    hs, fails = {}, 0
    if not path:
        return hs, fails
    import glob as _glob
    for f in sorted([path] + _glob.glob(_glob.escape(path[:-3]) + "__*.hb")):
        if not os.path.exists(f):
            continue
        for line in open(f, errors="replace"):
            if line.startswith("HB "):
                _, p, j, x = line.split()
                hs[(p, int(j))] = x
            elif line.startswith("HBFAIL"):
                fails += 1
    return hs, fails


class AllHints(dict):
    """cost mode: every step counts as hinted"""
    def get(self, k, d=None):
        return "0"


HDR_K = ("import C64Core.Nest\nimport C64Core.Load\nimport C64NData.Glob\nimport C64K.KHintGlue\nimport C64K.KCoverL\n\n"
         "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\nopen C64Chk\n\n")
HDR_KD = "import C64K.KHintGlue\nimport C64K.KCoverL\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\nopen C64Chk\n\n"


class ModuleK:
    """the units of one K module: (unit literal, [(theorem source, est s)], proof term)"""
    def __init__(self, name, root_sh, head, tl, bl, args, node, hints, seg, esub, is_arc, seg2=None, seg0=None):
        self.name, self.head, self.tl, self.bl, self.args, self.node, self.is_arc = name, head, tl, bl, args, node, is_arc
        annotate(root_sh)
        self.units = []
        self.stats = {"W": 0, "W_steps": 0, "seg_h": 0, "seg_p": 0, "sub": 0, "sub_leaves": 0, "loc": 0, "ts_fail": 0,
                      "E_eager": 0, "paths": sum(1 for _ in walk(root_sh))}
        self.seg2 = seg2 or seg
        self.seg0 = seg0 or seg
        self._pick(root_sh, (), hints, seg, esub)

    def st_part(self, p):
        return (f"(C64KChk.arcCtx C64NData.glob.g {self.head}).any (fun A => C64KChk.partOK C64NData.glob A {pl(p)} "
                f"{self.tl} {self.bl} {self.node}) = true")

    def st_head(self, p):
        return (f"(C64KChk.arcCtx C64NData.glob.g {self.head}).any (fun A => C64KChk.headAt C64NData.glob A {pl(p)} "
                f"{self.tl} {self.bl} {self.node}) = true")

    def st_leaf(self, p, f_):
        return f"C64KChk.leafAny C64NData.glob {self.head} {pl(p)} {self.tl} {self.bl} {self.node} ({f_}) = true"

    def _pick(self, sh, path, hints, seg, esub):
        if not sh["hasW"] and 1 <= sh["ne"] <= esub:
            u = len(self.units)
            leaves = [x for _, x in walk(sh) if x["k"] == "E"]
            nbad = sum(1 for x in leaves if lazy_bad(x["tubes"]) > 0)
            self.stats["ts_fail"] += sum(lazy_bad(x["tubes"]) for x in leaves)
            self.stats["E_eager"] += nbad
            est = (len(leaves) - nbad) * E_LEAF_S + nbad * E_LEAF_EAGER_S
            thm = (f"-- subtree {pl(path)}: {sh['ne']} empty leaves\ntheorem kb{u} : C64KChk.unitAny C64NData.glob "
                   f"{self.head} {self.tl} {self.bl} {self.node} (.sub {pl(path)}) = true := by\n  decide +kernel\n")
            self.units.append((f".sub {pl(path)}", [(thm, est)], f"kb{u}"))
            self.stats["sub"] += 1; self.stats["sub_leaves"] += sh["ne"]
            return
        u = len(self.units)
        if sh["k"] == "W":
            t = len(sh["tubes"]); T = sh["n"] + sh["h"]
            self.stats["W"] += 1; self.stats["W_steps"] += T
            self.stats["ts_fail"] += lazy_bad(sh["tubes"])
            key = pl(path).replace(" ", "")
            thms = [(f"-- W leaf {pl(path)}: {sh['n']} records, {sh['h']} hard arcs, {t} tubes\ntheorem kh{u} : "
                     f"{self.st_head(path)} := by\n  decide +kernel\n", tget(HEAD_S, t))]
            segs = []
            sg = self.seg0 if t == 0 else (seg if t == 1 else self.seg2)
            for i, J in enumerate(range(0, T, sg)):
                L = min(sg, T - J)
                hs = [hints.get((key, j)) for j in range(J, J + L)]
                plain = self.st_leaf(path, f"C64KChk.segF C64NData.glob {J} {L}")
                if all(h is not None for h in hs):
                    hl = ", ".join(f"C64KChk.hb 0x{h}" for h in hs)
                    thms.append((f"theorem ks{u}_{i}h : {self.st_leaf(path, f'C64KChk.segFT C64NData.glob {J} [{hl}]')} := by\n"
                                 f"  decide +kernel\n\ntheorem ks{u}_{i} : {plain} :=\n  C64KChk.segF_of_segFT_len ks{u}_{i}h rfl\n",
                                 tget(CTX_S, t) + L * tget(REC_H, t) + 0.1))
                    self.stats["seg_h"] += 1
                else:
                    thms.append((f"theorem ks{u}_{i} : {plain} := by\n  decide +kernel\n",
                                 tget(CTX_S, t) + 2 * L * tget(REC_H, t)))
                    self.stats["seg_p"] += 1
                segs.append(f"ks{u}_{i}")
            thms.append((f"theorem kr{u} : {self.st_leaf(path, f'C64KChk.restF C64NData.glob {T}')} := by\n  decide +kernel\n",
                         tget(CTX_S, t)))
            term = f"kr{u}"
            for s in reversed(segs):
                term = f"(C64KChk.rest_of_seg {s} {term})"
            self.units.append((f".loc {pl(path)}", thms, f"C64KChk.unitAny_loc_of (C64KChk.partAny_wit_of kh{u} {term})"))
        else:
            if sh["k"] == "E":
                bad = lazy_bad(sh["tubes"])
                self.stats["ts_fail"] += bad
                est = E_LEAF_S if bad == 0 else E_LEAF_EAGER_S
            else:
                est = LOC_S
            thm = f"theorem kl{u} : {self.st_part(path)} := by\n  decide +kernel\n"
            self.units.append((f".loc {pl(path)}", [(thm, est)], f"C64KChk.unitAny_loc_of kl{u}"))
            self.stats["loc"] += 1
        for i, c in enumerate(sh["c"]):
            self._pick(c, path + (i,), hints, seg, esub)

    def assembly(self, s0, s1, sc, pins, Rs, chunk):
        """[(source, est s)]: hh, hd, the linear cover check, the unit facts per chunk, okK"""
        U = [u[0] for u in self.units]
        chunks = [list(range(k, min(k + chunk, len(U)))) for k in range(0, len(U), chunk)]
        lits = ["[" + ", ".join(U[i] for i in ch) + "]" for ch in chunks]
        ulist = lits[-1]
        for lt in reversed(lits[:-1]):
            ulist = f"{lt} ++ ({ulist})"
        fuel = len(U) + 1
        ua = f"C64KChk.unitAny C64NData.glob {self.head} {self.tl} {self.bl} {self.node} u = true"
        out = [(f"theorem khh : C64KChk.hHead C64NData.glob.g {s0} {s1} {sc} {pins} {Rs} = true := by\n  decide +kernel\n", 1.0),
               (f"theorem khd : Nat.blt (C64KChk.depth {self.node}) C64NData.glob.fuel = true := by\n  decide +kernel\n", 1.0),
               (f"theorem khc : C64KChk.covL {fuel} (C64KChk.paths {self.node}) ({ulist}) = true := by\n  decide +kernel\n",
                1.0 + 0.002 * self.stats["paths"])]
        for g, (ch, lt) in enumerate(zip(chunks, lits)):
            chain = "fun _ h => nomatch h"
            for i in reversed(ch):
                chain = f"List.forall_mem_cons.2 ⟨{self.units[i][2]}, {chain}⟩"
            out.append((f"theorem kc{g} : ∀ u ∈ ({lt} : List C64KChk.KUnit), {ua} :=\n  {chain}\n", 0.2))
        hus = f"kc{len(chunks) - 1}"
        for g in reversed(range(len(chunks) - 1)):
            hus = f"List.forall_mem_append.2 ⟨kc{g}, {hus}⟩"
        cov = f"C64KChk.checkSubNK_of_coverL ({ulist}) {fuel} khh khd (List.cons_ne_nil _ _) khc\n    ({hus})"
        if self.is_arc:
            out.append((f"theorem okK : C64KChk.checkArcNK C64NData.glob arc = true := by\n  rw [karc_eq]\n  exact {cov}\n", 1.0))
        else:
            out.append((f"theorem okK : C64KChk.checkSubNK C64NData.glob {self.args} {self.node} = true :=\n  {cov}\n", 1.0))
        return out


def module_files(mod, asm, root, ns, data_src, data_s, split_s):
    """[(file base, source, est_s, est_gb, deps)] for one module: the data module, or the data module + KD unit files
    (independent of each other, theorems grouped up to split_s) + a last KD file with the assembly only"""
    thms_all = [th for u in mod.units for th in u[1]]
    total = data_s + sum(s for _, s in thms_all) + sum(s for _, s in asm)
    if total <= split_s:
        body = "".join(src + "\n" for src, _ in thms_all) + "\n".join(src for src, _ in asm)
        worst = max([s for _, s in thms_all] + [s for _, s in asm])
        return [(mod.name, data_src + body + f"\nend {ns}\n", total, max(DATA_GB, peak_gb(worst)), [])]
    groups, cur, acc = [], [], 0.0
    for th in thms_all:
        if cur and acc + th[1] > split_s:
            groups.append(cur); cur, acc = [], 0.0
        cur.append(th); acc += th[1]
    groups.append(cur)
    out = [(mod.name, data_src + f"\nend {ns}\n", data_s, DATA_GB, [])]
    for gi, grp in enumerate(groups, 1):
        body = "".join(src + "\n" for src, _ in grp)
        out.append((f"KD_{mod.name}_{gi}", f"import {root}.{mod.name}\n" + HDR_KD + f"namespace {ns}\n\n" + body + f"\nend {ns}\n",
                    5.0 + sum(s for _, s in grp), peak_gb(max(s for _, s in grp)), [mod.name]))
    prev = [f"KD_{mod.name}_{k}" for k in range(1, len(groups) + 1)]
    imps = f"import {root}.{mod.name}\n" + "".join(f"import {root}.{p}\n" for p in prev)
    body = "".join(src + "\n" for src, _ in asm)
    out.append((f"KD_{mod.name}_{len(groups) + 1}", imps + HDR_KD + f"namespace {ns}\n\n" + body + f"\nend {ns}\n",
                5.0 + sum(s for _, s in asm), peak_gb(max(s for _, s in asm)), [mod.name] + prev))
    return out


def n_seconds(ntimes, m):
    if not ntimes:
        return 0.0
    p = os.path.join(ntimes, f"{m}.log")
    if os.path.exists(p):
        mm = re.search(r"OK (\d+)", open(p).read())
        if mm:
            return int(mm.group(1)) / 1000.0
    return 0.0


def emit(args, root, d, nm, files, stats, manifest, jobs, costs, tot):
    est = sum(f[2] for f in files)
    costs.append([nm, round(est, 1), round(max(f[3] for f in files), 1)])
    if args.mode == "k":
        for fn, src, s, gb, deps in files:
            open(os.path.join(d, f"{fn}.lean"), "w").write(src)
            jobs.append([fn, ",".join(deps) if deps else "-", f"{gb:.1f}", f"{s:.0f}", f"{root}/{fn}.lean", f"{root}/{fn}.olean"])
        manifest[nm] = {"files": [f[0] for f in files], "okK_in": f"{root}.{files[-1][0]}",
                        "est_s": round(est, 1), "est_gb": round(max(f[3] for f in files), 1), **stats}
    tot["modules"] += 1; tot["files"] += len(files); tot["split"] += len(files) > 1; tot["est_s"] += est
    for k2 in ("W", "W_steps", "seg_h", "seg_p", "sub", "sub_leaves", "loc", "ts_fail", "E_eager"):
        tot[k2] = tot.get(k2, 0) + stats.get(k2, 0)


def cmd(args):
    C = G.load_cert(args.cert)
    ctx = G.Ctx(C["tau"], C["T1"], C["tiles"], C.get("iv_eps", "1/1000000000"))
    arcs = sorted(C["arcs"], key=lambda x: F(x["s0"]))
    if args.upper:
        arcs = [a for a in arcs if F(a["s1"]) <= F(1, 2)]
    root = args.root
    only = set(x for x in args.only.split(",") if x)
    d = os.path.join(args.out, root if args.mode == "k" else "hg")
    if args.mode != "cost":
        os.makedirs(d, exist_ok=True)
    if args.mode == "k" and root == "C64NData":
        open(os.path.join(d, "Glob.lean"), "w").write(
            "import C64Core.Nest\nimport C64Core.Load\n\nset_option maxRecDepth 100000\n\nopen C64Chk\n\nnamespace C64NData\n\n"
            f"def glob : GlobN := {ctx.glob_term()}\n\nend C64NData\n")
    index, manifest, jobs, costs = [], {}, [], []
    hg_order = []  # hg mode: (W steps, file name) of every hint-pass file
    tot = {"modules": 0, "files": 0, "split": 0, "est_s": 0.0}
    for i0 in range(len(arcs)):
        a = arcs[i0]
        i = i0 + args.index_offset
        _ENCS.clear()
        term, subs, rkids = G.arc_term(ctx, a, args.max_recs)
        enc = _ENCS[-1] if _ENCS else None
        assert enc is None or len(enc.subs) == len(enc.sub_nodes) == len(subs)
        A = f"A{i:04d}"
        mods = []      # (name, kind, shape, head, tl, bl, args, node, (s0, s1, sc, pins, Rs), data term)
        if a["type"] != "E":
            s0, s1, sc, pins, Rs, m = G.arc_head(a)
            rX = ctx.rad(a["s0"], a["s1"], a["sc"], ctx.tau)
            bl0 = "[" + ", ".join("(0, 0, 0)" for _ in range(m)) + "]"
            mods.append((A, "arc", shape(enc, enc.arc["tree"], [], top=True), f"{s0} {s1} {sc} {pins} {Rs} {rX}", "[]", bl0,
                         None, "knode", (s0, s1, sc, pins, Rs), term))
        sinfo = []
        for j, (tubes, boxes, sterm, nrec, kids) in enumerate(subs):
            args_s, t = G.sub_stmt(ctx, a, tubes, boxes, sterm)
            nm = f"{A}S{j:03d}"
            tl, bl = G.ctx_terms(ctx, tubes, boxes)
            sinfo.append({"name": nm, "args": args_s, "tubes": tl, "boxes": bl, "kids": [f"{A}S{k:03d}" for k in kids]})
            s0, s1, sc, pins, Rs, m = G.arc_head(a)
            mods.append((nm, "sub", shape(enc, enc.sub_nodes[j], tubes, top=True), args_s[: -len(" " + tl + " " + bl)], tl, bl,
                         args_s, "node", (s0, s1, sc, pins, Rs), t))
        s0_, s1_, sc_, pins_, Rs_, m_ = G.arc_head(a) if a["type"] != "E" else (0, 0, 0, "[]", "[]", 0)
        index.append({"arc": i, "name": A, "type": a["type"], "subs": sinfo, "kids": [f"{A}S{k:03d}" for k in rkids],
                      "boxes0": "[" + ", ".join("(0, 0, 0)" for _ in range(m_)) + "]",
                      "recs": G.count_recs(a["tree"]) if "tree" in a else 0})
        if args.mode == "hg":
            for (nm, kind, sh, head, tl, bl, args_s, node, asm, t) in mods:
                if only and nm not in only:
                    continue
                wp = [(p, x["n"] + x["h"]) for p, x in walk(sh) if x["k"] == "W"]
                if not wp:
                    continue
                nd = (f"(match C64NData.{nm}.arc with | .N _ _ _ _ _ _ t => t | .old _ => .ext)" if kind == "arc"
                      else f"C64NData.{nm}.node")
                groups, cur, acc = [], [], 0
                for p, T in wp:                  # W paths in groups of at most --hg-steps steps: one lean process each
                    if cur and acc + T > args.hg_steps:
                        groups.append((cur, acc)); cur, acc = [], 0
                    cur.append(p); acc += T
                groups.append((cur, acc))
                for gi, (grp, gsteps) in enumerate(groups, 1):
                    body = "".join(
                        f"open C64Chk in\n#eval show IO Unit from do\n  let gn := C64NData.glob\n"
                        f"  let some A := C64KChk.arcCtx gn.g {head} | IO.println \"HBFAIL {pl(p).replace(' ', '')} -1 noarcctx\"\n"
                        f"  C64KChk.hgPath gn A {tl} {bl} {nd} {pl(p)}\n" for p in grp)
                    fn = f"HG_{nm}.lean" if len(groups) == 1 else f"HG_{nm}__{gi}.lean"
                    hg_order.append((gsteps, fn))
                    open(os.path.join(d, fn), "w").write(
                        f"import C64NData.{nm}\nimport C64KX.HintGen\n\n" + body + f"\n#eval IO.println \"HBDONE {nm} {gi} {len(grp)}\"\n")
            continue
        if a["type"] == "E":
            if not (only and A not in only):
                ns = f"{root}.{A}"
                src = (HDR_K + f"namespace {ns}\n\n-- arc {i}: type E\nnoncomputable def arc : ArcN := {term}\n\n"
                       f"theorem okK : C64KChk.checkArcNK C64NData.glob arc = true := by\n  decide +kernel\n\nend {ns}\n")
                emit(args, root, d, A, [(A, src, 5.0, peak_gb(5.0), [])], {"kind": "old"}, manifest, jobs, costs, tot)
            continue
        for (nm, kind, sh, head, tl, bl, args_s, node, asm, t) in mods:
            if only and nm not in only:
                continue
            if args.mode == "cost":
                hints, hfail = AllHints(), 0
            else:
                hints, hfail = load_hints(os.path.join(args.hints, f"{nm}.hb") if args.hints else None)
            mod = ModuleK(nm, sh, head, tl, bl, args_s, node, hints, args.seg, args.esub, kind == "arc", seg2=args.seg2,
                          seg0=args.seg0)
            ns = f"{root}.{nm}"
            data_s = 3.0 + 0.3 * n_seconds(args.ntimes, nm)
            if kind == "arc":
                s0, s1, sc, pins, Rs = asm
                rX = head.split()[-1]
                data = (HDR_K + f"namespace {ns}\n\n-- arc {i}: type {a['type']}, s0 = {a['s0']}, s1 = {a['s1']}\n"
                        f"noncomputable def arc : ArcN := {term}\n\n"
                        f"/-- The tree of the arc. -/\nnoncomputable def knode : NTree := match arc with\n"
                        f"  | .N _ _ _ _ _ _ t => t\n  | .old _ => .ext\n\n"
                        f"theorem karc_eq : arc = .N {s0} {s1} {sc} {pins} {Rs} {rX} knode := rfl\n\n")
            else:
                j = int(nm[-3:])
                data = (HDR_K + f"namespace {ns}\n\n-- subtree {j} of arc {i} ({subs[j][3]} records)\n"
                        f"noncomputable def node : NTree := {t}\n\n")
            files = module_files(mod, mod.assembly(*asm, args.chunk), root, ns, data, data_s, args.split_s)
            emit(args, root, d, nm, files, {"kind": kind, "hint_fail": hfail, **mod.stats}, manifest, jobs, costs, tot)
    if args.mode == "hg":
        hg_order.sort(key=lambda x: (-x[0], x[1]))   # longest first (the hint pass runs them in this order)
        with open(os.path.join(d, "ORDER"), "w") as f:
            f.write("".join(fn + "\n" for _, fn in hg_order))
        print("hg files written for part offset", args.index_offset, json.dumps(
            {"files": len(hg_order), "W_steps": sum(x[0] for x in hg_order), "max_file_steps": max((x[0] for x in hg_order), default=0)}))
        return
    tot["est_s"] = round(tot["est_s"], 1)
    if args.mode == "cost":
        print(json.dumps({"part": args.index_offset, "est_s": tot["est_s"], "modules": costs, "tot": tot}))
        return
    json.dump(index, open(os.path.join(d, "index.json"), "w"))
    with open(os.path.join(d, f"manifest_{args.part_id or args.index_offset}.json"), "w") as f:
        json.dump(manifest, f, indent=0, sort_keys=True)
    with open(os.path.join(args.out, "jobs.tsv"), "w") as f:
        for row in jobs:
            f.write("\t".join(row) + "\n")
    print("K modules", json.dumps(tot, sort_keys=True))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["hg", "k", "cost"]); ap.add_argument("cert"); ap.add_argument("out")
    ap.add_argument("--max-recs", type=int, default=20000); ap.add_argument("--upper", action="store_true")
    ap.add_argument("--index-offset", type=int, default=0)
    ap.add_argument("--hints", default=""); ap.add_argument("--seg", type=int, default=20, help="segment steps for 1-tube W leaves")
    ap.add_argument("--seg0", type=int, default=80, help="segment steps for 0-tube W leaves")
    ap.add_argument("--seg2", type=int, default=20, help="segment steps for W leaves with >= 2 tubes")
    ap.add_argument("--esub", type=int, default=8); ap.add_argument("--split-s", type=float, default=28800.0)
    ap.add_argument("--chunk", type=int, default=64)
    ap.add_argument("--root", default="C64NData")
    ap.add_argument("--only", default="", help="comma list: write files only for these modules (the index stays complete)")
    ap.add_argument("--ntimes", default="")
    ap.add_argument("--pyflint", default="")
    ap.add_argument("--part-id", default="", help="part id as in the cert file name (manifest_<id>.json)")
    ap.add_argument("--hg-steps", type=int, default=1000,
                    help="hg mode: W steps per hint-pass file (one lean process each; a longer single path keeps its own file)")
    cmd(ap.parse_args())


if __name__ == "__main__":
    main()
