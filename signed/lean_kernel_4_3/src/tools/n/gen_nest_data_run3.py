#!/usr/bin/env python3
"""Export NESTED certificates (6.4, variant Cp, format of check_nested.py) to Lean data for the checker C64Core.Nest.

Nothing in the output is trusted by the proofs; the exporter only re-encodes:
  * s (arcs of T1) as integers over 2^ES, q (tile arcs, hard arcs, ivsplit points) as integers over 2^EQ; the points
    q_r of the representatives stay rationals;
  * the multipliers of a W1 record (u, v, y_1..y_m, vt_1..vt_K) and of an empty leaf (v, y_1..y_m, vt_1..vt_K) are
    scaled by the least common multiple of their denominators (the conditions are positively homogeneous in them);
  * W1 records: one natural number per W leaf, length-prefixed fields (q1, u, v, y_j, vt_k) in the order of the tile
    arcs; the hard arcs and the leaf header are Lean terms;
  * rX: the crossing radius of the generator (arb, 80 bits) for the leaf's tau_N, proposed to the checker, which uses
    max(its own proved radius, rX).
Module mode splits large arcs below the arc: a subtree with more than --max-recs W1 records below one hard arc (or
ivsplit/split child) becomes its own module (`checkSubN ... = true`), and the parent holds `.ext` there.

Usage:
  gen_nest_data_run3.py modules CERT.json[.gz] OUTDIR [--max-recs N] [--range a:b] [--upper] [--index-offset K]
     (--index-offset: module names use arc index i + K; for one part file of the upper half, K = the part number)
     (--upper: only the arcs in [0, 1/2]; the lower half is their mirror, see gen_main_nest.py --mirror)
  gen_nest_data.py sample CFG.json PHASEA_DIR 'PHASEB_GLOB' OUTDIR --n-sub K --n-arc J --n-root R [--seed S]
     (validation without the assembled certificate: phase-B subtrees in the context of their arc and stub;
      writes Test.lean and jobs.json for the reference checker)
"""
import argparse, glob, gzip, json, os, random, sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_lean_data import BW, qlit, scale, r_ship     # noqa: E402

P, NT, KT, D, DE, DT, DW, ES, EQ = 80, 18, 3, 23, 8, 12, 30, 13, 30   # run3: dT 7 -> 12 (run 2 failed ~0.1% of modules with 7; 9 fixes the tested ones)
LS, DS, LT, NL, FUEL = 6, 4, 2, 7, 400       # run3: nL 3 -> 7 (run 1 failed 0.7% with 3; 6 fixes the tested ones), dS 2 -> 4 (margin)


def grid(x, E):
    v = F(x) * 2 ** E
    assert v.denominator == 1, (x, E)
    return int(v)


class Ctx:
    """per-certificate encoding context: tau, T1, tiles, iv_eps, radius cache."""
    def __init__(self, tau, T1, tiles, iv_eps):
        self.tau = F(tau)
        c, a, b = (F(x) for x in T1)
        self.T1 = (c, F(0), a, b)
        self.T1raw = T1
        self.tiles = tiles
        self.tile_names = sorted(tiles)
        self.tile_idx = {k: i for i, k in enumerate(self.tile_names)}
        self.iv_eps = F(iv_eps)
        self.rcache = {}

    def rad(self, s0, s1, sc, tw):
        key = (F(s0), F(s1), F(sc), F(tw))
        if key not in self.rcache:
            self.rcache[key] = r_ship(self.T1, key[0], key[1], key[2], key[3])
        return self.rcache[key]

    def glob_term(self):
        c, a, b = self.T1raw
        tiles = "[" + ", ".join("(" + ", ".join(qlit(x) for x in self.tiles[k]) + ")" for k in self.tile_names) + "]"
        g = (f"{{ P := {P}, n := {NT}, k := {KT}, D := {D}, dE := {DE}, dT := {DT}, dW := {DW}, ES := {ES}, "
             f"EQ := {EQ}, tau := {qlit(self.tau)}, c := {qlit(c)}, a := {qlit(a)}, b := {qlit(b)}, tiles := {tiles} }}")
        return (f"{{ g := {g}, eps := {qlit(self.iv_eps)}, lS := {LS}, dS := {DS}, lT := {LT}, nL := {NL}, fuel := {FUEL} }}")


def atoms_term(ts, ms):
    assert len(ts) == len(ms)
    return "[" + ", ".join(f"({qlit(t)}, {qlit(m)})" for t, m in zip(ts, ms)) + "]"


def tube_term(ctx, tb):
    """tb = (tile name, q0, q1, ts, ms)"""
    nm, q0, q1, ts, ms = tb
    return f"⟨{ctx.tile_idx[nm]}, {grid(q0, EQ)}, {grid(q1, EQ)}, {atoms_term(ts, ms)}⟩"


def count_recs(node):
    if "ivsplit" in node or "split" in node:
        return sum(count_recs(k) for k in node["kids"])
    if node["type"] == "W":
        return sum(count_recs(a["child"]) if isinstance(a, dict) else 1 for a in node["tile_arcs"])
    return 1


EMPTY_COST = 3   # an empty leaf costs about 3 W1 records (native timings: ~100 ms vs ~35 ms)


def own_cost(node):
    """the work of a node without its children: W1 records, or EMPTY_COST for an empty leaf"""
    if "ivsplit" in node or "split" in node:
        return 0
    if node["type"] == "empty":
        return EMPTY_COST
    return sum(1 for a in node["tile_arcs"] if not isinstance(a, dict))


def children(node):
    if "ivsplit" in node or "split" in node:
        return node["kids"]
    if node.get("type") == "W":
        return [a["child"] for a in node["tile_arcs"] if isinstance(a, dict)]
    return []


def plan(node, max_cost, ext):
    """post-order: the cost of a node with its subtrees inline, after moving the largest inline children to their own
    modules (ids added to `ext`) until the inline cost is at most max_cost (a node's own records always stay)"""
    sizes = [(plan(k, max_cost, ext), k) for k in children(node)]
    total = own_cost(node) + sum(sz for sz, _ in sizes)
    for sz, k in sorted(sizes, key=lambda x: -x[0]):
        if total <= max_cost:
            break
        ext.add(id(k))
        total -= sz
    return total


class Enc:
    """encodes the trees of one rooted arc; with max_recs, the subtrees chosen by `plan` (each module's inline cost at
    most max_recs, records + EMPTY_COST per empty leaf) go to `subs` (contexts + terms)."""
    def __init__(self, ctx, arc, m, max_recs=None):
        self.ctx, self.arc, self.m, self.max_recs = ctx, arc, m, max_recs
        self.subs = []          # (tubes, boxes, term, nrecs, child sub indices)
        self.cur = []           # sub indices of the ext nodes of the module being written (in extList order)
        self.ext = set()        # ids of the nodes that become modules
        if max_recs is not None and "tree" in arc:
            plan(arc["tree"], max_recs, self.ext)

    def rx(self, tw):
        a = self.arc
        return self.ctx.rad(a["s0"], a["s1"], a["sc"], tw)

    def empty(self, node, K):
        tw = node.get("tau_rep", str(self.ctx.tau))
        ys = node["y"]
        assert len(ys) == self.m and len(node.get("vt", [])) == K, "empty leaf: multiplier count"
        w = BW()
        for x in scale(list(node["v"]) + [c for y in ys for c in y] + [c for y in node.get("vt", []) for c in y]):
            w.int(x)
        return f"(.empty {qlit(tw)} {self.rx(tw)} ({w.lit()}))"

    def wit(self, node, tubes, boxes):
        K = len(tubes)
        tw = node.get("tau_rep", str(self.ctx.tau))
        mus = node.get("mus", [])
        assert len(mus) == K, "W leaf: mus count"
        mus_t = []
        for x, tb in zip(mus, tubes):
            assert isinstance(x, list) and len(x) == 2, "interval tube needs [q_r, mu_r]"
            mus_t.append(f"({qlit(x[0])}, {qlit(x[1])})")
        hdr = (f"⟨{self.ctx.tile_idx[node['tile']]}, {qlit(tw)}, {self.rx(tw)}, {qlit(node['sigma'])}, "
               f"{atoms_term(node['wrep_t'], node['wrep_m'])}, [{', '.join(mus_t)}]⟩")
        items = sorted(node["tile_arcs"], key=lambda a: F(a["hard"][0]) if isinstance(a, dict) else F(a[0]))
        w = BW(); n = 0; hards = []; kids = []
        for a in items:
            if isinstance(a, dict):
                kind = a.get("kind", "disc")
                assert kind == "iv", "only interval tubes are supported (kind %r)" % kind
                q0, q1 = a["hard"]
                hards.append(f"({grid(q0, EQ)}, {grid(q1, EQ)})")
                nt = (node["tile"], F(q0), F(q1), node["wrep_t"], node["wrep_m"])
                kids.append(self.tree(a["child"], tubes + [nt], boxes))
            else:
                assert len(a) == 6 + 2 * self.m + 2 * K, "W1 record length"
                w.nat(grid(a[1], EQ))
                for x in scale(a[2:]):
                    w.int(x)
                n += 1
        dat = w.lit() if n else "0"
        return f"(.wit {hdr} {n} ({dat}) [{', '.join(hards)}] [{', '.join(kids)}])"

    def tree(self, node, tubes, boxes, top=False):
        if not top and id(node) in self.ext:
            saved, self.cur = self.cur, []
            term = self.tree(node, tubes, boxes, top=True)
            kids, self.cur = self.cur, saved
            self.subs.append((list(tubes), list(boxes), term, count_recs(node), kids))
            self.cur.append(len(self.subs) - 1)
            return ".ext"
        if "ivsplit" in node:
            k = node["ivsplit"]
            nm, q0, q1, ts, ms = tubes[k]
            qm = F(node["at"])
            lo = list(tubes); lo[k] = (nm, q0, qm, ts, ms)
            hi = list(tubes); hi[k] = (nm, qm, q1, ts, ms)
            a, b = node["kids"]
            return f"(.ivsplit {k} {grid(qm, EQ)} {self.tree(a, lo, boxes)} {self.tree(b, hi, boxes)})"
        if "split" in node:
            j = node["split"]
            kids = []
            for i, kd in enumerate(node["kids"]):
                b2 = list(boxes); d, ii, kk = b2[j]; b2[j] = (d + 1, 2 * ii + i % 2, 2 * kk + i // 2)
                kids.append(self.tree(kd, tubes, b2))
            return f"(.split {j} " + " ".join(kids) + ")"
        if node["type"] == "empty":
            return self.empty(node, len(tubes))
        assert node["type"] == "W"
        return self.wit(node, tubes, boxes)


def arc_head(arc):
    s0, s1, sc = grid(arc["s0"], ES), grid(arc["s1"], ES), grid(arc["sc"], ES)
    pcs = arc.get("pcs", [])
    pins = "[" + ", ".join(f"({qlit(p[0])}, {qlit(p[1])})" for p in pcs) + "]"
    Rs = "[" + ", ".join(qlit(R) for R in arc.get("Rs", [])) + "]"
    return s0, s1, sc, pins, Rs, len(pcs)


def arc_term(ctx, arc, max_recs=None):
    """(Lean term of type ArcN, list of subtrees) for an arc of the nested certificate."""
    if arc["type"] == "E":
        ur, ui = scale(arc["u"])
        return f".old (.E {grid(arc['s0'], ES)} {grid(arc['s1'], ES)} {ur if ur >= 0 else f'({ur})'} " \
               f"{ui if ui >= 0 else f'({ui})'})", [], []
    if arc["type"] == "H":
        arc = dict(arc, pcs=[], Rs=[], tree={"boxes": [], "type": "W", "tile": arc["tile"],
                                              "tile_arcs": arc["tile_arcs"], "wrep_t": arc["wrep_t"],
                                              "wrep_m": arc["wrep_m"], "sigma": arc["sigma"]})
    s0, s1, sc, pins, Rs, m = arc_head(arc)
    enc = Enc(ctx, arc, m, max_recs)
    boxes = [(0, 0, 0)] * m
    t = enc.tree(arc["tree"], [], boxes, top=True)
    rX = ctx.rad(arc["s0"], arc["s1"], arc["sc"], ctx.tau)
    return f".N {s0} {s1} {sc} {pins} {Rs} {rX} {t}", enc.subs, enc.cur


def ctx_terms(ctx, tubes, boxes):
    tl = "[" + ", ".join(tube_term(ctx, tb) for tb in tubes) + "]"
    bl = "[" + ", ".join(f"({d}, {i}, {k})" for d, i, k in boxes) + "]"
    return tl, bl


def sub_stmt(ctx, arc, tubes, boxes, term):
    s0, s1, sc, pins, Rs, m = arc_head(arc)
    rX = ctx.rad(arc["s0"], arc["s1"], arc["sc"], ctx.tau)
    tl, bl = ctx_terms(ctx, tubes, boxes)
    return f"{s0} {s1} {sc} {pins} {Rs} {rX} {tl} {bl}", term


HEADER = "import C64Core.Nest\nimport C64Core.Load\n\nset_option maxRecDepth 100000\n\nopen C64Chk\n\n"
TESTHDR = ("set_option compiler.extract_closed false\n\n"
           "@[noinline] def runSub (gn : GlobN) (s0 s1 sc : Nat) (pins : List (Q × Q)) (Rs : List Q) (rX : Nat) "
           "(tubes : List TubeD) (bx : List (Nat × Nat × Nat)) (t : NTree) : IO Bool :=\n"
           "  pure (checkSubN gn s0 s1 sc pins Rs rX tubes bx t)\n\n"
           "@[noinline] def runArc (gn : GlobN) (a : ArcN) : IO Bool := pure (checkArcN gn a)\n\n")


def eval_block(name, call, label):
    return (f"#eval show IO Unit from do\n  let t0 ← IO.monoMsNow\n  let r ← {call}\n"
            f"  IO.println s!\"{label} {{r}} {{(← IO.monoMsNow) - t0}} ms\"\n\n")


def load_cert(path):
    C = json.load(gzip.open(path, "rt") if path.endswith(".gz") else open(path))
    assert C.get("variant") == "Cp"
    return C


def cmd_modules(args):
    C = load_cert(args.cert)
    ctx = Ctx(C["tau"], C["T1"], C["tiles"], C.get("iv_eps", "1/1000000000"))
    arcs = sorted(C["arcs"], key=lambda x: F(x["s0"]))
    if args.upper:            # the lower half is the mirror of the upper half (C64Chk.main_of_checksN_mirror)
        arcs = [a for a in arcs if F(a["s1"]) <= F(1, 2)]
    d = os.path.join(args.out, "C64NData"); os.makedirs(d, exist_ok=True)
    hdr = HEADER.replace("import C64Core.Load\n", "import C64Core.Load\nimport C64NData.Glob\n", 1)
    open(os.path.join(d, "Glob.lean"), "w").write(
        HEADER + "namespace C64NData\n\n" + f"def glob : GlobN := {ctx.glob_term()}\n\n"
        "theorem globOK : checkGlobN glob = true := by native_decide\n\nend C64NData\n")
    rng = range(len(arcs)) if not args.range else range(*[int(x) for x in args.range.split(":")])
    index = []
    for i0 in rng:
        a = arcs[i0]
        i = i0 + args.index_offset       # global arc index (a part file holds arc p of the upper half as its arc 0)
        term, subs, rkids = arc_term(ctx, a, args.max_recs)
        src = hdr + (f"namespace C64NData.A{i:04d}\n\n-- arc {i}: type {a['type']}, s0 = {a['s0']}, s1 = {a['s1']}\n"
                     f"def arc : ArcN := {term}\n\n"
                     f"theorem ok : checkArcN C64NData.glob arc = true := by native_decide\n\nend C64NData.A{i:04d}\n")
        open(os.path.join(d, f"A{i:04d}.lean"), "w").write(src)
        sinfo = []
        for j, (tubes, boxes, sterm, nrec, kids) in enumerate(subs):
            args_s, t = sub_stmt(ctx, a, tubes, boxes, sterm)
            nm = f"A{i:04d}S{j:03d}"
            tl, bl = ctx_terms(ctx, tubes, boxes)
            sinfo.append({"name": nm, "args": args_s, "tubes": tl, "boxes": bl, "kids": [f"A{i:04d}S{k:03d}" for k in kids]})
            src = hdr + (f"namespace C64NData.{nm}\n\n-- subtree {j} of arc {i} ({nrec} records)\n"
                         f"def node : NTree := {t}\n\n"
                         f"theorem ok : checkSubN C64NData.glob {args_s} node = true := by native_decide\n\n"
                         f"end C64NData.{nm}\n")
            open(os.path.join(d, nm + ".lean"), "w").write(src)
        s0_, s1_, sc_, pins_, Rs_, m_ = arc_head(a) if a["type"] != "E" else (0, 0, 0, "[]", "[]", 0)
        index.append({"arc": i, "name": f"A{i:04d}", "type": a["type"], "subs": sinfo,
                      "kids": [f"A{i:04d}S{k:03d}" for k in rkids],
                      "boxes0": "[" + ", ".join("(0, 0, 0)" for _ in range(m_)) + "]",
                      "recs": count_recs(a["tree"]) if "tree" in a else 0})
    json.dump(index, open(os.path.join(d, "index.json"), "w"))
    print("wrote modules", rng, "subtrees", sum(len(x["subs"]) for x in index))


def first_node(node, pred, path=()):
    """first node (depth-first, tile-arc order) satisfying pred"""
    if pred(node):
        return node
    if "ivsplit" in node or "split" in node:
        for k in node["kids"]:
            r = first_node(k, pred)
            if r is not None:
                return r
        return None
    if node.get("type") == "W":
        for a in sorted(node["tile_arcs"], key=lambda a: F(a["hard"][0]) if isinstance(a, dict) else F(a[0])):
            if isinstance(a, dict):
                r = first_node(a["child"], pred)
                if r is not None:
                    return r
    return None


def perturb(child, kind):
    """negative controls (the result must be false): returns a perturbed deep copy, or None if not applicable."""
    c = json.loads(json.dumps(child))
    isW = lambda n: n.get("type") == "W"
    if kind == "u_neg":            # a W1 record with u -> -u
        n = first_node(c, lambda n: isW(n) and any(not isinstance(a, dict) for a in n["tile_arcs"]))
        if n is None: return None
        a = next(a for a in n["tile_arcs"] if not isinstance(a, dict))
        a[2], a[3] = str(-F(a[2])), str(-F(a[3]))
    elif kind == "vt_neg":         # a W1 record with vt_1 -> -vt_1
        n = first_node(c, lambda n: isW(n) and n.get("mus") and any(not isinstance(a, dict) for a in n["tile_arcs"]))
        if n is None: return None
        a = next(a for a in n["tile_arcs"] if not isinstance(a, dict))
        k = len(a) - 2 * len(n["mus"])
        if F(a[k]) == 0 and F(a[k + 1]) == 0: return None
        a[k], a[k + 1] = str(-F(a[k])), str(-F(a[k + 1]))
    elif kind == "qr_out":         # w_rep's q_r outside the hard arc of its first tube
        n = first_node(c, lambda n: isW(n) and n.get("mus"))
        if n is None: return None
        n["mus"][0][0] = str(F(n["mus"][0][0]) + 1)
    elif kind == "mu_bad":         # w_rep's mu_r -> mu_r + 1
        n = first_node(c, lambda n: isW(n) and n.get("mus"))
        if n is None: return None
        n["mus"][0][1] = str(F(n["mus"][0][1]) + 1)
    elif kind == "tau_low":        # tau_rep below tau
        n = first_node(c, lambda n: n.get("type") in ("W", "empty"))
        n["tau_rep"] = "1/5"
    elif kind == "v_neg_empty":    # an empty leaf with v -> -v
        n = first_node(c, lambda n: n.get("type") == "empty")
        if n is None: return None
        n["v"] = [str(-F(x)) for x in n["v"]]
    elif kind == "ivsplit_out":    # an ivsplit point moved to the end of its arc
        n = first_node(c, lambda n: "ivsplit" in n)
        if n is None: return None
        n["at"] = "1"
    elif kind == "wrep_mass":      # w_rep mass above tau_N
        n = first_node(c, lambda n: isW(n))
        n["wrep_m"] = [str(F(x) * 2) for x in n["wrep_m"]]
    else:
        raise ValueError(kind)
    return c


NEG_KINDS = ["u_neg", "vt_neg", "qr_out", "mu_bad", "tau_low", "v_neg_empty", "ivsplit_out", "wrep_mass"]


def cmd_sample(args):
    cfg = json.load(open(args.cfg))
    tiles = {}
    for nm, t in cfg["tiles"].items():           # as the assembler: 'up' tiles as given, 'dn' tiles conjugated
        tiles[nm + "up"] = t; tiles[nm + "dn"] = [t[0], str(-F(t[1])), t[2], t[3]]
    ctx = Ctx(cfg["tau"], cfg["T1"], tiles, args.eps)
    rnd = random.Random(args.seed)
    stubs, fine = {}, []
    for fn in sorted(glob.glob(os.path.join(args.phasea, "A", "A_*.jsonl"))):
        for line in open(fn):
            r = json.loads(line)
            if "stub" in r:
                stubs[r["k"]] = r
            elif r["result"]["type"] == "N":
                fine.append(r["result"])
    jobs = []
    src = [HEADER, TESTHDR, f"def glob : GlobN := {ctx.glob_term()}\n\n#eval checkGlobN glob\n\n"]
    # (1) complete rooted arcs of phase A (root W leaf, no tubes)
    for i, a in enumerate(rnd.sample(fine, min(args.n_arc, len(fine)))):
        term, _ = arc_term(ctx, a)
        nrec = count_recs(a["tree"])
        src.append(f"def arcA{i} : ArcN := {term}\n")
        src.append(eval_block(f"arcA{i}", f"runArc glob arcA{i}", f"job {len(jobs)} arcA s0={a['s0']} recs={nrec}"))
        jobs.append({"kind": "arc", "arc": a, "recs": nrec})
    # (2) root W leaves of joined arcs: stub W1 records + the task pieces as hard arcs (children not checked)
    for i, k in enumerate(rnd.sample(sorted(stubs), min(args.n_root, len(stubs)))):
        st = stubs[k]["stub"]
        leaf = {kk: v for kk, v in st.items() if kk not in ("stub", "w1_arcs", "hard")}
        leaf["tile_arcs"] = st["w1_arcs"] + [{"hard": list(t), "kind": "iv", "child": {}} for t in stubs[k]["tasks"]]
        s0, s1 = F(k, 4096), F(k + 1, 4096)
        arc = {"type": "N", "s0": str(s0), "s1": str(s1), "sc": str((s0 + s1) / 2), "pcs": [], "Rs": [], "tree": leaf}
        enc = Enc(ctx, arc, 0)
        enc.tree = (lambda orig: (lambda node, tubes, boxes, top=False: ".ext" if node == {} else orig(node, tubes, boxes, top)))(enc.tree)
        t = enc.tree(leaf, [], [], top=True)
        rX = ctx.rad(arc["s0"], arc["s1"], arc["sc"], ctx.tau)
        src.append(f"def arcR{i} : ArcN := .N {grid(s0, ES)} {grid(s1, ES)} {grid((s0 + s1) / 2, ES)} [] [] {rX} {t}\n")
        nrec = len(st["w1_arcs"])
        src.append(eval_block(f"arcR{i}", f"runArc glob arcR{i}", f"job {len(jobs)} root k={k} recs={nrec}"))
        jobs.append({"kind": "root", "arc": arc, "recs": nrec})
    # (3) phase-B subtrees in the context of their arc and stub (one random entry of random task lines)
    files = sorted(glob.glob(args.phaseb))
    picked = 0
    while picked < args.n_sub:
        fn = rnd.choice(files)
        lines = []
        with gzip.open(fn, "rt") as fh:
            for j, line in enumerate(fh):
                if j >= args.scan:
                    break
                lines.append(line)
        if not lines:
            continue
        r = json.loads(rnd.choice(lines))
        k = r["k"]
        if not r["ok"] or k not in stubs:
            continue
        st = stubs[k]["stub"]
        ents = r["entries"]
        if args.need:
            ents = [e for e in ents if all(first_node(e["child"], (lambda n, w=w: ("ivsplit" in n) if w == "ivsplit"
                                                                   else n.get("type") == w)) is not None
                                           for w in args.need.split(","))]
            if not ents:
                continue
        e = rnd.choice(ents)
        s0, s1 = F(k, 4096), F(k + 1, 4096)
        arc = {"type": "N", "s0": str(s0), "s1": str(s1), "sc": str((s0 + s1) / 2), "pcs": [], "Rs": []}
        tube = (st["tile"], F(e["hard"][0]), F(e["hard"][1]), st["wrep_t"], st["wrep_m"])
        enc = Enc(ctx, arc, 0)
        t = enc.tree(e["child"], [tube], [], top=True)
        a_s, t = sub_stmt(ctx, arc, [tube], [], t)
        nrec = count_recs(e["child"])
        src.append(f"def sub{picked} : NTree := {t}\n")
        src.append(eval_block(f"sub{picked}", f"runSub glob {a_s} sub{picked}",
                              f"job {len(jobs)} sub k={k} hard={e['hard'][0]},{e['hard'][1]} recs={nrec}"))
        jobs.append({"kind": "sub", "arc": arc, "tube": [st["tile"], e["hard"][0], e["hard"][1], st["wrep_t"],
                                                          st["wrep_m"]], "child": e["child"], "recs": nrec,
                     "file": os.path.basename(fn)})
        picked += 1
    # (4) negative controls on the sub jobs (each kind on the first sub job where it applies)
    subs = [j for j in jobs if j["kind"] == "sub"]
    for kind in (NEG_KINDS if args.neg else []):
        for j0 in subs:
            pc = perturb(j0["child"], kind)
            if pc is None:
                continue
            arc = j0["arc"]; nm, q0, q1, ts, ms = j0["tube"]
            tube = (nm, F(q0), F(q1), ts, ms)
            enc = Enc(ctx, arc, 0)
            t = enc.tree(pc, [tube], [], top=True)
            a_s, t = sub_stmt(ctx, arc, [tube], [], t)
            i = len(jobs)
            src.append(f"def neg{i} : NTree := {t}\n")
            src.append(eval_block(f"neg{i}", f"runSub glob {a_s} neg{i}", f"job {i} neg:{kind} recs={j0['recs']}"))
            jobs.append(dict(j0, child=pc, neg=kind))
            break
    os.makedirs(args.out, exist_ok=True)
    open(os.path.join(args.out, "Test.lean"), "w").write("".join(src))
    json.dump({"tau": cfg["tau"], "T1": cfg["T1"], "tiles": tiles, "iv_eps": args.eps, "jobs": jobs},
              open(os.path.join(args.out, "jobs.json"), "w"))
    print("wrote", args.out, "jobs", len(jobs))


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest="cmd", required=True)
    m = sp.add_parser("modules"); m.add_argument("cert"); m.add_argument("out")
    m.add_argument("--max-recs", type=int, default=20000); m.add_argument("--range", default="")
    m.add_argument("--upper", action="store_true")
    m.add_argument("--index-offset", type=int, default=0)
    s = sp.add_parser("sample"); s.add_argument("cfg"); s.add_argument("phasea"); s.add_argument("phaseb")
    s.add_argument("out"); s.add_argument("--n-sub", type=int, default=20); s.add_argument("--n-arc", type=int, default=5)
    s.add_argument("--n-root", type=int, default=3); s.add_argument("--seed", type=int, default=1)
    s.add_argument("--scan", type=int, default=400); s.add_argument("--eps", default="1/1000000")
    s.add_argument("--neg", action="store_true"); s.add_argument("--need", default="")
    args = ap.parse_args()
    cmd_modules(args) if args.cmd == "modules" else cmd_sample(args)


if __name__ == "__main__":
    main()
