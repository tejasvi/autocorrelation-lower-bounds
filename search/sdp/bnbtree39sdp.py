"""Production-shaped writer with SDP-direct leaves: bnbtree39f_4702b857.py (loaded unchanged from this file's directory) plus
an SDP model used when the run's opts.json has "sdp": true.  CLI, files, records and meta are those of bnbtree39f; only the model
changes (see README.md in this directory).  Extra dependency on the workers: clarabel (pip).
  init:  bnbtree39sdp.py init DIR n lam --depth D --opts "$(cat opts_init.json)"   (the options of the run behind the paper)
  work / status / recover: exactly as bnbtree39f (the workers read the sdp options from DIR/opts.json)."""
import os, sys, time, json, importlib.util
from fractions import Fraction as Fr
import numpy as np
import scipy.sparse as sp
_HERE = os.path.dirname(os.path.abspath(__file__))
_BASE = os.path.join(_HERE, "bnbtree39f_4702b857.py")
sys.path.insert(0, _HERE)
_spec = importlib.util.spec_from_file_location("bnbtree39f_base", _BASE)
_base = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(_base)

SDP_DEFAULTS = dict(sdp=False, sdp_gap=0.008, sdp_k=12, sdp_tol=1e-5, sdp_maxit=200, sdp_mode='active', sdp_mindepth=0,
                    sdp_dense_age=3, sdp_direct=True, sdp_eig_rel=1e-7, sdp_refine=False, sdp_maxit_cap=None, sdp_log=False, sdp_fallback=False,
                    sdp_setup_lp_cuts=True, sdp_slack_tol=1e-3)


class SDPOracle:
    def __init__(self, model):
        self.m = m = model; n = m.n; spec = m.spec
        N = n + 1; self.N = N
        A = m.A.tocsr(); nf = m.nfixed
        lo = m.row_lo[:nf]; up = m.row_up[:nf]
        eq = np.isfinite(lo) & np.isfinite(up) & (lo == up)
        le = ~np.isfinite(lo) & np.isfinite(up)
        ge = np.isfinite(lo) & ~np.isfinite(up)
        rng = np.isfinite(lo) & np.isfinite(up) & (lo != up)
        self.eq_idx = np.nonzero(eq)[0]; self.le_idx = np.nonzero(le | rng)[0]; self.ge_idx = np.nonzero(ge | rng)[0]
        self.A_eq = A[self.eq_idx]; self.b_eq = lo[self.eq_idx]
        self.A_fix_in = sp.vstack([A[self.le_idx], -A[self.ge_idx]]).tocsr()
        self.k_fix = np.concatenate([up[self.le_idx], -lo[self.ge_idx]])
        self.ncol = m.ncol
        # PSD map: entry (a, b) of M (a, b >= 0, upper incl. diagonal, (0,0) constant) <- column index, weight in <S, E_j>
        pcols = np.array([m.cix[("m", spec.leaf_of_bin[i])] for i in range(n)])
        zc = np.zeros((n, n), dtype=np.int64)
        for i in range(n):
            for j in range(n):
                zc[i, j] = m.cix[("Z", min(i, j), max(i, j))]
        self.pcols, self.zcols = pcols, zc
        iu = np.triu_indices(n)
        self.zu_cols = zc[iu]; self.zu_i = iu[0]; self.zu_j = iu[1]
        self.zu_w = np.where(iu[0] == iu[1], 1.0, 2.0)
        self.c = np.asarray(m.cost, float)

    # ---- data at the current box (model.L, model.U) ------------------------------------------------------------
    def setup(self):
        m = self.m; L, U = np.asarray(m.L, float), np.asarray(m.U, float)
        cz, cmd, cme, rhs = m.mc_coeffs(L, U)
        npair = m.npairs; diag = m.mc_diag
        rr, cc, vv, bb = [], [], [], []
        base = 0
        for q in range(4):
            ks = np.arange(npair) if q < 3 else np.nonzero(~diag)[0]
            r_ids = base + np.arange(len(ks))
            rr += [r_ids, r_ids]; cc += [m.mc_z[ks], m.mc_md[ks]]; vv += [cz[q, ks], cmd[q, ks]]
            nd = ~diag[ks]
            rr.append(r_ids[nd]); cc.append(m.mc_me[ks][nd]); vv.append(cme[q, ks][nd])
            bb.append(rhs[q, ks]); base += len(ks)
        A_mc = sp.csr_matrix((np.concatenate(vv), (np.concatenate(rr), np.concatenate(cc))), shape=(base, self.ncol))
        self.nmc = base
        # cut rows of the model's pool (rows nrow..nrow+ncut: square cuts "a x >= lo", stale McCormick rows "a x <= up")
        # v4: with sdp_setup_lp_cuts only the pool cuts that are rows of the LP (pos >= 0); the restricted SDP keeps only those
        # anyway, and dense SDP cuts accumulate in the pool until reset_cuts (speed only: the SDP is identical)
        lp_only = bool(m.opts.get("sdp_setup_lp_cuts"))
        cids = np.array([c for c in range(m.nrow, m.nrow + m.ncut) if c in m.cut_cols and len(m.cut_cols[c])
                         and (not lp_only or m.pos[c] >= 0)], dtype=np.int64)
        if len(cids):
            lo_c = np.asarray(m.row_lo[cids], float); up_c = np.asarray(m.row_up[cids], float)
            sgn = np.where(np.isfinite(lo_c), -1.0, 1.0)            # -1: ">= lo" row negated; +1: "<= up" row
            cr = np.concatenate([np.full(len(m.cut_cols[c]), t) for t, c in enumerate(cids)])
            ccol = np.concatenate([np.asarray(m.cut_cols[c]) for c in cids])
            cval = np.concatenate([sgn[t] * np.asarray(m.cut_vals[c], float) for t, c in enumerate(cids)])
            A_cut = sp.csr_matrix((cval, (cr, ccol)), shape=(len(cids), self.ncol))
            k_cut = np.where(sgn < 0, -lo_c, up_c)
        else:
            sgn = np.zeros(0); A_cut = sp.csr_matrix((0, self.ncol)); k_cut = np.zeros(0)
        self.cut_ids, self.cut_sgn = cids, sgn
        # canonical McCormick row (nfixed + 4 pair + q) of each of my McCormick rows (q-major; q = 3 skips diagonal pairs)
        kk = np.concatenate([np.arange(npair)] * 3 + [np.nonzero(~diag)[0]])
        qq = np.concatenate([np.full(npair, q) for q in range(3)] + [np.full(int((~diag).sum()), 3)])
        self.mc_canon = m.nfixed + 4 * kk + qq
        self.K = sp.vstack([self.A_fix_in, A_mc, A_cut]).tocsr(); self.KT = self.K.T.tocsr()
        self.k = np.concatenate([self.k_fix, np.concatenate(bb), k_cut])
        self.AeT = self.A_eq.T.tocsr()
        lb = np.asarray(m.col_lb, float).copy(); ub = np.asarray(m.col_ub, float).copy()
        lb[m.blockcol] = L; ub[m.blockcol] = U
        self.lb, self.ub = lb, ub

    def duals_from_writer(self, y):
        """Writer convention (y_r > 0: a_r x >= lo_r, y_r < 0: a_r x <= up_r; canonical rows) -> (ye, yl) of this oracle."""
        y = np.asarray(y, float)
        ye = y[self.eq_idx].copy()
        yle = np.maximum(-y[self.le_idx], 0.0); yge = np.maximum(y[self.ge_idx], 0.0)
        ymc = np.maximum(-y[self.mc_canon], 0.0)
        # diagonal pairs: canonical q = 3 duplicates q = 2 (not among my rows): fold its dual onto q = 2
        m = self.m; dk = np.nonzero(m.mc_diag)[0]
        if len(dk):
            npair = m.npairs
            ymc[2 * npair + dk] += np.maximum(-y[m.nfixed + 4 * dk + 3], 0.0)
        ycut = np.maximum(-self.cut_sgn * y[self.cut_ids], 0.0) if len(self.cut_ids) else np.zeros(0)
        return ye, np.concatenate([yle, yge, ymc, ycut])

    def writer_from_duals(self, ye, yl, cap):
        """(ye, yl) -> writer-convention canonical row duals (length cap; cut rows left zero)."""
        y = np.zeros(cap)
        y[self.eq_idx] += ye
        a = len(self.le_idx); b = len(self.ge_idx)
        np.add.at(y, self.le_idx, -yl[:a]); np.add.at(y, self.ge_idx, yl[a:a + b])
        np.add.at(y, self.mc_canon, -yl[a + b:a + b + self.nmc])
        if len(self.cut_ids):
            y[self.cut_ids] += -self.cut_sgn * yl[a + b + self.nmc:]
        return y

    def Mof(self, x):
        n = self.m.n; M = np.empty((n + 1, n + 1)); M[0, 0] = 1.0
        M[0, 1:] = M[1:, 0] = x[self.pcols]; M[1:, 1:] = x[self.zcols]
        return M

    def AstarS(self, S):
        """<S, E_j> for every column j (zero for columns outside M)."""
        g = np.zeros(self.ncol)
        g[self.pcols] += 2.0 * S[0, 1:]
        np.add.at(g, self.zu_cols, self.zu_w * S[1 + self.zu_i, 1 + self.zu_j])
        return g

    def reduced(self, ye, yl, S):
        return self.c - self.AeT @ ye + self.KT @ yl - self.AstarS(S)

    def dual_bound(self, ye, yl, S):
        r = self.reduced(ye, yl, S)
        return float(self.b_eq @ ye - self.k @ yl - S[0, 0] + np.minimum(r * self.lb, r * self.ub).sum())


def restricted_sdp(orc, active_only=True, extra_rows=None, tol=1e-7, max_iter=200, dual_rows=None, slack_x=None, slack_tol=None,
                   free_aux=False, solve_method=None, settings=None, only_rows=None):
    """Clarabel Shor SDP over the oracle's rows restricted to those present in the model's HiGHS LP (pos >= 0), plus column
    bounds and the PSD cone.  Returns (value, S, time).  The S (PSD dual) only proposes cut directions."""
    import clarabel
    m = orc.m; orc.setup()
    canon_in = np.concatenate([orc.le_idx, orc.ge_idx, orc.mc_canon, orc.cut_ids]).astype(np.int64)
    keep_in = (m.pos[canon_in] >= 0) if active_only else np.ones(len(canon_in), bool)
    keep_eq = (m.pos[orc.eq_idx] >= 0) if active_only else np.ones(len(orc.eq_idx), bool)
    if extra_rows is not None:
        keep_in |= np.isin(canon_in, extra_rows)
    if dual_rows is not None:                    # inequality rows restricted further to those with a nonzero LP dual
        keep_in &= np.isin(canon_in, dual_rows)
    if only_rows is not None:                    # inequality rows restricted to the given canonical ids (e.g. an ancestor's SDP-active set)
        keep_in &= np.isin(canon_in, only_rows)
    orc.last_canon_in = canon_in
    if slack_x is not None:                      # ... or to rows within slack_tol of active at the LP primal slack_x
        sl = orc.k - orc.K @ slack_x
        keep_in &= sl <= slack_tol * (1.0 + np.abs(orc.k))
    Ae = orc.A_eq[keep_eq]; be = orc.b_eq[keep_eq]
    Kin = orc.K[keep_in]; kin = orc.k[keep_in]
    N = orc.N; nsv = N * (N + 1) // 2; n = m.n
    rows, cols, vals = [], [], []; b_psd = np.zeros(nsv); k = 0
    for j in range(N):
        for i in range(j + 1):
            sc = 1.0 if i == j else np.sqrt(2.0)
            if i == 0 and j == 0:
                b_psd[k] = 1.0
            elif i == 0:
                rows.append(k); cols.append(orc.pcols[j - 1]); vals.append(-sc)
            else:
                rows.append(k); cols.append(orc.zcols[i - 1, j - 1]); vals.append(-sc)
            k += 1
    A_psd = sp.csr_matrix((vals, (rows, cols)), shape=(nsv, orc.ncol))
    I = sp.identity(orc.ncol, format='csr')
    fin_u = np.isfinite(orc.ub); fin_l = np.isfinite(orc.lb)
    if free_aux:
        # P, G, ZA columns free: their reduced costs vanish at the optimum, which is exactly the verifier's completion of the
        # P/G/ZA row duals in a D record (so the SDP dual stays certifiable after completion)
        aux = np.array([k[0] in ('P', 'G', 'ZA') for k in m.colkeys], dtype=bool)
        fin_u &= ~aux; fin_l &= ~aux
    A_nn = sp.vstack([Kin, I[fin_u], -I[fin_l]]).tocsr()
    b_nn = np.concatenate([kin, orc.ub[fin_u], -orc.lb[fin_l]])
    A = sp.vstack([Ae, A_nn, A_psd]).tocsc(); b = np.concatenate([be, b_nn, b_psd])
    st = clarabel.DefaultSettings(); st.verbose = False; st.max_iter = max_iter
    st.tol_gap_abs = tol; st.tol_gap_rel = tol; st.tol_feas = tol; st.max_threads = 1
    if solve_method:
        st.direct_solve_method = solve_method
    for k_, v_ in (settings or {}).items():
        setattr(st, k_, v_)
    t0 = time.process_time()
    cones = [clarabel.ZeroConeT(Ae.shape[0]), clarabel.NonnegativeConeT(A_nn.shape[0]), clarabel.PSDTriangleConeT(N)]
    sol = clarabel.DefaultSolver(sp.csc_matrix((orc.ncol, orc.ncol)), orc.c, A, b, cones, st).solve()
    t = time.process_time() - t0
    z = np.array(sol.z)[-nsv:]; S = np.zeros((N, N)); k = 0
    for j in range(N):
        for i in range(j + 1):
            if i == j:
                S[i, i] = z[k]
            else:
                S[i, j] = S[j, i] = z[k] / np.sqrt(2.0)
            k += 1
    zz = np.array(sol.z)
    ye = np.zeros(len(orc.eq_idx)); yl = np.zeros(len(canon_in))
    ne = int(keep_eq.sum()); ni = int(keep_in.sum())
    ye[keep_eq] = -zz[:ne]; yl[keep_in] = np.maximum(zz[ne:ne + ni], 0.0)
    orc.last_duals = (ye, yl)
    return (float(sol.obj_val) if np.isfinite(sol.obj_val) else None), S, t, int(Ae.shape[0] + Kin.shape[0])


class SDPModel(_base.Model):
    def __init__(self, n, lam, opts=None):
        o = dict(SDP_DEFAULTS); o.update(opts or {})
        super().__init__(n, lam, o)
        self.orc = SDPOracle(self)
        sp_ = self.spec
        self.zidx = np.array([[self.cix[("Z", min(i, j), max(i, j))] for j in range(n)] for i in range(n)])
        self.pidx = np.array([self.cix[("m", sp_.leaf_of_bin[i])] for i in range(n)])
        self.sdp_stats = {"calls": 0, "time": 0.0, "close": 0, "cuts": 0, "resolve_time": 0.0}
        self.dense_ids = set()
        self.sdp_log = []                  # per call: [gap before, sdp value, #cuts, LP after (or None), closed, sdp time]

    def dense_cut(self, v):
        n = self.n; sp_ = self.spec
        v = np.asarray(v, float)
        if np.abs(v[1:]).max() < 1e-9 * max(1.0, abs(v[0])):
            return None
        sc = 2 ** int(self.opts["psd_bits"])           # same scale as encode_leaf's 2*psd_bits cut rows (audit (b))
        v = v / np.abs(v).max(); vi = np.round(v * sc).astype(np.int64)
        if not vi[1:].any():
            return None
        vf = vi / float(sc); cols, vals = [], []
        nz = [i for i in range(n) if vi[i + 1] != 0]
        for a, i in enumerate(nz):
            cols.append(int(self.zidx[i, i])); vals.append(vf[i + 1] ** 2)
            if vi[0] != 0:
                cols.append(int(self.pidx[i])); vals.append(2 * vf[0] * vf[i + 1])
            for j in nz[a + 1:]:
                cols.append(int(self.zidx[i, j])); vals.append(2 * vf[i + 1] * vf[j + 1])
        key = ["sq", int(vi[0]), [[int(sp_.leaf_of_bin[i]), int(vi[i + 1])] for i in nz]]
        cid = self.new_cut(cols, vals, -vf[0] ** 2, key)
        if cid is not None:
            self.dense_ids.add(int(cid))
        return cid

    def direct_dual(self, ev, V):
        """Writer-convention dual of the SDP solution: row duals (restricted rows, zeros elsewhere) plus one dense square cut
        per eigenvector of S with eigenvalue > sdp_eig_rel * max (multiplier sigma * |u|_inf^2: the cut row is built from
        u / |u|_inf).  Cuts are created in the pool, not added to the LP."""
        if getattr(self.orc, 'last_duals', None) is None:
            return None
        ye, yl = self.orc.last_duals
        y = self.orc.writer_from_duals(ye, yl, self.cap)
        top = ev.max()
        if top <= 0:
            return None
        for i in np.argsort(-ev):
            if ev[i] <= self.opts["sdp_eig_rel"] * top:
                break
            u = V[:, i]; sc = np.abs(u).max()
            cid = self.dense_cut(u)
            if cid is None:
                continue
            y[cid] += ev[i] * sc * sc
        return y

    def reset_cuts(self):
        super().reset_cuts()
        self.dense_ids = set()

    def solve_node(self):
        A = self.opts.get("sdp_dense_age")
        if A is not None and self.dense_ids:
            lr = self.lprows
            dmask = np.fromiter((int(c) in self.dense_ids for c in lr), dtype=bool, count=len(lr))
            dead = lr[dmask & (self.age[lr] > A)]
            if len(dead):
                self.delete_rows(dead)
        res = super().solve_node()
        o = self.opts
        if not o["sdp"] or res[0] != "branch" or res[1] is None or self.lam - res[1] > o["sdp_gap"]:
            return res
        t0 = time.process_time()
        try:
            # v4: sdp_slack_tol keeps only the LP rows within that relative slack of active at the LP primal (fewer rows)
            xs = {} if o.get("sdp_slack_tol") is None or res[2] is None else dict(slack_x=np.asarray(res[2], float), slack_tol=o["sdp_slack_tol"])
            val, S, ts, nrows = restricted_sdp(self.orc, active_only=(o["sdp_mode"] == 'active'), tol=o["sdp_tol"],
                                               max_iter=o["sdp_maxit"], free_aux=bool(o.get("sdp_direct")),
                                               settings=None if o.get("sdp_refine", True) else {'iterative_refinement_enable': False}, **xs)
        except Exception:
            val, S = None, None
        tcall = time.process_time() - t0
        self.sdp_stats["calls"] += 1; self.sdp_stats["time"] += tcall
        entry = [self.lam - res[1], val, 0, None, 0, tcall]
        if o.get("sdp_log", True):
            self.sdp_log.append(entry)                # per-call log for experiments; off in production (audit (d))
        if S is None or val is None or not np.isfinite(val) or not np.all(np.isfinite(S)) or val < self.lam:
            return res                          # the SDP cannot close this node (or failed): branch, no cuts added (audit (a))
        try:
            return self._sdp_close(res, S, entry)
        except Exception:
            self.sdp_stats["post_fail"] = self.sdp_stats.get("post_fail", 0) + 1
            return res                          # any failure after the SDP: branch as in production (audit (a))

    def _sdp_close(self, res, S, entry):
        o = self.opts
        ev, V = np.linalg.eigh(S); order = np.argsort(-ev)
        if o.get("sdp_direct"):
            y_direct = self.direct_dual(ev, V)
            if y_direct is not None:
                enc = self.encode_leaf(self.canon_dual(y_direct), np.asarray(self.L), np.asarray(self.U))
                if enc is not None:
                    self.sdp_stats["close"] += 1; self.sdp_stats["direct"] = self.sdp_stats.get("direct", 0) + 1
                    entry[3] = enc[1]; entry[4] = 2
                    return ("leaf", enc[1], res[2], y_direct)
            self.sdp_stats["direct_fail"] = self.sdp_stats.get("direct_fail", 0) + 1
        if not o.get("sdp_fallback", True):
            return res                          # production: dense cuts never enter the LP (a later LP leaf using one
                                                # could fall back to an uncertifiable U leaf): just branch (v4: also
                                                # without sdp_direct)
        ids = []
        for i in order[:o["sdp_k"]]:
            if ev[i] <= 1e-6 * max(ev.max(), 1e-12):
                break
            cid = self.dense_cut(V[:, i])
            if cid is not None and self.pos[cid] < 0:
                ids.append(cid)
        if not ids:
            return res
        self.add_rows(np.array(ids, dtype=np.int64)); self.sdp_stats["cuts"] += len(ids)
        t1 = time.process_time()
        res2 = super().solve_node()
        self.sdp_stats["resolve_time"] += time.process_time() - t1
        entry[2] = len(ids); entry[3] = res2[1]
        if res2[0] == "leaf":
            # a leaf closed with dense cuts must carry them: if no D/E encoding passes the float re-check, the
            # production writer would fall back to a U leaf that the verifier cannot certify with its own cuts -> branch
            y2 = res2[3]
            uses_dense = y2 is not None and np.any(y2[self.nrow:self.nrow + self.ncut] != 0)
            if uses_dense and self.encode_leaf(self.canon_dual(y2), np.asarray(self.L), np.asarray(self.U)) is None:
                self.sdp_stats["encode_fail"] = self.sdp_stats.get("encode_fail", 0) + 1
                return res                      # branch with the pre-SDP LP result (always carries x) (audit (c))
            self.sdp_stats["close"] += 1; entry[4] = 1
        return res2


def make_model(n, lam, opts):
    o = dict(opts or {})
    if o.get("sdp"):
        oo = dict(SDP_DEFAULTS); oo.update(o)
        m = SDPModel(n, float(lam), oo)
    else:
        m = _base.Model(n, float(lam), o)
    m.lam_exact = Fr(lam)
    return m


_base.make_model = make_model

if __name__ == "__main__":
    _src = open(_BASE).read()
    _main = _src[_src.index('if __name__ == "__main__":'):].replace('if __name__ == "__main__":', 'if True:', 1)
    exec(compile(_main, _BASE, "exec"), _base.__dict__)
