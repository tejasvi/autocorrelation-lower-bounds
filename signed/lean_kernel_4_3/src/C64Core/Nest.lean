import C64Core.Check

/-!
# Nested certificates: the checker (core Lean only)

This extends the three-level checker (`C64Core.Check`) to nested certificates: the node sets carry interval tubes
(`∃ z ∈ A'', μ ≥ 0 : |ŵ(z) - S(z) - μ G_base(z)| ≤ ε`, `A''` an arc of a tile), the witness (W) leaves may have hard
tile arcs whose children carry one more tube, and `ivsplit` nodes split the arc of a tube.  The conditions are those
of the nested checker of record:
* every leaf has its own mass parameter `τ_N ≥ τ` (crossing radius `r'` for `τ_N`, `r ≤ r'`);
* the sign condition and the bound term of a tube are bounded on pieces of its arc (midpoint, disc radius, Lipschitz
  bound of `G_base` on the disc), with bisection of a piece where the test fails;
* in the functions of `t`, the term of a tube is bounded by the maximum over pieces of its arc (`groupHi`), each with a
  disc correction that is proportional to `|t|` (`termHi`);
* the representative `w_rep` of a W leaf lies in the node set: mass, crossing disc, boxes, and for every tube a point
  `q_r` of its arc and `μ_r ≥ 0` with `|ŵ_rep(z(q_r)) - S(z(q_r)) - μ_r G_base(z(q_r))| ≤ ε`;
* the tile arcs of a W leaf (W1 records and hard arcs) tile `[0, 1]`.
The functions of the three-level checker are not changed.
-/

namespace C64Chk

open Ival Ival.Ball C64Num

/-! ## Data -/

/-- An interval tube: the tile index, the arc `[q₀, q₁]` (`q = n / 2^EQ`) and the base atoms `(t_k, m_k)`. -/
structure TubeD where
  ti : Nat
  q0 : Nat
  q1 : Nat
  as : List (Q × Q)
deriving Repr, Inhabited

/-- The header of a W leaf: tile index, `τ_N`, a proposed crossing radius `rX` for `τ_N`, `σ`, the atoms of `w_rep`,
and per tube `(q_r, μ_r)`. -/
structure WHdr where
  ti : Nat
  tw : Q
  rX : Nat
  sg : Q
  as : List (Q × Q)
  mus : List (Q × Q)
deriving Repr, Inhabited

/-- The node trees.  `wit h n dat hards kids`: `n` W1 records in `dat` (each `q₁, u, v, y_1 … y_m, vt_1 … vt_K`, in the
order of the tile arcs), the hard arcs `[q₀, q₁]` (in order) and their children.  `empty tw rX dat`: the multipliers
`v, y_1 … y_m, vt_1 … vt_K`.  `ext`: a subtree whose check is a separate statement. -/
inductive NTree where
  | empty (tw : Q) (rX : Nat) (dat : Nat)
  | wit (h : WHdr) (n : Nat) (dat : Nat) (hards : List (Nat × Nat)) (kids : List NTree)
  | split (j : Nat) (c0 c1 c2 c3 : NTree)
  | ivsplit (k : Nat) (qm : Nat) (lo hi : NTree)
  | ext
deriving Repr, Inhabited

/-- Arcs of a nested certificate: an arc of the three-level format, or a rooted arc with a node tree. -/
inductive ArcN where
  | old (a : Arc)
  | N (s0 s1 sc : Nat) (pins : List (Q × Q)) (Rs : List Q) (rX : Nat) (t : NTree)
deriving Repr, Inhabited

/-- Global data of a nested certificate: the three-level data, `ε` of the interval tubes, the number `2^lS` of
pieces for the sign and bound conditions of a tube and their bisection depth `dS`, the numbers `2^lT, …,
2^(lT + nL - 1)` of pieces of a tube in the functions of `t` (tried in this order), and a depth bound of the trees. -/
structure GlobN where
  g : Glob
  eps : Q
  lS : Nat
  dS : Nat
  lT : Nat
  nL : Nat
  fuel : Nat
deriving Repr, Inhabited

/-- `⌈ε 2^P⌉` and `⌊ε 2^P⌋`. -/
def epsHi (gn : GlobN) : Nat := Ball.cdiv (gn.eps.n.toNat * 2 ^ gn.g.P) gn.eps.d
def epsLo (gn : GlobN) : Nat := gn.eps.n.toNat * 2 ^ gn.g.P / gn.eps.d

/-! ## Multiplication with shifts (equal to `Ball.mul`; used in the inner loops) -/

/-- `Ball.mul` computed with shifts: `rnd2 p P = (p + 2^P / 2) >>> P`, `cdiv n 2^P = (n + 2^P - 1) >>> P`. -/
@[inline] def Ball.mulS (P : Nat) (a b : Ball) : Ball :=
  ⟨(a.m * b.m + (((1 <<< P) >>> 1 : Nat) : Int)) >>> P,
   ((a.m.natAbs * b.r + b.m.natAbs * a.r + a.r * b.r + (1 <<< P) - 1) >>> P) + 1⟩

/-- `CBall.mul` with `Ball.mulS`. -/
@[inline] def CBall.mulS (P : Nat) (a b : CBall) : CBall :=
  ⟨Ball.sub (Ball.mulS P a.re b.re) (Ball.mulS P a.im b.im), Ball.add (Ball.mulS P a.re b.im) (Ball.mulS P a.im b.re)⟩

/-- `reMul` with `Ball.mulS`. -/
@[inline] def reMulS (P : Nat) (a b : CBall) : Ball := Ball.sub (Ball.mulS P a.re b.re) (Ball.mulS P a.im b.im)

/-! ## Bounds in `t` with disc terms -/

/-- A term `Re(c K_t(z))` for `z` in a disc of radius `ρ` around the point `ζ` of a table: as `TermS`, the disc factor
`dz ≥ 2π ρ e^{π ρ}` and `yz ≥ 2π |Im ζ| e^{π |Im ζ| / 16}` (both `0` for a point). -/
structure TermD where
  W : CBall
  w : CBall
  st : List (CBall × CBall)
  m2 : Nat
  dz : Nat
  yz : Nat

def termD (cf : CBall) (T : PtT) (dy : Nat × Nat) : TermD := ⟨cf, T.w, T.st, T.mz, dy.1, dy.2⟩

def toD (T : TermS) : TermD := ⟨T.W, T.w, T.st, T.m2, 0, 0⟩

/-- An upper bound of `|W|` (units `2^-P`): `max + ⌈min / 2⌉ ≥ √(max² + min²)`. -/
@[inline] def absW (W : CBall) : Nat :=
  max W.re.absHi W.im.absHi + (min W.re.absHi W.im.absHi + 1) / 2

/-- The disc correction of a term on the cell with centre `tn / 2^e`: `|W| dz (|tn| + 1) / 2^e · (1 + yz / 2^e)`, an
upper bound of `|c| |K_t(z) - K_t(ζ)|` for `t` in the cell and `z` in the disc
(`|K_t(z) - K_t(ζ)| ≤ ρ 2π |t| e^{2π |t| ρ} |K_t(ζ)|`, `|K_t(ζ)| ≤ |K_{t_c}(ζ)| e^{2π h |Im ζ|}`,
`e^{2π h Y} ≤ 1 + 2π h Y e^{π Y / 16}` for `h ≤ 1/32`). -/
def corrD (P e : Nat) (tn : Int) (T : TermD) : Nat :=
  Ball.cdiv (mulU P (absW T.W) T.dz * (tn.natAbs + 1)) (2 ^ e) +
    Ball.cdiv (mulU P (mulU P (absW T.W) T.dz) T.yz * (tn.natAbs + 1)) (2 ^ (2 * e))

/-- Value, derivative, `Σ |W| m₂` and `Σ` of the disc corrections of a list of terms at the cell. -/
def sumTermsD (P e : Nat) (tn : Int) : List TermD → Ball × Ball × Nat × Nat
  | [] => (⟨0, 0⟩, ⟨0, 0⟩, 0, 0)
  | T :: ts =>
    let r := sumTermsD P e tn ts
    (Ball.add T.W.re r.1, Ball.add (reMulS P T.W T.w) r.2.1, mulU P (absW T.W) T.m2 + r.2.2.1, corrD P e tn T + r.2.2.2)

/-- A group (the pieces of a tube) on the cell: the largest `value + correction`, the hull of the derivatives, the
largest `|W| m₂`; `none` for an empty group. -/
def groupB (P e : Nat) (tn : Int) : List TermD → Option (Int × Ball × Nat)
  | [] => none
  | [T] => some (T.W.re.hi + (corrD P e tn T : Int), reMulS P T.W T.w, mulU P (absW T.W) T.m2)
  | T :: ts => (groupB P e tn ts).map fun b =>
      (max (T.W.re.hi + (corrD P e tn T : Int)) b.1, hullB (reMulS P T.W T.w) b.2.1, max (mulU P (absW T.W) T.m2) b.2.2)

/-- The sums over the groups. -/
def groupsB (P e : Nat) (tn : Int) : List (List TermD) → Option (Int × Ball × Nat)
  | [] => some (0, ⟨0, 0⟩, 0)
  | G :: gs => (groupB P e tn G).bind fun b => (groupsB P e tn gs).map fun s => (b.1 + s.1, Ball.add b.2.1 s.2.1, b.2.2 + s.2.2)

/-- The cell `[t_c - 2^{-e}, t_c + 2^{-e}]`, `t_c = tn / 2^e` (`e ≥ 5`), is accepted:
`f(t_c) + 2^{-e} |f'(t_c)| + 2^{-2e} M₂ / 2 + corrections < target`, the groups entering with the largest value,
the hull of their derivatives and the largest `M₂` term. -/
def cellOKD (P : Nat) (ts : List TermD) (gs : List (List TermD)) (e : Nat) (tn : Int) (target : Int) : Bool :=
  let r := sumTermsD P e tn ts
  decide (5 ≤ e) &&
    (groupsB P e tn gs).any fun b =>
      decide (r.1.hi + b.1 + (Ball.cdiv (Ball.add r.2.1 b.2.1).absHi (2 ^ e) : Nat) +
        (Ball.cdiv (r.2.2.1 + b.2.2) (2 ^ (2 * e + 1)) : Nat) + (r.2.2.2 : Int) < target)

def stepD (P : Nat) (down : Bool) (T : TermD) : TermD :=
  match T.st with
  | [] => T
  | (kp, km) :: rest => { T with W := CBall.mulS P T.W (if down then km else kp), st := rest }

/-- Adaptive cells with centres `tn / 2^e`. -/
def cellsD (P : Nat) (target : Int) : Nat → Nat → Nat → Int → List TermD → List (List TermD) → Bool
  | 0, _, _, _, _, _ => false
  | fuel + 1, skip, e, tn, ts, gs =>
    (skip == 0 && cellOKD P ts gs e tn target) ||
      (cellsD P target fuel (skip - 1) (e + 1) (2 * tn - 1) (ts.map (stepD P true)) (gs.map (·.map (stepD P true))) &&
       cellsD P target fuel (skip - 1) (e + 1) (2 * tn + 1) (ts.map (stepD P false)) (gs.map (·.map (stepD P false))))

/-- `Σ_terms Re(c K_t(z)) + Σ_groups max Re(c K_t(z)) < target` for all `t ∈ [-1/2, 1/2]` and all `z` in the discs. -/
def tboundD (P D : Nat) (ts : List TermD) (gs : List (List TermD)) (target : Int) : Bool :=
  cellsD P target (D + 1) 4 1 0 ts gs

/-- The factors `(2π ρ e^{π ρ}, 2π |Im z| e^{π |Im z| / 16})` (units `2^-P`) of a disc with centre `z`, radius `ρ`. -/
def dzOf (c : Cfg) (z : CBall) (rho : Nat) : Option (Nat × Nat) :=
  (expPiHi c rho).bind fun ex => (expPiHi c (Ball.cdiv z.im.absHi 16)).map fun ey =>
    (mulU c.P (2 * mulU c.P (piHi c.P) rho) ex, mulU c.P (2 * mulU c.P (piHi c.P) z.im.absHi) ey)

/-! ## Pieces with third-order bounds of `S` -/

/-- `(S(z), S'(z), S''(z))`, `S'' = ((2 - (πz)²) sin(πz) - 2πz cos(πz)) / (πz · z²)`. -/
def cSS2 (c : Cfg) (z : CBall) : Option (CBall × CBall × CBall) :=
  (ccosSinPi c z).bind fun cs =>
    let pz := CBall.mulR c.P (piB c.P) z
    (cdiv c.P cs.2 pz).bind fun s =>
    (cdiv c.P (CBall.sub (CBall.mul c.P pz cs.1) cs.2) (CBall.mul c.P pz z)).bind fun s1 =>
    (cdiv c.P (CBall.sub (CBall.mul c.P (CBall.sub ⟨Ball.ofInt c.P 2, ⟨0, 0⟩⟩ (CBall.mul c.P pz pz)) cs.2)
        (CBall.mul c.P (CBall.add pz pz) cs.1)) (CBall.mul c.P pz (CBall.mul c.P z z))).map fun s2 => (s, s1, s2)

/-- A piece `[n₀, n₁] / 2^e` of an ellipse: midpoint `z`, disc radius `ρ`, `S(z)`, `S'(z)`, `S''(z)`,
`eY ≥ e^{π (|Im z| + ρ)}`, and `dS ≥ sup |S(ζ) - S(z)|` on the disc:
`|S'(z)| ρ + |S''(z)| ρ² / 2 + (π³/3) eY ρ³ / 6`. -/
structure Piece3 where
  z : CBall
  rho : Nat
  sz : CBall
  s1 : CBall
  s2 : CBall
  eY : Nat
  dS : Nat

/-- The second- and third-order terms `|S''(z)| ρ² / 2 + π³ eY ρ³ / 18` (units `2^-P`). -/
def d23 (P : Nat) (s2 : CBall) (rho eY : Nat) : Nat :=
  Ball.cdiv (normHi s2 * rho * rho) (2 * 2 ^ (2 * P)) + Ball.cdiv (piHi P ^ 3 * eY * rho ^ 3) (18 * 2 ^ (6 * P))

def piece3 (c : Cfg) (E : EllB) (n0 n1 e : Nat) : Option Piece3 :=
  (ellPt c E (midB c.P n0 n1 e)).bind fun z =>
  (ellRad c E n0 n1 e).bind fun rho =>
  (cSS2 c z).bind fun ss =>
  (expPiHi c (z.im.absHi + rho)).map fun eY =>
    ⟨z, rho, ss.1, ss.2.1, ss.2.2, eY, mulU c.P (normHi ss.2.1) rho + d23 c.P ss.2.2 rho eY⟩

/-- Lower bound of `Re(ū S)` on the disc of the piece. -/
def aLow3 (P : Nat) (u : CBall) (p : Piece3) : Int := reConjLo P u p.sz - (mulU P (normHi u) p.dS : Nat)

/-- `Re(ū S(p)) - Re(v̄ S(z_c)) - |v| r' - Σ_j max_{Q_j} Re(ȳ_j x)` on the disc of the piece (lower bound). -/
def aTA3 (g : Glob) (A : ACtx) (r' : Nat) (u v : CBall) (hiY : Int) (p : Piece3) : Int :=
  aLow3 g.P u p - reConjHi g.P v A.Sc - (mulU g.P (normHi v) r' : Nat) - hiY

/-- `(Σ m_k K_{t_k}(z), Σ m_k (-2πi t_k) K_{t_k}(z))`. -/
def sumK1 (c : Cfg) (z : CBall) : List (Q × Q) → Option (CBall × CBall)
  | [] => some (⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨⟨0, 0⟩, ⟨0, 0⟩⟩)
  | (t, m) :: as => (ckt c (t.ball c.P) z).bind fun k => (sumK1 c z as).map fun s =>
      let mk := CBall.mulR c.P (m.ball c.P) k
      let tp := Ball.mulInt 2 (Ball.mul c.P (piB c.P) (t.ball c.P))
      (CBall.add mk s.1, CBall.add ⟨Ball.mul c.P tp mk.im, Ball.neg (Ball.mul c.P tp mk.re)⟩ s.2)

/-! ## Interval tubes -/

/-- A piece `[n₀, n₁] / 2^e` of the arc of a tube: `S` and `G_base` at the midpoint with bounds of their variation on
the disc: `dS` (as `Piece3`) and `dG = |G'(z)| ρ + d23 + Σ m_k · π² eY ρ² / 2`. -/
structure IvP where
  n0 : Nat
  n1 : Nat
  e : Nat
  sz : CBall
  dS : Nat
  gz : CBall
  dG : Nat

def ivPiece (c : Cfg) (E : EllB) (as : List (Q × Q)) (mSum : Nat) (n0 n1 e : Nat) : Option IvP :=
  (piece3 c E n0 n1 e).bind fun p => (sumK1 c p.z as).map fun w =>
    ⟨n0, n1, e, p.sz, p.dS, CBall.sub p.sz w.1,
     mulU c.P (normHi (CBall.sub p.s1 w.2)) p.rho + d23 c.P p.s2 p.rho p.eY +
       Ball.cdiv (mSum * piHi c.P ^ 2 * p.eY * p.rho * p.rho) (2 * 2 ^ (5 * c.P))⟩

/-- On one piece, for the multiplier `vt`: `neg = true` (W1): `Re(v̄t G) ≤ 0` on the disc, and the upper bound of
`Re(v̄t S)`; `neg = false` (empty leaf): `Re(v̄t G) ≥ 0`, and the lower bound of `Re(v̄t S)`. -/
def ivOne (P : Nat) (neg : Bool) (vt : CBall) (p : IvP) : Option Int :=
  let nv := normHi vt
  if neg then
    if reConjHi P vt p.gz + (mulU P nv p.dG : Nat) ≤ 0 then some (reConjHi P vt p.sz + (mulU P nv p.dS : Nat))
    else none
  else
    if 0 ≤ reConjLo P vt p.gz - (mulU P nv p.dG : Nat) then some (reConjLo P vt p.sz - (mulU P nv p.dS : Nat))
    else none

/-- The larger (W1) or smaller (empty) of two bounds. -/
@[inline] def comb (neg : Bool) (a b : Int) : Int := if neg then max a b else min a b

/-- Bisection of a piece. -/
def ivRec (c : Cfg) (E : EllB) (as : List (Q × Q)) (mSum : Nat) (neg : Bool) (vt : CBall) :
    Nat → Nat → Nat → Nat → Option Int
  | 0, n0, n1, e => (ivPiece c E as mSum n0 n1 e).bind (ivOne c.P neg vt)
  | fuel + 1, n0, n1, e => ((ivPiece c E as mSum n0 n1 e).bind (ivOne c.P neg vt)).orElse fun _ =>
      (ivRec c E as mSum neg vt fuel (2 * n0) (n0 + n1) (e + 1)).bind fun b1 =>
        (ivRec c E as mSum neg vt fuel (n0 + n1) (2 * n1) (e + 1)).map fun b2 => comb neg b1 b2

/-- A precomputed piece, bisected (depth `dS`) if its test fails. -/
def ivTry (c : Cfg) (E : EllB) (as : List (Q × Q)) (mSum : Nat) (neg : Bool) (vt : CBall) (dS : Nat) (p : IvP) :
    Option Int :=
  (ivOne c.P neg vt p).orElse fun _ =>
    match dS with
    | 0 => none
    | d + 1 => (ivRec c E as mSum neg vt d (2 * p.n0) (p.n0 + p.n1) (p.e + 1)).bind fun b1 =>
        (ivRec c E as mSum neg vt d (p.n0 + p.n1) (2 * p.n1) (p.e + 1)).map fun b2 => comb neg b1 b2

/-- All pieces of a tube. -/
def ivAll (c : Cfg) (E : EllB) (as : List (Q × Q)) (mSum : Nat) (neg : Bool) (vt : CBall) (dS : Nat) :
    List IvP → Option Int
  | [] => none
  | [p] => ivTry c E as mSum neg vt dS p
  | p :: ps => (ivTry c E as mSum neg vt dS p).bind fun b => (ivAll c E as mSum neg vt dS ps).map (comb neg b)

/-- A piece `[n₀, n₁] / 2^e` of a tube for the functions of `t`: the table of its midpoint, the disc factors
`dz`, `yz` and the disc radius `ρ`. -/
structure TPc where
  T : PtT
  dz : Nat
  yz : Nat
  n0 : Nat
  n1 : Nat
  e : Nat
  rho : Nat

/-- The data of a tube at a leaf: its tile, atoms, `mSum ≥ Σ m_k`, the `2^lS` pieces for the sign and bound
conditions, and per level `l < nL` the `2^(lT + l)` pieces for the functions of `t`. -/
structure TubeC where
  E : EllB
  as : List (Q × Q)
  mSum : Nat
  ps : List IvP
  ts : List (List TPc)

/-- A piece of a tube for the functions of `t`. -/
def tPiece (g : Glob) (E : EllB) (n0 n1 e : Nat) : Option TPc :=
  (ellPt g.cfg E (midB g.P n0 n1 e)).bind fun z => (ellRad g.cfg E n0 n1 e).bind fun rho =>
    (ptT g.cfg g.D z).bind fun T => (dzOf g.cfg z rho).map fun dz => ⟨T, dz.1, dz.2, n0, n1, e, rho⟩

/-- The `i`-th of `2^l` equal pieces of `[q₀, q₁] / 2^EQ`, as `[n₀, n₁] / 2^(EQ + l)`. -/
@[inline] def subPc (q0 q1 l i : Nat) : Nat × Nat := (q0 * 2 ^ l + i * (q1 - q0), q0 * 2 ^ l + (i + 1) * (q1 - q0))

def tubeC (gn : GlobN) (tb : TubeD) : Option TubeC :=
  let g := gn.g
  (tileOf g tb.ti).bind fun E => (atomsOK tb.as).bind fun mm =>
    let mSum := Ball.cdiv (mm.1.toNat * 2 ^ g.P) mm.2
    ((List.range (2 ^ gn.lS)).mapM fun i =>
        ivPiece g.cfg E tb.as mSum (subPc tb.q0 tb.q1 gn.lS i).1 (subPc tb.q0 tb.q1 gn.lS i).2 (g.EQ + gn.lS)).bind
      fun ps =>
        ((List.range gn.nL).mapM fun l => (List.range (2 ^ (gn.lT + l))).mapM fun i =>
            tPiece g E (subPc tb.q0 tb.q1 (gn.lT + l) i).1 (subPc tb.q0 tb.q1 (gn.lT + l) i).2 (g.EQ + gn.lT + l)).map
          fun ts => ⟨E, tb.as, mSum, ps, ts⟩

/-- The sum over the tubes of the bound terms with the `ε` terms (`neg = true`: upper bound of
`Σ sup Re(v̄t S) + |vt| ε`; `neg = false`: lower bound of `Σ inf Re(v̄t S) - |vt| ε`); zero multipliers count `0`. -/
def ivSum (gn : GlobN) (neg : Bool) : List TubeC → List (Int × Int) → Option Int
  | [], [] => some 0
  | tc :: tcs, vt :: vts =>
    (if vt.1 = 0 ∧ vt.2 = 0 then some 0
     else (ivAll gn.g.cfg tc.E tc.as tc.mSum neg (intC gn.g.P vt) gn.dS tc.ps).map fun (b : Int) =>
       if neg then b + ((mulU gn.g.P (normHi (intC gn.g.P vt)) (epsHi gn) : Nat) : Int)
       else b - ((mulU gn.g.P (normHi (intC gn.g.P vt)) (epsHi gn) : Nat) : Int)).bind fun (b : Int) =>
      (ivSum gn neg tcs vts).map fun s => b + s
  | _, _ => none

/-- The groups of the tubes in the functions of `t` (level `l`: the `2^(lT + l)` pieces): coefficient `-conj(vt)` (W1)
or `conj(vt)` (empty leaf). -/
def ivGroups (P : Nat) (neg : Bool) (l : Nat) : List TubeC → List (Int × Int) → List (List TermD)
  | tc :: tcs, vt :: vts =>
    if vt.1 = 0 ∧ vt.2 = 0 then ivGroups P neg l tcs vts
    else ((tc.ts.getD l []).map fun x =>
        termD (if neg then CBall.neg (CBall.conj (intC P vt)) else CBall.conj (intC P vt)) x.T (x.dz, x.yz)) ::
      ivGroups P neg l tcs vts
  | _, _ => []

/-- The levels tried: `[0]` without tubes, else `[0, …, nL - 1]`. -/
def levels (gn : GlobN) (tcs : List TubeC) : List Nat := if tcs.isEmpty then [0] else List.range gn.nL

/-! ## W1 records -/

/-- The W1 condition on the piece of a tile arc, with the bound terms `ivB` and the groups `gs` of the tubes. -/
def taPieceOKN (g : Glob) (A : ACtx) (r' tn td : Nat) (u v : CBall) (yts : List TermS) (hiY ivB : Int)
    (gs : List (List TermD)) (pd : Piece3) (T : PtT) (dz : Nat × Nat) : Bool :=
  decide (0 < aTA3 g A r' u v hiY pd - ivB) &&
    tboundD g.P g.D (termD (CBall.conj u) T dz :: toD (termOf (CBall.neg (CBall.conj v)) A.zT) :: yts.map toD) gs
      ((((aTA3 g A r' u v hiY pd - ivB).toNat * td / tn : Nat) : Int))

def checkTAPieceN (g : Glob) (A : ACtx) (E : EllB) (r' tn td : Nat) (u v : CBall) (yts : List TermS)
    (hiY ivB : Int) (gs : List (List TermD)) (n0 n1 e : Nat) : Bool :=
  (piece3 g.cfg E n0 n1 e).any fun pd => (ptT g.cfg g.D pd.z).any fun T => (dzOf g.cfg pd.z pd.rho).any fun dz =>
    taPieceOKN g A r' tn td u v yts hiY ivB gs pd T dz

def checkTAN (g : Glob) (A : ACtx) (E : EllB) (r' tn td : Nat) (u v : CBall) (yts : List TermS)
    (hiY ivB : Int) (gs : List (List TermD)) : Nat → Nat → Nat → Nat → Bool
  | 0, n0, n1, e => checkTAPieceN g A E r' tn td u v yts hiY ivB gs n0 n1 e
  | fuel + 1, n0, n1, e => checkTAPieceN g A E r' tn td u v yts hiY ivB gs n0 n1 e ||
      (checkTAN g A E r' tn td u v yts hiY ivB gs fuel (2 * n0) (n0 + n1) (e + 1) &&
       checkTAN g A E r' tn td u v yts hiY ivB gs fuel (n0 + n1) (2 * n1) (e + 1))

/-- One W1 record of a leaf with `m` pins and `K` tubes: `q₁`, `u`, `v`, `y_1 … y_m`, `vt_1 … vt_K`, the rest. -/
def rdTAN (m K s : Nat) : Nat × (Int × Int) × (Int × Int) × List (Int × Int) × List (Int × Int) × Nat :=
  let (q1, s) := rdNat s
  let (u, s) := rdPair s
  let (v, s) := rdPair s
  let (ys, s) := rdPairs m s
  let (vts, s) := rdPairs K s
  (q1, u, v, ys, vts, s)

/-- The checks of one W1 record on `[q₀, q₁]`. -/
def taOKN (gn : GlobN) (A : ACtx) (E : EllB) (r' tn td : Nat) (B : List Box4) (tcs : List TubeC) (q0 q1 : Nat)
    (u v : Int × Int) (ys vts : List (Int × Int)) : Bool :=
  let g := gn.g
  decide (q0 < q1) && decide (q1 ≤ 2 ^ g.EQ) && (decide (reConjHi g.P (intC g.P v) A.Sc ≤ 0) || v == (0, 0)) &&
    (ivSum gn true tcs vts).any fun ivB => (levels gn tcs).any fun l =>
      checkTAN g A E r' tn td (intC g.P u) (intC g.P v) (yTerms g.P true A.pins ys) (sumBox true B ys) ivB
        (ivGroups g.P true l tcs vts) g.dT q0 q1 g.EQ

/-- The tile arcs from `q` to `1`: a hard arc `[q, b]` at the head of `hs`, or else the next W1 record (`N` left in
`s`); at `q = 1` nothing may be left. -/
def walkTA (gn : GlobN) (A : ACtx) (E : EllB) (r' tn td : Nat) (B : List Box4) (tcs : List TubeC) :
    Nat → Nat → Nat → Nat → List (Nat × Nat) → Bool
  | 0, _, _, _, _ => false
  | fuel + 1, N, q, s, hs =>
    if q = 2 ^ gn.g.EQ then N == 0 && hs.isEmpty
    else
      match hs with
      | (a, b) :: hs' =>
        if a = q then decide (q < b) && decide (b ≤ 2 ^ gn.g.EQ) && walkTA gn A E r' tn td B tcs fuel N b s hs'
        else walkW1 gn A E r' tn td B tcs fuel N q s hs
      | [] => walkW1 gn A E r' tn td B tcs fuel N q s hs
where
  walkW1 (gn : GlobN) (A : ACtx) (E : EllB) (r' tn td : Nat) (B : List Box4) (tcs : List TubeC) (fuel N q s : Nat)
      (hs : List (Nat × Nat)) : Bool :=
    match N with
    | 0 => false
    | N' + 1 =>
      let r := rdTAN A.pins.length tcs.length s
      taOKN gn A E r' tn td B tcs q r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 &&
        walkTA gn A E r' tn td B tcs fuel N' r.1 r.2.2.2.2.2 hs

/-! ## Leaves -/

/-- `ŵ_rep` meets the tube: `q_r ∈ [q₀, q₁]`, `μ_r ≥ 0`, `|ŵ_rep(z) - S(z) - μ_r G_base(z)| ≤ ε` at `z = z(q_r)`. -/
def tubeRepOK (gn : GlobN) (as : List (Q × Q)) (tb : TubeD) (qm : Q × Q) : Bool :=
  let g := gn.g
  decide (0 < qm.1.d) && decide (0 < qm.2.d) && decide (0 ≤ qm.2.n) &&
    decide ((tb.q0 : Int) * qm.1.d ≤ qm.1.n * 2 ^ g.EQ) && decide (qm.1.n * 2 ^ g.EQ ≤ (tb.q1 : Int) * qm.1.d) &&
    (tileOf g tb.ti).any fun Et => (ellPt g.cfg Et (qm.1.ball g.P)).any fun z => (cS g.cfg z).any fun sz =>
      (sumK g.cfg z as).any fun w => (sumK g.cfg z tb.as).any fun w0 =>
        decide (normHi (CBall.sub (CBall.sub w sz) (CBall.mulR g.P (qm.2.ball g.P) (CBall.sub sz w0))) ≤ epsLo gn)

/-- The checks of a W leaf, except its children: `τ ≤ τ_N`, `w_rep` in the node set, the odd winding number of
`G_{w_rep}` along the tile, and the tile arcs. -/
def witLocalN (gn : GlobN) (A : ACtx) (tubes : List TubeD) (bx : List (Nat × Nat × Nat)) (h : WHdr) (n dat : Nat)
    (hards : List (Nat × Nat)) : Bool :=
  let g := gn.g
  (tileOf g h.ti).any fun E => (atomsOK h.as).any fun mm =>
    decide (0 < h.tw.n) && decide (0 < h.tw.d) && decide (g.tau.n * h.tw.d ≤ h.tw.n * g.tau.d) &&
    decide (mm.1 * h.tw.d ≤ h.tw.n * mm.2) && decide (0 < h.sg.d) && decide ((h.sg.d : Int) ≤ h.sg.n) &&
    decide (h.mus.length = tubes.length) && (tubes.zip h.mus).all (fun x => tubeRepOK gn h.as x.1 x.2) &&
    (rBound g A.E1 h.tw.n.toNat h.tw.d A.s0 A.s1 A.sc A.zc A.Sc A.S1c h.rX).any fun r' =>
      (sumK g.cfg A.zc h.as).any fun wz =>
        decide (A.r ≤ r') && decide (normHi (CBall.sub wz (CBall.mulR g.P (h.sg.ball g.P) A.Sc)) ≤ r') &&
        pinsIn g.cfg h.as A.pins (pinBoxes g.P A.pins bx) &&
        windOdd g E h.as (Ball.cdiv (mm.1.toNat * 2 ^ g.P) mm.2) &&
        (tubes.mapM (tubeC gn)).any fun tcs =>
          walkTA gn A E r' h.tw.n.toNat h.tw.d (pinBoxes g.P A.pins bx) tcs (n + hards.length + 1) n 0 dat hards

/-- An empty leaf: `v`, `y_j`, `vt_k` from `dat`; `Re(v̄ S(z_c)) ≥ 0`, the signs on the tubes, and
`τ_N max(0, ψ) < Re(v̄ S(z_c)) - |v| r' + Σ min_{Q_j} Re(ȳ_j x) + Σ (inf Re(v̄t S) - |vt| ε)`. -/
def emptyN (gn : GlobN) (A : ACtx) (tubes : List TubeD) (bx : List (Nat × Nat × Nat)) (tw : Q) (rX dat : Nat) :
    Bool :=
  let g := gn.g
  let B := pinBoxes g.P A.pins bx
  let v := (rdPair dat).1
  let ys := (rdPairs A.pins.length (rdPair dat).2).1
  let vts := (rdPairs tubes.length (rdPairs A.pins.length (rdPair dat).2).2).1
  decide (0 < tw.n) && decide (0 < tw.d) && decide (g.tau.n * tw.d ≤ tw.n * g.tau.d) &&
    (decide (0 ≤ reConjLo g.P (intC g.P v) A.Sc) || v == (0, 0)) &&
    (rBound g A.E1 tw.n.toNat tw.d A.s0 A.s1 A.sc A.zc A.Sc A.S1c rX).any fun r' =>
      decide (A.r ≤ r') && (tubes.mapM (tubeC gn)).any fun tcs => (ivSum gn false tcs vts).any fun ivB =>
        decide (0 < reConjLo g.P (intC g.P v) A.Sc - (mulU g.P (normHi (intC g.P v)) r' : Nat) + sumBox false B ys + ivB) &&
          (levels gn tcs).any fun l => tboundD g.P g.D ((termOf (CBall.conj (intC g.P v)) A.zT :: yTerms g.P false A.pins ys).map toD)
            (ivGroups g.P false l tcs vts)
            ((((reConjLo g.P (intC g.P v) A.Sc - (mulU g.P (normHi (intC g.P v)) r' : Nat) + sumBox false B ys +
                ivB).toNat * tw.d / tw.n.toNat : Nat) : Int))

/-! ## Trees and arcs -/

/-- The tree check (`ext` subtrees are separate statements). -/
def checkN (gn : GlobN) (A : ACtx) : Nat → List TubeD → List (Nat × Nat × Nat) → NTree → Bool
  | 0, _, _, _ => false
  | _ + 1, tubes, bx, .empty tw rX dat => emptyN gn A tubes bx tw rX dat
  | fuel + 1, tubes, bx, .wit h n dat hards kids =>
    witLocalN gn A tubes bx h n dat hards && decide (kids.length = hards.length) &&
      (hards.zip kids).all fun x => checkN gn A fuel (tubes ++ [⟨h.ti, x.1.1, x.1.2, h.as⟩]) bx x.2
  | fuel + 1, tubes, bx, .split j c0 c1 c2 c3 =>
    decide (j < bx.length) &&
      checkN gn A fuel tubes (bx.set j (kid (bx.getD j (0, 0, 0)) 0)) c0 &&
      checkN gn A fuel tubes (bx.set j (kid (bx.getD j (0, 0, 0)) 1)) c1 &&
      checkN gn A fuel tubes (bx.set j (kid (bx.getD j (0, 0, 0)) 2)) c2 &&
      checkN gn A fuel tubes (bx.set j (kid (bx.getD j (0, 0, 0)) 3)) c3
  | fuel + 1, tubes, bx, .ivsplit k qm lo hi =>
    match tubes[k]? with
    | some tb => decide (tb.q0 < qm) && decide (qm < tb.q1) &&
        checkN gn A fuel (tubes.set k { tb with q1 := qm }) bx lo &&
        checkN gn A fuel (tubes.set k { tb with q0 := qm }) bx hi
    | none => false
  | _ + 1, _, _, .ext => true

/-- A subtree with the tubes `tubes` and the boxes `bx`, in the context of the arc `(s₀, s₁, s_c, pins, Rs, rX)`. -/
def checkSubN (gn : GlobN) (s0 s1 sc : Nat) (pins : List (Q × Q)) (Rs : List Q) (rX : Nat) (tubes : List TubeD)
    (bx : List (Nat × Nat × Nat)) (t : NTree) : Bool :=
  hHead gn.g s0 s1 sc pins Rs && (arcCtx gn.g s0 s1 sc pins Rs rX).any fun A => checkN gn A gn.fuel tubes bx t

def checkArcN (gn : GlobN) : ArcN → Bool
  | .old a => checkArc gn.g a
  | .N s0 s1 sc pins Rs rX t => checkSubN gn s0 s1 sc pins Rs rX [] (pins.map fun _ => (0, 0, 0)) t

def ArcN.s0 : ArcN → Nat
  | .old a => a.s0
  | .N s0 _ _ _ _ _ _ => s0

def ArcN.s1 : ArcN → Nat
  | .old a => a.s1
  | .N _ s1 _ _ _ _ _ => s1

/-- The arcs `[s₀, s₁], [s₁, s₂], …` (`s = n / 2^ES`) run consecutively from `x` to `1/2`: the upper half of `T₁`;
the lower half is covered by the mirror arcs (`C64Chk.main_of_checksN_mirror`). -/
def coverHalfOK (g : Glob) : Nat → List (Nat × Nat) → Bool
  | _, [] => false
  | x, [(a, b)] => x == a && 2 * b == 2 ^ g.ES
  | x, (a, b) :: rest => x == a && coverHalfOK g b rest

/-- The parameters of a nested certificate. -/
def globParamsN (gn : GlobN) : Bool :=
  globParams gn.g && decide (0 < gn.eps.d) && decide (0 ≤ gn.eps.n) && decide (1000 * gn.eps.n ≤ gn.eps.d) &&
    decide (gn.g.EQ + gn.lS + gn.dS + 1 ≤ gn.g.P) && decide (gn.g.EQ + gn.lT + gn.nL ≤ gn.g.P)

def checkGlobN (gn : GlobN) : Bool := globParamsN gn && windOdd gn.g (T1B gn.g) [] 0

end C64Chk
