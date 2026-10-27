import C64Core.Nest
import C64K.KChk
import C64K.KPieceGood

/-!
# The nested checker on sign-magnitude balls (kernel layer, core Lean only)

This file mirrors `C64Core/Nest.lean` (namespace `C64Chk`) function by function on `KIval.KBall` / `KNum.KCBall`, in the
style of `C64K.KChk`: natural-number primitives, branching by `cond`, signed pairs `SI` for the integers computed from
balls.  The data types of the nested certificates (`TubeD`, `WHdr`, `NTree`, `ArcN`, `GlobN`) and the data-only
functions (`rdTAN`, `atomsOK`, `kid`, `globParamsN`, `coverHalfOK`) are those of `C64Chk`; the exact rational checks of a
leaf on its data (`decide (…)` on the integers of the data) are kept as they are.  Where `Nest` calls a function of
the three-level checker, the port calls the corresponding function of `C64K.KChk`.

Deviations from a literal transcription, each of them exact (`C64K.KNestSim`):
* `Ball.mulS`, `CBall.mulS`, `reMulS` (the products computed with shifts) are `KBall.mul`, `KCBall.mul`, `reMul`
  (`Ball.mulS = Ival.Ball.mul`);
* the pair `walkTA` / `walkTA.walkW1` (mutual, hence well-founded recursion) is one function whose recursion is
  structural in the fuel: `walkW1` takes the recursive call as an argument;
* the cell centres `tn` of `cellsD` are signed pairs;
* under the cheap guard `tsLazyOK` (C64K.KPieceGood), `tubeC` builds the pieces for the functions of `t` lazily
  (`tsLazy`, `Option.getD` per piece) instead of through `mapM`: the kernel computes a piece only when a test reads it.
  Under the guard every piece is `some` (`C64KChk.tPiece_isSome`), so the value is the same.

The top-level functions are `checkSubNK`, `checkArcNK` and `checkGlobNK`; `C64K.KNestSim` proves that they are equal to
`C64Chk.checkSubN`, `C64Chk.checkArcN` and `C64Chk.checkGlobN` for all inputs.
-/

namespace C64KChk

open KIval KIval.KBall KNum C64Chk

/-! ## Signed integers and natural numbers: maximum and minimum -/

/-- `max a b` (as `Int.max`: `if a ≤ b then b else a`). -/
@[inline] def SI.max (a b : SI) : SI := cond (SI.le a b) b a

/-- `min a b` (as `Int.min`: `if a ≤ b then a else b`). -/
@[inline] def SI.min (a b : SI) : SI := cond (SI.le a b) a b

/-- `min a b` on `Nat`. -/
@[inline] def nmin (a b : Nat) : Nat := cond (Nat.ble a b) a b

/-- `⌈ε 2^P⌉` and `⌊ε 2^P⌋`. -/
def epsHi (gn : GlobN) : Nat := KBall.cdiv (Nat.mul gn.eps.n.toNat (Nat.pow 2 gn.g.P)) gn.eps.d
def epsLo (gn : GlobN) : Nat := Nat.div (Nat.mul gn.eps.n.toNat (Nat.pow 2 gn.g.P)) gn.eps.d

/-! ## Bounds in `t` with disc terms -/

/-- A term `Re(c K_t(z))` for `z` in a disc around the point of a table, as `C64Chk.TermD`. -/
structure TermD where
  W : KCBall
  w : KCBall
  st : List (KCBall × KCBall)
  m2 : Nat
  dz : Nat
  yz : Nat

def termD (cf : KCBall) (T : PtT) (dy : Nat × Nat) : TermD := ⟨cf, T.w, T.st, T.mz, dy.1, dy.2⟩

def toD (T : TermS) : TermD := ⟨T.W, T.w, T.st, T.m2, 0, 0⟩

/-- An upper bound of `|W|`: `max + ⌈min / 2⌉`. -/
@[inline] def absW (W : KCBall) : Nat :=
  Nat.add (nmax (absHi W.re) (absHi W.im)) (Nat.div (Nat.add (nmin (absHi W.re) (absHi W.im)) 1) 2)

/-- The disc correction of a term on the cell with centre `tn / 2^e`, as `C64Chk.corrD` (`|tn|` is `tn.m`). -/
def corrD (P e : Nat) (tn : SI) (T : TermD) : Nat :=
  Nat.add (KBall.cdiv (Nat.mul (mulU P (absW T.W) T.dz) (Nat.add tn.m 1)) (Nat.pow 2 e))
    (KBall.cdiv (Nat.mul (mulU P (mulU P (absW T.W) T.dz) T.yz) (Nat.add tn.m 1)) (Nat.pow 2 (Nat.mul 2 e)))

def sumTermsD (P e : Nat) (tn : SI) : List TermD → KBall × KBall × Nat × Nat
  | [] => (⟨false, 0, 0⟩, ⟨false, 0, 0⟩, 0, 0)
  | T :: ts =>
    let r := sumTermsD P e tn ts
    (KBall.add T.W.re r.1, KBall.add (reMul P T.W T.w) r.2.1, Nat.add (mulU P (absW T.W) T.m2) r.2.2.1,
      Nat.add (corrD P e tn T) r.2.2.2)

def groupB (P e : Nat) (tn : SI) : List TermD → Option (SI × KBall × Nat)
  | [] => none
  | [T] => some (SI.add (hiS T.W.re) (SI.ofNat (corrD P e tn T)), reMul P T.W T.w, mulU P (absW T.W) T.m2)
  | T :: ts => (groupB P e tn ts).map fun b =>
      (SI.max (SI.add (hiS T.W.re) (SI.ofNat (corrD P e tn T))) b.1, hullB (reMul P T.W T.w) b.2.1,
        nmax (mulU P (absW T.W) T.m2) b.2.2)

def groupsB (P e : Nat) (tn : SI) : List (List TermD) → Option (SI × KBall × Nat)
  | [] => some (SI.ofNat 0, ⟨false, 0, 0⟩, 0)
  | G :: gs => (groupB P e tn G).bind fun b => (groupsB P e tn gs).map fun s =>
      (SI.add b.1 s.1, KBall.add b.2.1 s.2.1, Nat.add b.2.2 s.2.2)

def cellOKD (P : Nat) (ts : List TermD) (gs : List (List TermD)) (e : Nat) (tn : SI) (target : SI) : Bool :=
  let r := sumTermsD P e tn ts
  Nat.ble 5 e &&
    (groupsB P e tn gs).any fun b =>
      SI.lt (SI.add (SI.add (SI.add (SI.add (hiS r.1) b.1)
          (SI.ofNat (KBall.cdiv (absHi (KBall.add r.2.1 b.2.1)) (Nat.pow 2 e))))
          (SI.ofNat (KBall.cdiv (Nat.add r.2.2.1 b.2.2) (Nat.pow 2 (Nat.add (Nat.mul 2 e) 1)))))
          (SI.ofNat r.2.2.2)) target

def stepD (P : Nat) (down : Bool) (T : TermD) : TermD :=
  match T.st with
  | [] => T
  | (kp, km) :: rest => ⟨KCBall.mul P T.W (cond down km kp), T.w, rest, T.m2, T.dz, T.yz⟩

/-- Adaptive cells with centres `tn / 2^e`. -/
def cellsD (P : Nat) (target : SI) : Nat → Nat → Nat → SI → List TermD → List (List TermD) → Bool
  | 0, _, _, _, _, _ => false
  | fuel + 1, skip, e, tn, ts, gs =>
    (cond (Nat.beq skip 0) (cellOKD P ts gs e tn target) false) ||
      (cellsD P target fuel (Nat.sub skip 1) (Nat.add e 1) (SI.sub (SI.mul (SI.ofNat 2) tn) (SI.ofNat 1))
          (ts.map (stepD P true)) (gs.map (·.map (stepD P true))) &&
       cellsD P target fuel (Nat.sub skip 1) (Nat.add e 1) (SI.add (SI.mul (SI.ofNat 2) tn) (SI.ofNat 1))
          (ts.map (stepD P false)) (gs.map (·.map (stepD P false))))

def tboundD (P D : Nat) (ts : List TermD) (gs : List (List TermD)) (target : SI) : Bool :=
  cellsD P target (Nat.add D 1) 4 1 (SI.ofNat 0) ts gs

/-- The disc factors `(2π ρ e^{π ρ}, 2π |Im z| e^{π |Im z| / 16})`. -/
def dzOf (c : Cfg) (z : KCBall) (rho : Nat) : Option (Nat × Nat) :=
  (expPiHi c rho).bind fun ex => (expPiHi c (KBall.cdiv (absHi z.im) 16)).map fun ey =>
    (mulU c.P (Nat.mul 2 (mulU c.P (piHi c.P) rho)) ex, mulU c.P (Nat.mul 2 (mulU c.P (piHi c.P) (absHi z.im))) ey)

/-! ## Pieces with third-order bounds of `S` -/

/-- `(S(z), S'(z), S''(z))`. -/
def cSS2 (c : Cfg) (z : KCBall) : Option (KCBall × KCBall × KCBall) :=
  (ccosSinPi c z).bind fun cs =>
    let pz := KCBall.mulR c.P (piB c.P) z
    (KNum.cdiv c.P cs.2 pz).bind fun s =>
    (KNum.cdiv c.P (KCBall.sub (KCBall.mul c.P pz cs.1) cs.2) (KCBall.mul c.P pz z)).bind fun s1 =>
    (KNum.cdiv c.P (KCBall.sub (KCBall.mul c.P (KCBall.sub ⟨KBall.ofInt c.P false 2, ⟨false, 0, 0⟩⟩
          (KCBall.mul c.P pz pz)) cs.2) (KCBall.mul c.P (KCBall.add pz pz) cs.1))
        (KCBall.mul c.P pz (KCBall.mul c.P z z))).map fun s2 => (s, s1, s2)

structure Piece3 where
  z : KCBall
  rho : Nat
  sz : KCBall
  s1 : KCBall
  s2 : KCBall
  eY : Nat
  dS : Nat

/-- `|S''(z)| ρ² / 2 + π³ eY ρ³ / 18`. -/
def d23 (P : Nat) (s2 : KCBall) (rho eY : Nat) : Nat :=
  Nat.add (KBall.cdiv (Nat.mul (Nat.mul (normHi s2) rho) rho) (Nat.mul 2 (Nat.pow 2 (Nat.mul 2 P))))
    (KBall.cdiv (Nat.mul (Nat.mul (Nat.pow (piHi P) 3) eY) (Nat.pow rho 3)) (Nat.mul 18 (Nat.pow 2 (Nat.mul 6 P))))

def piece3 (c : Cfg) (E : EllB) (n0 n1 e : Nat) : Option Piece3 :=
  (ellPt c E (midB c.P n0 n1 e)).bind fun z =>
  (ellRad c E n0 n1 e).bind fun rho =>
  (cSS2 c z).bind fun ss =>
  (expPiHi c (Nat.add (absHi z.im) rho)).map fun eY =>
    ⟨z, rho, ss.1, ss.2.1, ss.2.2, eY, Nat.add (mulU c.P (normHi ss.2.1) rho) (d23 c.P ss.2.2 rho eY)⟩

def aLow3 (P : Nat) (u : KCBall) (p : Piece3) : SI := SI.sub (reConjLo P u p.sz) (SI.ofNat (mulU P (normHi u) p.dS))

def aTA3 (g : Glob) (A : ACtx) (r' : Nat) (u v : KCBall) (hiY : SI) (p : Piece3) : SI :=
  SI.sub (SI.sub (SI.sub (aLow3 g.P u p) (reConjHi g.P v A.Sc)) (SI.ofNat (mulU g.P (normHi v) r'))) hiY

/-- `(Σ m_k K_{t_k}(z), Σ m_k (-2πi t_k) K_{t_k}(z))`. -/
def sumK1 (c : Cfg) (z : KCBall) : List (Q × Q) → Option (KCBall × KCBall)
  | [] => some (⟨⟨false, 0, 0⟩, ⟨false, 0, 0⟩⟩, ⟨⟨false, 0, 0⟩, ⟨false, 0, 0⟩⟩)
  | a :: as => (ckt c (qBall c.P a.1) z).bind fun k => (sumK1 c z as).map fun s =>
      let mk := KCBall.mulR c.P (qBall c.P a.2) k
      let tp := KBall.mulInt false 2 (KBall.mul c.P (piB c.P) (qBall c.P a.1))
      (KCBall.add mk s.1, KCBall.add ⟨KBall.mul c.P tp mk.im, KBall.neg (KBall.mul c.P tp mk.re)⟩ s.2)

/-! ## Interval tubes -/

structure IvP where
  n0 : Nat
  n1 : Nat
  e : Nat
  sz : KCBall
  dS : Nat
  gz : KCBall
  dG : Nat

def ivPiece (c : Cfg) (E : EllB) (as : List (Q × Q)) (mSum : Nat) (n0 n1 e : Nat) : Option IvP :=
  (piece3 c E n0 n1 e).bind fun p => (sumK1 c p.z as).map fun w =>
    ⟨n0, n1, e, p.sz, p.dS, KCBall.sub p.sz w.1,
     Nat.add (Nat.add (mulU c.P (normHi (KCBall.sub p.s1 w.2)) p.rho) (d23 c.P p.s2 p.rho p.eY))
       (KBall.cdiv (Nat.mul (Nat.mul (Nat.mul (Nat.mul mSum (Nat.pow (piHi c.P) 2)) p.eY) p.rho) p.rho)
         (Nat.mul 2 (Nat.pow 2 (Nat.mul 5 c.P))))⟩

def ivOne (P : Nat) (neg : Bool) (vt : KCBall) (p : IvP) : Option SI :=
  let nv := normHi vt
  cond neg
    (cond (SI.le (SI.add (reConjHi P vt p.gz) (SI.ofNat (mulU P nv p.dG))) (SI.ofNat 0))
      (some (SI.add (reConjHi P vt p.sz) (SI.ofNat (mulU P nv p.dS)))) none)
    (cond (SI.le (SI.ofNat 0) (SI.sub (reConjLo P vt p.gz) (SI.ofNat (mulU P nv p.dG))))
      (some (SI.sub (reConjLo P vt p.sz) (SI.ofNat (mulU P nv p.dS)))) none)

/-- The larger (W1) or smaller (empty) of two bounds. -/
@[inline] def comb (neg : Bool) (a b : SI) : SI := cond neg (SI.max a b) (SI.min a b)

def ivRec (c : Cfg) (E : EllB) (as : List (Q × Q)) (mSum : Nat) (neg : Bool) (vt : KCBall) :
    Nat → Nat → Nat → Nat → Option SI
  | 0, n0, n1, e => (ivPiece c E as mSum n0 n1 e).bind (ivOne c.P neg vt)
  | fuel + 1, n0, n1, e => ((ivPiece c E as mSum n0 n1 e).bind (ivOne c.P neg vt)).orElse fun _ =>
      (ivRec c E as mSum neg vt fuel (Nat.mul 2 n0) (Nat.add n0 n1) (Nat.add e 1)).bind fun b1 =>
        (ivRec c E as mSum neg vt fuel (Nat.add n0 n1) (Nat.mul 2 n1) (Nat.add e 1)).map fun b2 => comb neg b1 b2

def ivTry (c : Cfg) (E : EllB) (as : List (Q × Q)) (mSum : Nat) (neg : Bool) (vt : KCBall) (dS : Nat) (p : IvP) :
    Option SI :=
  (ivOne c.P neg vt p).orElse fun _ =>
    match dS with
    | 0 => none
    | d + 1 => (ivRec c E as mSum neg vt d (Nat.mul 2 p.n0) (Nat.add p.n0 p.n1) (Nat.add p.e 1)).bind fun b1 =>
        (ivRec c E as mSum neg vt d (Nat.add p.n0 p.n1) (Nat.mul 2 p.n1) (Nat.add p.e 1)).map fun b2 => comb neg b1 b2

def ivAll (c : Cfg) (E : EllB) (as : List (Q × Q)) (mSum : Nat) (neg : Bool) (vt : KCBall) (dS : Nat) :
    List IvP → Option SI
  | [] => none
  | [p] => ivTry c E as mSum neg vt dS p
  | p :: ps => (ivTry c E as mSum neg vt dS p).bind fun b => (ivAll c E as mSum neg vt dS ps).map (comb neg b)

structure TPc where
  T : PtT
  dz : Nat
  yz : Nat
  n0 : Nat
  n1 : Nat
  e : Nat
  rho : Nat

structure TubeC where
  E : EllB
  as : List (Q × Q)
  mSum : Nat
  ps : List IvP
  ts : List (List TPc)

def tPiece (g : Glob) (E : EllB) (n0 n1 e : Nat) : Option TPc :=
  (ellPt ⟨g.P, g.n, g.k⟩ E (midB g.P n0 n1 e)).bind fun z => (ellRad ⟨g.P, g.n, g.k⟩ E n0 n1 e).bind fun rho =>
    (ptT ⟨g.P, g.n, g.k⟩ g.D z).bind fun T => (dzOf ⟨g.P, g.n, g.k⟩ z rho).map fun dz =>
      ⟨T, dz.1, dz.2, n0, n1, e, rho⟩

/-- The `i`-th of `2^l` equal pieces of `[q₀, q₁] / 2^EQ`. -/
@[inline] def subPc (q0 q1 l i : Nat) : Nat × Nat :=
  (Nat.add (Nat.mul q0 (Nat.pow 2 l)) (Nat.mul i (Nat.sub q1 q0)),
   Nat.add (Nat.mul q0 (Nat.pow 2 l)) (Nat.mul (Nat.add i 1) (Nat.sub q1 q0)))

/-- A placeholder piece (never read: under `tsLazyOK` every piece is `some`). -/
def tpcNone : TPc := ⟨⟨[], ⟨⟨false, 0, 0⟩, ⟨false, 0, 0⟩⟩, 0⟩, 0, 0, 0, 0, 0, 0⟩

/-- The pieces for the functions of `t`, one list per level, each piece computed only when it is read. -/
def tsLazy (gn : GlobN) (tb : TubeD) (E : EllB) : List (List TPc) :=
  (List.range gn.nL).map fun l => (List.range (Nat.pow 2 (Nat.add gn.lT l))).map fun i =>
    (tPiece gn.g E (subPc tb.q0 tb.q1 (Nat.add gn.lT l) i).1 (subPc tb.q0 tb.q1 (Nat.add gn.lT l) i).2
      (Nat.add (Nat.add gn.g.EQ gn.lT) l)).getD tpcNone

def tubeC (gn : GlobN) (tb : TubeD) : Option TubeC :=
  (tileOf gn.g tb.ti).bind fun E => (atomsOK tb.as).bind fun mm =>
    let mSum := KBall.cdiv (Nat.mul mm.1.toNat (Nat.pow 2 gn.g.P)) mm.2
    ((List.range (Nat.pow 2 gn.lS)).mapM fun i =>
        ivPiece ⟨gn.g.P, gn.g.n, gn.g.k⟩ E tb.as mSum (subPc tb.q0 tb.q1 gn.lS i).1 (subPc tb.q0 tb.q1 gn.lS i).2
          (Nat.add gn.g.EQ gn.lS)).bind fun ps =>
      cond (tsLazyOK gn tb E) (some ⟨E, tb.as, mSum, ps, tsLazy gn tb E⟩)
        (((List.range gn.nL).mapM fun l => (List.range (Nat.pow 2 (Nat.add gn.lT l))).mapM fun i =>
            tPiece gn.g E (subPc tb.q0 tb.q1 (Nat.add gn.lT l) i).1 (subPc tb.q0 tb.q1 (Nat.add gn.lT l) i).2
              (Nat.add (Nat.add gn.g.EQ gn.lT) l)).map fun ts => ⟨E, tb.as, mSum, ps, ts⟩)

/-- The sum over the tubes of the bound terms with the `ε` terms. -/
def ivSum (gn : GlobN) (neg : Bool) : List TubeC → List (Int × Int) → Option SI
  | [], [] => some (SI.ofNat 0)
  | tc :: tcs, vt :: vts =>
    (cond (isZ2 vt) (some (SI.ofNat 0))
      ((ivAll ⟨gn.g.P, gn.g.n, gn.g.k⟩ tc.E tc.as tc.mSum neg (intC gn.g.P vt) gn.dS tc.ps).map fun b =>
        cond neg (SI.add b (SI.ofNat (mulU gn.g.P (normHi (intC gn.g.P vt)) (epsHi gn))))
          (SI.sub b (SI.ofNat (mulU gn.g.P (normHi (intC gn.g.P vt)) (epsHi gn)))))).bind fun b =>
      (ivSum gn neg tcs vts).map fun s => SI.add b s
  | _, _ => none

/-- The groups of the tubes in the functions of `t` (level `l`). -/
def ivGroups (P : Nat) (neg : Bool) (l : Nat) : List TubeC → List (Int × Int) → List (List TermD)
  | tc :: tcs, vt :: vts =>
    cond (isZ2 vt) (ivGroups P neg l tcs vts)
      (((tc.ts.getD l []).map fun x =>
          termD (cond neg (KCBall.neg (KCBall.conj (intC P vt))) (KCBall.conj (intC P vt))) x.T (x.dz, x.yz)) ::
        ivGroups P neg l tcs vts)
  | _, _ => []

/-- The levels tried: `[0]` without tubes, else `[0, …, nL - 1]`. -/
def levels (gn : GlobN) (tcs : List TubeC) : List Nat := cond tcs.isEmpty [0] (List.range gn.nL)

/-! ## W1 records -/

def taPieceOKN (g : Glob) (A : ACtx) (r' tn td : Nat) (u v : KCBall) (yts : List TermS) (hiY ivB : SI)
    (gs : List (List TermD)) (pd : Piece3) (T : PtT) (dz : Nat × Nat) : Bool :=
  SI.lt (SI.ofNat 0) (SI.sub (aTA3 g A r' u v hiY pd) ivB) &&
    tboundD g.P g.D (termD (KCBall.conj u) T dz :: toD (termOf (KCBall.neg (KCBall.conj v)) A.zT) :: yts.map toD) gs
      (SI.ofNat (Nat.div (Nat.mul (SI.toNat (SI.sub (aTA3 g A r' u v hiY pd) ivB)) td) tn))

def checkTAPieceN (g : Glob) (A : ACtx) (E : EllB) (r' tn td : Nat) (u v : KCBall) (yts : List TermS)
    (hiY ivB : SI) (gs : List (List TermD)) (n0 n1 e : Nat) : Bool :=
  (piece3 ⟨g.P, g.n, g.k⟩ E n0 n1 e).any fun pd => (ptT ⟨g.P, g.n, g.k⟩ g.D pd.z).any fun T =>
    (dzOf ⟨g.P, g.n, g.k⟩ pd.z pd.rho).any fun dz => taPieceOKN g A r' tn td u v yts hiY ivB gs pd T dz

def checkTAN (g : Glob) (A : ACtx) (E : EllB) (r' tn td : Nat) (u v : KCBall) (yts : List TermS)
    (hiY ivB : SI) (gs : List (List TermD)) : Nat → Nat → Nat → Nat → Bool
  | 0, n0, n1, e => checkTAPieceN g A E r' tn td u v yts hiY ivB gs n0 n1 e
  | fuel + 1, n0, n1, e => checkTAPieceN g A E r' tn td u v yts hiY ivB gs n0 n1 e ||
      (checkTAN g A E r' tn td u v yts hiY ivB gs fuel (Nat.mul 2 n0) (Nat.add n0 n1) (Nat.add e 1) &&
       checkTAN g A E r' tn td u v yts hiY ivB gs fuel (Nat.add n0 n1) (Nat.mul 2 n1) (Nat.add e 1))

/-- The checks of one W1 record on `[q₀, q₁]`. -/
def taOKN (gn : GlobN) (A : ACtx) (E : EllB) (r' tn td : Nat) (B : List Box4) (tcs : List TubeC) (q0 q1 : Nat)
    (u v : Int × Int) (ys vts : List (Int × Int)) : Bool :=
  blt q0 q1 && Nat.ble q1 (Nat.pow 2 gn.g.EQ) &&
    (SI.le (reConjHi gn.g.P (intC gn.g.P v) A.Sc) (SI.ofNat 0) || isZ2 v) &&
    (ivSum gn true tcs vts).any fun ivB => (levels gn tcs).any fun l =>
      checkTAN gn.g A E r' tn td (intC gn.g.P u) (intC gn.g.P v) (yTerms gn.g.P true A.pins ys) (sumBox true B ys)
        ivB (ivGroups gn.g.P true l tcs vts) gn.g.dT q0 q1 gn.g.EQ

/-- The next W1 record (`N` left in `s`), then the tile arcs after it by `rec` (the body of `C64Chk.walkTA.walkW1`,
with the recursive call as an argument). -/
@[inline] def walkW1 (gn : GlobN) (A : ACtx) (E : EllB) (r' tn td : Nat) (B : List Box4) (tcs : List TubeC)
    (rec : Nat → Nat → Nat → List (Nat × Nat) → Bool) (N q s : Nat) (hs : List (Nat × Nat)) : Bool :=
  match N with
  | 0 => false
  | N' + 1 =>
    let r := rdTAN A.pins.length tcs.length s
    taOKN gn A E r' tn td B tcs q r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 && rec N' r.1 r.2.2.2.2.2 hs

/-- The tile arcs from `q` to `1`: a hard arc `[q, b]` at the head of `hs`, or else the next W1 record. -/
def walkTA (gn : GlobN) (A : ACtx) (E : EllB) (r' tn td : Nat) (B : List Box4) (tcs : List TubeC) :
    Nat → Nat → Nat → Nat → List (Nat × Nat) → Bool
  | 0, _, _, _, _ => false
  | fuel + 1, N, q, s, hs =>
    cond (Nat.beq q (Nat.pow 2 gn.g.EQ)) (Nat.beq N 0 && hs.isEmpty)
      (match hs with
       | (a, b) :: hs' =>
         cond (Nat.beq a q) (blt q b && Nat.ble b (Nat.pow 2 gn.g.EQ) && walkTA gn A E r' tn td B tcs fuel N b s hs')
           (walkW1 gn A E r' tn td B tcs (walkTA gn A E r' tn td B tcs fuel) N q s hs)
       | [] => walkW1 gn A E r' tn td B tcs (walkTA gn A E r' tn td B tcs fuel) N q s hs)

/-! ## Leaves -/

/-- `ŵ_rep` meets the tube (as `C64Chk.tubeRepOK`; the exact checks on the data unchanged). -/
def tubeRepOK (gn : GlobN) (as : List (Q × Q)) (tb : TubeD) (qm : Q × Q) : Bool :=
  decide (0 < qm.1.d) && decide (0 < qm.2.d) && decide (0 ≤ qm.2.n) &&
    decide ((tb.q0 : Int) * qm.1.d ≤ qm.1.n * 2 ^ gn.g.EQ) &&
    decide (qm.1.n * 2 ^ gn.g.EQ ≤ (tb.q1 : Int) * qm.1.d) &&
    (tileOf gn.g tb.ti).any fun Et => (ellPt ⟨gn.g.P, gn.g.n, gn.g.k⟩ Et (qBall gn.g.P qm.1)).any fun z =>
      (cS ⟨gn.g.P, gn.g.n, gn.g.k⟩ z).any fun sz =>
      (sumK ⟨gn.g.P, gn.g.n, gn.g.k⟩ z as).any fun w => (sumK ⟨gn.g.P, gn.g.n, gn.g.k⟩ z tb.as).any fun w0 =>
        Nat.ble (normHi (KCBall.sub (KCBall.sub w sz) (KCBall.mulR gn.g.P (qBall gn.g.P qm.2) (KCBall.sub sz w0))))
          (epsLo gn)

/-- The checks of a W leaf, except its children (as `C64Chk.witLocalN`). -/
def witLocalN (gn : GlobN) (A : ACtx) (tubes : List TubeD) (bx : List (Nat × Nat × Nat)) (h : WHdr) (n dat : Nat)
    (hards : List (Nat × Nat)) : Bool :=
  (tileOf gn.g h.ti).any fun E => (atomsOK h.as).any fun mm =>
    decide (0 < h.tw.n) && decide (0 < h.tw.d) && decide (gn.g.tau.n * h.tw.d ≤ h.tw.n * gn.g.tau.d) &&
    decide (mm.1 * h.tw.d ≤ h.tw.n * mm.2) && decide (0 < h.sg.d) && decide ((h.sg.d : Int) ≤ h.sg.n) &&
    decide (h.mus.length = tubes.length) && (tubes.zip h.mus).all (fun x => tubeRepOK gn h.as x.1 x.2) &&
    (rBound gn.g A.E1 h.tw.n.toNat h.tw.d A.s0 A.s1 A.sc A.zc A.Sc A.S1c h.rX).any fun r' =>
      (sumK ⟨gn.g.P, gn.g.n, gn.g.k⟩ A.zc h.as).any fun wz =>
        Nat.ble A.r r' && Nat.ble (normHi (KCBall.sub wz (KCBall.mulR gn.g.P (qBall gn.g.P h.sg) A.Sc))) r' &&
        pinsIn ⟨gn.g.P, gn.g.n, gn.g.k⟩ h.as A.pins (pinBoxes gn.g.P A.pins bx) &&
        windOdd gn.g E h.as (KBall.cdiv (Nat.mul mm.1.toNat (Nat.pow 2 gn.g.P)) mm.2) &&
        (tubes.mapM (tubeC gn)).any fun tcs =>
          walkTA gn A E r' h.tw.n.toNat h.tw.d (pinBoxes gn.g.P A.pins bx) tcs (Nat.add (Nat.add n hards.length) 1)
            n 0 dat hards

/-- An empty leaf (as `C64Chk.emptyN`). -/
def emptyN (gn : GlobN) (A : ACtx) (tubes : List TubeD) (bx : List (Nat × Nat × Nat)) (tw : Q) (rX dat : Nat) :
    Bool :=
  let B := pinBoxes gn.g.P A.pins bx
  let v := (rdPair dat).1
  let ys := (rdPairs A.pins.length (rdPair dat).2).1
  let vts := (rdPairs tubes.length (rdPairs A.pins.length (rdPair dat).2).2).1
  decide (0 < tw.n) && decide (0 < tw.d) && decide (gn.g.tau.n * tw.d ≤ tw.n * gn.g.tau.d) &&
    (SI.nonneg (reConjLo gn.g.P (intC gn.g.P v) A.Sc) || isZ2 v) &&
    (rBound gn.g A.E1 tw.n.toNat tw.d A.s0 A.s1 A.sc A.zc A.Sc A.S1c rX).any fun r' =>
      Nat.ble A.r r' && (tubes.mapM (tubeC gn)).any fun tcs => (ivSum gn false tcs vts).any fun ivB =>
        SI.lt (SI.ofNat 0) (SI.add (SI.add (SI.sub (reConjLo gn.g.P (intC gn.g.P v) A.Sc)
          (SI.ofNat (mulU gn.g.P (normHi (intC gn.g.P v)) r'))) (sumBox false B ys)) ivB) &&
          (levels gn tcs).any fun l =>
            tboundD gn.g.P gn.g.D ((termOf (KCBall.conj (intC gn.g.P v)) A.zT :: yTerms gn.g.P false A.pins ys).map toD)
              (ivGroups gn.g.P false l tcs vts)
              (SI.ofNat (Nat.div (Nat.mul (SI.toNat (SI.add (SI.add (SI.sub (reConjLo gn.g.P (intC gn.g.P v) A.Sc)
                (SI.ofNat (mulU gn.g.P (normHi (intC gn.g.P v)) r'))) (sumBox false B ys)) ivB)) tw.d) tw.n.toNat))

/-! ## Trees and arcs -/

/-- The tree check (`ext` subtrees are separate statements), as `C64Chk.checkN`. -/
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

/-- A subtree in the context of its arc (the kernel version of `C64Chk.checkSubN`). -/
def checkSubNK (gn : GlobN) (s0 s1 sc : Nat) (pins : List (Q × Q)) (Rs : List Q) (rX : Nat) (tubes : List TubeD)
    (bx : List (Nat × Nat × Nat)) (t : NTree) : Bool :=
  hHead gn.g s0 s1 sc pins Rs && (arcCtx gn.g s0 s1 sc pins Rs rX).any fun A => checkN gn A gn.fuel tubes bx t

/-- An arc of a nested certificate (the kernel version of `C64Chk.checkArcN`). -/
def checkArcNK (gn : GlobN) : ArcN → Bool
  | .old a => checkArc gn.g a
  | .N s0 s1 sc pins Rs rX t => checkSubNK gn s0 s1 sc pins Rs rX [] (pins.map fun _ => (0, 0, 0)) t

/-- The global conditions (the kernel version of `C64Chk.checkGlobN`). -/
def checkGlobNK (gn : GlobN) : Bool := globParamsN gn && windOdd gn.g (T1B gn.g) [] 0

end C64KChk
