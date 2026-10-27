import C64K.KChkSim2
import C64K.KNest
import C64K.KPieceSome

/-!
# Simulation: the kernel port of the nested checker computes exactly what `C64Chk` (`C64Core.Nest`) computes

Every ball of `C64K.KNest` maps to the corresponding ball of `C64Core.Nest` under `KBall.toBall` / `KCBall.toC`, signed
pairs under `SI.toInt`, and the structures of the nested checker (`TermD`, `Piece3`, `IvP`, `TPc`, `TubeC`) field by
field.  The main results are `checkSubNK_eq`, `checkArcNK_eq` and `checkGlobNK_eq`: for all inputs,
`checkSubNK gn … = C64Chk.checkSubN gn …`, `checkArcNK gn a = C64Chk.checkArcN gn a`,
`checkGlobNK gn = C64Chk.checkGlobN gn`.  So a kernel-checked `checkSubNK … = true` (by `decide +kernel`) gives the
statement `C64Chk.checkSubN … = true` of the N proof, by rewriting.
-/

namespace C64KChk

open KIval KIval.KBall KNum KNum.KCBall C64Chk

/-! ## Generic lemmas -/

lemma orElse_sim {α α' : Type} {o : Option α} {o' : Option α'} {h : α → α'} (ho : o.map h = o')
    {f : Unit → Option α} {f' : Unit → Option α'} (hf : (f ()).map h = f' ()) :
    (o.orElse f).map h = o'.orElse f' := by
  subst ho
  cases o with
  | none => exact hf
  | some a => rfl

lemma mapM_sim {α β β' : Type} {f : α → Option β} {f' : α → Option β'} {h : β → β'}
    (hf : ∀ a, (f a).map h = f' a) : ∀ l : List α, (l.mapM f).map (List.map h) = l.mapM f'
  | [] => rfl
  | a :: l => by
    simp only [List.mapM_cons]
    refine bind_sim (hf a) fun b => ?_
    refine bind_sim (mapM_sim hf l) fun bs => ?_
    rfl

lemma lany_eq {α : Type} (l : List α) {p p' : α → Bool} (hp : ∀ a, p a = p' a) : l.any p = l.any p' := by
  congr 1
  funext a
  exact hp a

/-- An `Option.map` of a `cond` with a `none` branch, against an `if`. -/
lemma opt_cond_sim {c : Bool} {p : Prop} [Decidable p] (hc : c = decide p) {a : SI} {a' : Int}
    (ha : SI.toInt a = a') : (cond c (some a) none).map SI.toInt = if p then some a' else none := by
  subst hc
  by_cases hp : p <;> simp [hp, ha]

/-! ## Products with shifts, maximum and minimum -/

theorem ball_mulS_eq (P : ℕ) (a b : Ival.Ball) : C64Chk.Ball.mulS P a b = Ival.Ball.mul P a b := by
  simp only [C64Chk.Ball.mulS, Ival.Ball.mul, Ival.Ball.rnd2, Ival.Ball.cdiv, Nat.shiftLeft_eq, one_mul,
    Nat.shiftRight_eq_div_pow, Int.shiftRight_eq_div_pow, pow_one]

theorem cball_mulS_eq (P : ℕ) (a b : C64Num.CBall) : C64Chk.CBall.mulS P a b = C64Num.CBall.mul P a b := by
  simp only [C64Chk.CBall.mulS, C64Num.CBall.mul, ball_mulS_eq]

theorem reMulS_eq (P : ℕ) (a b : C64Num.CBall) : C64Chk.reMulS P a b = C64Chk.reMul P a b := by
  simp only [C64Chk.reMulS, C64Chk.reMul, ball_mulS_eq]

@[simp] lemma SI.toInt_max (a b : SI) : SI.toInt (SI.max a b) = Max.max (SI.toInt a) (SI.toInt b) := by
  unfold SI.max
  rw [SI.le_eq]
  by_cases h : SI.toInt a ≤ SI.toInt b
  · simp [h, max_def]
  · simp [h, max_def]

@[simp] lemma SI.toInt_min (a b : SI) : SI.toInt (SI.min a b) = Min.min (SI.toInt a) (SI.toInt b) := by
  unfold SI.min
  rw [SI.le_eq]
  by_cases h : SI.toInt a ≤ SI.toInt b
  · simp [h, min_def]
  · simp [h, min_def]

lemma nmin_eq (a b : Nat) : nmin a b = min a b := by
  unfold nmin
  by_cases h : a ≤ b <;> simp [h, min_def]

lemma comb_eq (neg : Bool) (a b : SI) : SI.toInt (comb neg a b) = C64Chk.comb neg (SI.toInt a) (SI.toInt b) := by
  cases neg <;> simp [comb, C64Chk.comb]

lemma epsHi_eq (gn : GlobN) : epsHi gn = C64Chk.epsHi gn := rfl

lemma epsLo_eq (gn : GlobN) : epsLo gn = C64Chk.epsLo gn := rfl

/-! ## Bounds in `t` with disc terms -/

def toTD (T : TermD) : C64Chk.TermD := ⟨toC T.W, toC T.w, toSt T.st, T.m2, T.dz, T.yz⟩

lemma termD_eq (cf : KCBall) (T : PtT) (dy : Nat × Nat) :
    toTD (termD cf T dy) = C64Chk.termD (toC cf) (toPt T) dy := rfl

lemma toD_eq (T : TermS) : toTD (toD T) = C64Chk.toD (toTm T) := rfl

lemma absW_eq (W : KCBall) : absW W = C64Chk.absW (toC W) := by
  unfold absW C64Chk.absW
  simp only [nmax_eq, nmin_eq, absHi_eq, toC_re, toC_im, nadd, ndiv]

lemma corrD_eq (P e : Nat) (tn : SI) (T : TermD) : corrD P e tn T = C64Chk.corrD P e (SI.toInt tn) (toTD T) := by
  unfold corrD C64Chk.corrD
  have h : (SI.toInt tn).natAbs = tn.m := natAbs_sval tn.s tn.m
  rw [h, absW_eq]
  rfl

def toS4 (r : KBall × KBall × Nat × Nat) : Ival.Ball × Ival.Ball × Nat × Nat := (toBall r.1, toBall r.2.1, r.2.2.1, r.2.2.2)

lemma sumTermsD_eq (P e : Nat) (tn : SI) : ∀ ts : List TermD,
    toS4 (sumTermsD P e tn ts) = C64Chk.sumTermsD P e (SI.toInt tn) (ts.map toTD)
  | [] => rfl
  | T :: ts => by
    simp only [sumTermsD, C64Chk.sumTermsD, List.map_cons]
    rw [← sumTermsD_eq P e tn ts]
    simp only [toS4, toBall_add, reMul_eq, reMulS_eq, absW_eq, corrD_eq, mulU_eq, nadd]
    rfl

def toG (b : SI × KBall × Nat) : Int × Ival.Ball × Nat := (SI.toInt b.1, toBall b.2.1, b.2.2)

lemma groupB_eq (P e : Nat) (tn : SI) : ∀ ts : List TermD,
    (groupB P e tn ts).map toG = C64Chk.groupB P e (SI.toInt tn) (ts.map toTD)
  | [] => rfl
  | [T] => by
    simp only [groupB, C64Chk.groupB, List.map_cons, List.map_nil, Option.map_some]
    simp only [toG, SI.toInt_add, hiS_eq, SI.toInt_ofNat, corrD_eq, reMul_eq, reMulS_eq, absW_eq, mulU_eq]
    rfl
  | T :: T2 :: ts => by
    have ih := groupB_eq P e tn (T2 :: ts)
    rw [List.map_cons] at ih
    rw [List.map_cons, List.map_cons]
    simp only [groupB, C64Chk.groupB]
    rw [← ih]
    cases groupB P e tn (T2 :: ts) with
    | none => rfl
    | some b =>
      simp only [Option.map_some, toG, SI.toInt_max, SI.toInt_add, hiS_eq, SI.toInt_ofNat, corrD_eq, toBall_hullB,
        reMul_eq, reMulS_eq, nmax_eq, absW_eq, mulU_eq]
      rfl

lemma groupsB_eq (P e : Nat) (tn : SI) : ∀ gs : List (List TermD),
    (groupsB P e tn gs).map toG = C64Chk.groupsB P e (SI.toInt tn) (gs.map (List.map toTD))
  | [] => rfl
  | G :: gs => by
    simp only [groupsB, C64Chk.groupsB, List.map_cons]
    rw [← groupB_eq P e tn G, ← groupsB_eq P e tn gs]
    cases groupB P e tn G with
    | none => rfl
    | some b =>
      cases groupsB P e tn gs with
      | none => rfl
      | some s => simp [toG, toBall_add]

lemma cellOKD_eq (P : Nat) (ts : List TermD) (gs : List (List TermD)) (e : Nat) (tn target : SI) :
    cellOKD P ts gs e tn target =
      C64Chk.cellOKD P (ts.map toTD) (gs.map (List.map toTD)) e (SI.toInt tn) (SI.toInt target) := by
  simp only [cellOKD, C64Chk.cellOKD, nble]
  rw [← sumTermsD_eq, ← groupsB_eq]
  congr 1
  exact any_sim rfl fun b => by
    simp only [SI.lt_eq, SI.toInt_add, SI.toInt_ofNat, hiS_eq, toS4, toG, absHi_eq, toBall_add, cdiv_eq, npow, nadd,
      nmul] <;> rfl

lemma stepD_eq (P : Nat) (down : Bool) (T : TermD) : toTD (stepD P down T) = C64Chk.stepD P down (toTD T) := by
  unfold stepD C64Chk.stepD
  cases h : T.st with
  | nil => simp [toTD, toSt, h]
  | cons x rest =>
    obtain ⟨kp, km⟩ := x
    simp only [toTD, toSt, h, List.map_cons, Prod.map]
    cases down <;> simp [toC_mul, cball_mulS_eq]

lemma map_stepD (P : Nat) (d : Bool) (ts : List TermD) :
    (ts.map (stepD P d)).map toTD = (ts.map toTD).map (C64Chk.stepD P d) := by
  simp only [List.map_map]
  exact List.map_congr_left fun T _ => stepD_eq P d T

lemma map_map_stepD (P : Nat) (d : Bool) (gs : List (List TermD)) :
    (gs.map (·.map (stepD P d))).map (List.map toTD) = (gs.map (List.map toTD)).map (·.map (C64Chk.stepD P d)) := by
  simp only [List.map_map]
  exact List.map_congr_left fun G _ => by simp only [Function.comp_apply]; exact map_stepD P d G

lemma cellsD_eq (P : Nat) (target : SI) : ∀ (fuel skip e : Nat) (tn : SI) (ts : List TermD) (gs : List (List TermD)),
    cellsD P target fuel skip e tn ts gs =
      C64Chk.cellsD P (SI.toInt target) fuel skip e (SI.toInt tn) (ts.map toTD) (gs.map (List.map toTD))
  | 0, _, _, _, _, _ => rfl
  | fuel + 1, skip, e, tn, ts, gs => by
    simp only [cellsD, C64Chk.cellsD]
    rw [cellsD_eq P target fuel, cellsD_eq P target fuel, cellOKD_eq, map_stepD, map_stepD, map_map_stepD,
      map_map_stepD]
    simp only [nbeq, nsub, nadd, cond_and_false, SI.toInt_sub, SI.toInt_add, SI.toInt_mul, SI.toInt_ofNat,
      Nat.cast_ofNat, Nat.cast_one]
    cases skip <;> simp

lemma tboundD_eq (P D : Nat) (ts : List TermD) (gs : List (List TermD)) (target : SI) :
    tboundD P D ts gs target = C64Chk.tboundD P D (ts.map toTD) (gs.map (List.map toTD)) (SI.toInt target) := by
  unfold tboundD C64Chk.tboundD
  rw [cellsD_eq]
  rfl

lemma dzOf_eq (c : KNum.Cfg) (z : KCBall) (rho : Nat) : dzOf c z rho = C64Chk.dzOf c.toC (toC z) rho := by
  unfold dzOf C64Chk.dzOf
  rw [expPiHi_eq, expPiHi_eq]
  simp only [absHi_eq, toC_im, piHi_eq, mulU_eq, cdiv_eq, nmul, KNum.Cfg.toC]

/-! ## Pieces with third-order bounds of `S` -/

def toC3 (s : KCBall × KCBall × KCBall) : C64Num.CBall × C64Num.CBall × C64Num.CBall := (toC s.1, toC s.2.1, toC s.2.2)

lemma toC_two (P : Nat) : toC (⟨KBall.ofInt P false 2, ⟨false, 0, 0⟩⟩ : KCBall) = ⟨Ival.Ball.ofInt P 2, ⟨0, 0⟩⟩ := by
  simp only [toC, toBall_ofInt, sval_false]
  rfl

lemma cSS2_eq (c : KNum.Cfg) (z : KCBall) : (cSS2 c z).map toC3 = C64Chk.cSS2 c.toC (toC z) := by
  simp only [cSS2, C64Chk.cSS2]
  refine bind_sim (toC_ccosSinPi c z) fun cs => ?_
  have h1 := toC_cdiv c.P cs.2 (KCBall.mulR c.P (piB c.P) z)
  have h2 := toC_cdiv c.P (KCBall.sub (KCBall.mul c.P (KCBall.mulR c.P (piB c.P) z) cs.1) cs.2)
    (KCBall.mul c.P (KCBall.mulR c.P (piB c.P) z) z)
  have h3 := toC_cdiv c.P (KCBall.sub (KCBall.mul c.P (KCBall.sub ⟨KBall.ofInt c.P false 2, ⟨false, 0, 0⟩⟩
        (KCBall.mul c.P (KCBall.mulR c.P (piB c.P) z) (KCBall.mulR c.P (piB c.P) z))) cs.2)
        (KCBall.mul c.P (KCBall.add (KCBall.mulR c.P (piB c.P) z) (KCBall.mulR c.P (piB c.P) z)) cs.1))
      (KCBall.mul c.P (KCBall.mulR c.P (piB c.P) z) (KCBall.mul c.P z z))
  simp only [toC_mulR, toC_sub, toC_mul, toC_add, toBall_piB, toC_two] at h1 h2 h3
  refine bind_sim h1 fun s => ?_
  refine bind_sim h2 fun s1 => ?_
  exact map_sim h3 fun s2 => rfl

lemma d23_eq (P : Nat) (s2 : KCBall) (rho eY : Nat) : d23 P s2 rho eY = C64Chk.d23 P (toC s2) rho eY := by
  unfold d23 C64Chk.d23
  simp only [normHi_eq, piHi_eq, cdiv_eq, nadd, nmul, npow]

def toP3 (p : Piece3) : C64Chk.Piece3 := ⟨toC p.z, p.rho, toC p.sz, toC p.s1, toC p.s2, p.eY, p.dS⟩

lemma piece3_eq (c : KNum.Cfg) (E : EllB) (n0 n1 e : Nat) :
    (piece3 c E n0 n1 e).map toP3 = C64Chk.piece3 c.toC (toE E) n0 n1 e := by
  unfold piece3 C64Chk.piece3
  have hz := ellPt_eq c E (midB c.P n0 n1 e)
  rw [toBall_midB] at hz
  refine bind_sim hz fun z => ?_
  refine bind_eq (ellRad_eq c E n0 n1 e) fun rho => ?_
  refine bind_sim (cSS2_eq c z) fun ss => ?_
  refine map_eq' ?_ fun eY => ?_
  · rw [expPiHi_eq, absHi_eq]
    rfl
  · simp only [toP3, toC3, normHi_eq, d23_eq, mulU_eq, nadd]
    rfl

lemma aLow3_eq (P : Nat) (u : KCBall) (p : Piece3) : SI.toInt (aLow3 P u p) = C64Chk.aLow3 P (toC u) (toP3 p) := by
  unfold aLow3 C64Chk.aLow3
  rw [SI.toInt_sub, reConjLo_eq, SI.toInt_ofNat, normHi_eq]
  rfl

lemma aTA3_eq (g : Glob) (A : ACtx) (r' : Nat) (u v : KCBall) (hiY : SI) (p : Piece3) :
    SI.toInt (aTA3 g A r' u v hiY p) = C64Chk.aTA3 g (toAC A) r' (toC u) (toC v) (SI.toInt hiY) (toP3 p) := by
  unfold aTA3 C64Chk.aTA3
  rw [SI.toInt_sub, SI.toInt_sub, SI.toInt_sub, aLow3_eq, reConjHi_eq, SI.toInt_ofNat, normHi_eq]
  rfl

lemma sumK1_eq (c : KNum.Cfg) (z : KCBall) : ∀ as : List (Q × Q),
    (sumK1 c z as).map (Prod.map toC toC) = C64Chk.sumK1 c.toC (toC z) as
  | [] => rfl
  | a :: as => by
    obtain ⟨t, m⟩ := a
    simp only [sumK1, C64Chk.sumK1]
    have hk := toC_ckt c (qBall c.P t) z
    rw [toBall_qBall] at hk
    refine bind_sim hk fun k => ?_
    refine map_sim (sumK1_eq c z as) fun s => ?_
    simp only [Prod.map, toC, KCBall.add, KCBall.mulR, C64Num.CBall.add, C64Num.CBall.mulR, toBall_add, toBall_mul,
      toBall_mulInt, toBall_neg, toBall_qBall, toBall_piB, sval_false, Nat.cast_ofNat, KNum.Cfg.toC]
    all_goals rfl

/-! ## Interval tubes -/

def toIv (p : IvP) : C64Chk.IvP := ⟨p.n0, p.n1, p.e, toC p.sz, p.dS, toC p.gz, p.dG⟩

lemma ivPiece_eq (c : KNum.Cfg) (E : EllB) (as : List (Q × Q)) (mSum n0 n1 e : Nat) :
    (ivPiece c E as mSum n0 n1 e).map toIv = C64Chk.ivPiece c.toC (toE E) as mSum n0 n1 e := by
  unfold ivPiece C64Chk.ivPiece
  refine bind_sim (piece3_eq c E n0 n1 e) fun p => ?_
  refine map_sim (sumK1_eq c p.z as) fun w => ?_
  simp only [toIv, toP3, Prod.map, toC_sub, normHi_eq, d23_eq, mulU_eq, piHi_eq, cdiv_eq, nadd, nmul, npow,
    KNum.Cfg.toC]

lemma ivOne_eq (P : Nat) (neg : Bool) (vt : KCBall) (p : IvP) :
    (ivOne P neg vt p).map SI.toInt = C64Chk.ivOne P neg (toC vt) (toIv p) := by
  dsimp only [ivOne, C64Chk.ivOne]
  cases neg
  · simp only [Bool.cond_false, Bool.false_eq_true, ↓reduceIte]
    refine opt_cond_sim ?_ ?_
    · rw [SI.le_eq, SI.toInt_sub, reConjLo_eq, SI.toInt_ofNat, normHi_eq]
      rfl
    · rw [SI.toInt_sub, reConjLo_eq, SI.toInt_ofNat, normHi_eq]
      rfl
  · simp only [Bool.cond_true, ↓reduceIte]
    refine opt_cond_sim ?_ ?_
    · rw [SI.le_eq, SI.toInt_add, reConjHi_eq, SI.toInt_ofNat, normHi_eq]
      rfl
    · rw [SI.toInt_add, reConjHi_eq, SI.toInt_ofNat, normHi_eq]
      rfl

lemma ivRec_eq (c : KNum.Cfg) (E : EllB) (as : List (Q × Q)) (mSum : Nat) (neg : Bool) (vt : KCBall) :
    ∀ (fuel n0 n1 e : Nat), (ivRec c E as mSum neg vt fuel n0 n1 e).map SI.toInt =
      C64Chk.ivRec c.toC (toE E) as mSum neg (toC vt) fuel n0 n1 e
  | 0, n0, n1, e => by
    simp only [ivRec, C64Chk.ivRec]
    exact bind_sim (ivPiece_eq c E as mSum n0 n1 e) fun p => ivOne_eq c.P neg vt p
  | fuel + 1, n0, n1, e => by
    simp only [ivRec, C64Chk.ivRec]
    refine orElse_sim (bind_sim (ivPiece_eq c E as mSum n0 n1 e) fun p => ivOne_eq c.P neg vt p) ?_
    refine bind_sim (ivRec_eq c E as mSum neg vt fuel _ _ _) fun b1 => ?_
    refine map_sim (ivRec_eq c E as mSum neg vt fuel _ _ _) fun b2 => ?_
    exact comb_eq neg b1 b2

lemma ivTry_eq (c : KNum.Cfg) (E : EllB) (as : List (Q × Q)) (mSum : Nat) (neg : Bool) (vt : KCBall) (dS : Nat)
    (p : IvP) :
    (ivTry c E as mSum neg vt dS p).map SI.toInt = C64Chk.ivTry c.toC (toE E) as mSum neg (toC vt) dS (toIv p) := by
  unfold ivTry C64Chk.ivTry
  refine orElse_sim (ivOne_eq c.P neg vt p) ?_
  cases dS with
  | zero => rfl
  | succ d =>
    dsimp only
    refine bind_sim (ivRec_eq c E as mSum neg vt d _ _ _) fun b1 => ?_
    refine map_sim (ivRec_eq c E as mSum neg vt d _ _ _) fun b2 => ?_
    exact comb_eq neg b1 b2

lemma ivAll_eq (c : KNum.Cfg) (E : EllB) (as : List (Q × Q)) (mSum : Nat) (neg : Bool) (vt : KCBall) (dS : Nat) :
    ∀ ps : List IvP, (ivAll c E as mSum neg vt dS ps).map SI.toInt =
      C64Chk.ivAll c.toC (toE E) as mSum neg (toC vt) dS (ps.map toIv)
  | [] => rfl
  | [p] => by
    simp only [ivAll, C64Chk.ivAll, List.map_cons, List.map_nil]
    exact ivTry_eq c E as mSum neg vt dS p
  | p :: p2 :: ps => by
    have ih := ivAll_eq c E as mSum neg vt dS (p2 :: ps)
    rw [List.map_cons] at ih
    rw [List.map_cons, List.map_cons]
    simp only [ivAll, C64Chk.ivAll]
    refine bind_sim (ivTry_eq c E as mSum neg vt dS p) fun b => ?_
    exact map_sim ih fun s => comb_eq neg b s

def toTP (x : TPc) : C64Chk.TPc := ⟨toPt x.T, x.dz, x.yz, x.n0, x.n1, x.e, x.rho⟩

def toTC (tc : TubeC) : C64Chk.TubeC := ⟨toE tc.E, tc.as, tc.mSum, tc.ps.map toIv, tc.ts.map (List.map toTP)⟩

lemma tPiece_eq (g : Glob) (E : EllB) (n0 n1 e : Nat) :
    (tPiece g E n0 n1 e).map toTP = C64Chk.tPiece g (toE E) n0 n1 e := by
  unfold tPiece C64Chk.tPiece
  have hz := ellPt_eq ⟨g.P, g.n, g.k⟩ E (midB g.P n0 n1 e)
  rw [toBall_midB, cfg_toC] at hz
  refine bind_sim hz fun z => ?_
  rw [ellRad_eq, cfg_toC]
  refine bind_eq rfl fun rho => ?_
  have hT := ptT_eq ⟨g.P, g.n, g.k⟩ g.D z
  rw [cfg_toC] at hT
  refine bind_sim hT fun T => ?_
  rw [dzOf_eq, cfg_toC]
  exact map_eq' rfl fun dz => rfl

lemma subPc_eq (q0 q1 l i : Nat) : subPc q0 q1 l i = C64Chk.subPc q0 q1 l i := rfl

/-! ### The lazy pieces of a tube (`tsLazyOK`, `tsLazy`) -/

/-- A `mapM` whose every result is `some (g a)` is `some` of the `map`. -/
lemma mapM_eq_some_map {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ l : List α, (∀ a ∈ l, f a = some (g a)) → l.mapM f = some (l.map g)
  | [], _ => rfl
  | a :: l, h => by
    have ha := h a (List.mem_cons_self ..)
    have ih := mapM_eq_some_map f g l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp [List.mapM_cons, ha, ih]

/-- The pieces of the levels `l < nL` satisfy the hypotheses of `tPiece_isSome` under the guard. -/
lemma tPiece_some_of_guard (gn : GlobN) (tb : TubeD) (E : EllB) (hg : tsLazyOK gn tb E = true) {l i : Nat}
    (hl : l < gn.nL) (hi : i < 2 ^ (gn.lT + l)) :
    tPiece gn.g E (subPc tb.q0 tb.q1 (Nat.add gn.lT l) i).1 (subPc tb.q0 tb.q1 (Nat.add gn.lT l) i).2
        (Nat.add (Nat.add gn.g.EQ gn.lT) l) =
      some ((tPiece gn.g E (subPc tb.q0 tb.q1 (Nat.add gn.lT l) i).1 (subPc tb.q0 tb.q1 (Nat.add gn.lT l) i).2
        (Nat.add (Nat.add gn.g.EQ gn.lT) l)).getD tpcNone) := by
  simp only [tsLazyOK, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨hG, hq⟩, hq1⟩, hE⟩ := hg
  simp only [globLazyOK, Bool.and_eq_true] at hG
  obtain ⟨⟨⟨⟨hP, hn⟩, hk⟩, hD⟩, hL⟩ := hG
  have hP : gn.g.P = 80 := Nat.eq_of_beq_eq_true hP
  have hn : gn.g.n = 18 := Nat.eq_of_beq_eq_true hn
  have hk : gn.g.k = 3 := Nat.eq_of_beq_eq_true hk
  have hD : gn.g.D = 23 := Nat.eq_of_beq_eq_true hD
  have hL := Nat.le_of_ble_eq_true hL
  have hq : tb.q0 < tb.q1 := Nat.le_of_ble_eq_true hq
  have hq1 := Nat.le_of_ble_eq_true hq1
  simp only [Nat.add_eq, Nat.pow_eq] at hL hq1
  set m := gn.lT + l with hm
  have hi1 : i + 1 ≤ 2 ^ m := hi
  have h1 : (subPc tb.q0 tb.q1 (Nat.add gn.lT l) i).2 ≤ 2 ^ (Nat.add (Nat.add gn.g.EQ gn.lT) l) := by
    simp only [subPc, Nat.add_eq, Nat.mul_eq, Nat.pow_eq, Nat.sub_eq]
    rw [← hm]
    have e1 : (i + 1) * (tb.q1 - tb.q0) ≤ 2 ^ m * (tb.q1 - tb.q0) := Nat.mul_le_mul_right _ hi1
    have e2 : tb.q0 * 2 ^ m + 2 ^ m * (tb.q1 - tb.q0) = 2 ^ m * tb.q1 := by
      rw [Nat.mul_comm tb.q0, ← Nat.mul_add, Nat.add_sub_cancel' (Nat.le_of_lt hq)]
    have e3 : 2 ^ m * tb.q1 ≤ 2 ^ m * 2 ^ gn.g.EQ := Nat.mul_le_mul_left _ hq1
    have e4 : 2 ^ (gn.g.EQ + gn.lT + l) = 2 ^ m * 2 ^ gn.g.EQ := by
      rw [hm, ← Nat.pow_add, Nat.add_assoc, Nat.add_comm gn.g.EQ]
    rw [e4]
    omega
  have hsome := C64KPiece.tPiece_isSome gn.g E (subPc tb.q0 tb.q1 (Nat.add gn.lT l) i).1
    (subPc tb.q0 tb.q1 (Nat.add gn.lT l) i).2 (Nat.add (Nat.add gn.g.EQ gn.lT) l) hP hn hk hD hE
    (by simp only [Nat.add_eq]; omega) h1
  cases ht : tPiece gn.g E (subPc tb.q0 tb.q1 (Nat.add gn.lT l) i).1 (subPc tb.q0 tb.q1 (Nat.add gn.lT l) i).2
      (Nat.add (Nat.add gn.g.EQ gn.lT) l) with
  | none => rw [ht] at hsome; simp at hsome
  | some x => rfl

/-- Under the guard, the eager pieces of a tube are the lazy ones. -/
lemma tsMapM_lazy (gn : GlobN) (tb : TubeD) (E : EllB) (hg : tsLazyOK gn tb E = true) :
    ((List.range gn.nL).mapM fun l => (List.range (Nat.pow 2 (Nat.add gn.lT l))).mapM fun i =>
        tPiece gn.g E (subPc tb.q0 tb.q1 (Nat.add gn.lT l) i).1 (subPc tb.q0 tb.q1 (Nat.add gn.lT l) i).2
          (Nat.add (Nat.add gn.g.EQ gn.lT) l)) = some (tsLazy gn tb E) := by
  unfold tsLazy
  refine mapM_eq_some_map _ _ _ fun l hl => ?_
  refine mapM_eq_some_map _ _ _ fun i hi => ?_
  exact tPiece_some_of_guard gn tb E hg (List.mem_range.mp hl) (by simpa [Nat.add_eq, Nat.pow_eq] using List.mem_range.mp hi)

lemma tubeC_eq (gn : GlobN) (tb : TubeD) : (tubeC gn tb).map toTC = C64Chk.tubeC gn tb := by
  unfold tubeC C64Chk.tubeC
  refine bind_sim (tileOf_eq gn.g tb.ti) fun E => ?_
  refine bind_eq rfl fun mm => ?_
  have hps : ((List.range (Nat.pow 2 gn.lS)).mapM fun i =>
        ivPiece ⟨gn.g.P, gn.g.n, gn.g.k⟩ E tb.as (KBall.cdiv (Nat.mul mm.1.toNat (Nat.pow 2 gn.g.P)) mm.2)
          (subPc tb.q0 tb.q1 gn.lS i).1 (subPc tb.q0 tb.q1 gn.lS i).2 (Nat.add gn.g.EQ gn.lS)).map (List.map toIv) =
      (List.range (2 ^ gn.lS)).mapM fun i =>
        C64Chk.ivPiece gn.g.cfg (toE E) tb.as (Ival.Ball.cdiv (mm.1.toNat * 2 ^ gn.g.P) mm.2)
          (C64Chk.subPc tb.q0 tb.q1 gn.lS i).1 (C64Chk.subPc tb.q0 tb.q1 gn.lS i).2 (gn.g.EQ + gn.lS) :=
    mapM_sim (fun i => ivPiece_eq _ E tb.as _ _ _ _) _
  refine bind_sim hps fun ps => ?_
  have hts : ((List.range gn.nL).mapM fun l => (List.range (Nat.pow 2 (Nat.add gn.lT l))).mapM fun i =>
        tPiece gn.g E (subPc tb.q0 tb.q1 (Nat.add gn.lT l) i).1 (subPc tb.q0 tb.q1 (Nat.add gn.lT l) i).2
          (Nat.add (Nat.add gn.g.EQ gn.lT) l)).map (List.map (List.map toTP)) =
      (List.range gn.nL).mapM fun l => (List.range (2 ^ (gn.lT + l))).mapM fun i =>
        C64Chk.tPiece gn.g (toE E) (C64Chk.subPc tb.q0 tb.q1 (gn.lT + l) i).1 (C64Chk.subPc tb.q0 tb.q1 (gn.lT + l) i).2
          (gn.g.EQ + gn.lT + l) :=
    mapM_sim (fun l => mapM_sim (fun i => tPiece_eq gn.g E _ _ _) _) _
  cases hg : tsLazyOK gn tb E
  · exact map_sim hts fun ts => rfl
  · show ((some (tsLazy gn tb E)).map fun ts =>
        (⟨E, tb.as, KBall.cdiv (Nat.mul mm.1.toNat (Nat.pow 2 gn.g.P)) mm.2, ps, ts⟩ : TubeC)).map toTC = _
    rw [← tsMapM_lazy gn tb E hg]
    exact map_sim hts fun ts => rfl

/-- The sum over the tubes of the bound terms. -/
lemma ivSum_eq (gn : GlobN) (neg : Bool) : ∀ (tcs : List TubeC) (vts : List (Int × Int)),
    (ivSum gn neg tcs vts).map SI.toInt = C64Chk.ivSum gn neg (tcs.map toTC) vts
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | tc :: tcs, vt :: vts => by
    simp only [ivSum, C64Chk.ivSum, List.map_cons]
    have h1 : (cond (isZ2 vt) (some (SI.ofNat 0))
        ((ivAll ⟨gn.g.P, gn.g.n, gn.g.k⟩ tc.E tc.as tc.mSum neg (intC gn.g.P vt) gn.dS tc.ps).map fun b =>
          cond neg (SI.add b (SI.ofNat (mulU gn.g.P (normHi (intC gn.g.P vt)) (epsHi gn))))
            (SI.sub b (SI.ofNat (mulU gn.g.P (normHi (intC gn.g.P vt)) (epsHi gn)))))).map SI.toInt =
        (if vt.1 = 0 ∧ vt.2 = 0 then some 0
         else (C64Chk.ivAll gn.g.cfg (toE tc.E) tc.as tc.mSum neg (C64Chk.intC gn.g.P vt) gn.dS (tc.ps.map toIv)).map
          fun (b : Int) =>
            if neg then b + ((C64Chk.mulU gn.g.P (C64Num.normHi (C64Chk.intC gn.g.P vt)) (C64Chk.epsHi gn) : Nat) : Int)
            else b - ((C64Chk.mulU gn.g.P (C64Num.normHi (C64Chk.intC gn.g.P vt)) (C64Chk.epsHi gn) : Nat) : Int)) := by
      rw [isZ2_eq]
      by_cases h : vt.1 = 0 ∧ vt.2 = 0
      · simp only [h, and_self, decide_true, Bool.cond_true, ↓reduceIte, Option.map_some, SI.toInt_ofNat,
          Nat.cast_zero]
      · simp only [h, decide_false, Bool.cond_false, ↓reduceIte]
        have hA := ivAll_eq ⟨gn.g.P, gn.g.n, gn.g.k⟩ tc.E tc.as tc.mSum neg (intC gn.g.P vt) gn.dS tc.ps
        rw [toC_intC] at hA
        refine map_sim hA fun b => ?_
        cases neg <;> simp [normHi_eq, toC_intC, epsHi_eq, mulU_eq]
    refine bind_sim h1 fun b => ?_
    exact map_sim (ivSum_eq gn neg tcs vts) fun s => SI.toInt_add b s

lemma getD_map_map {α β : Type} (f : α → β) (l : List (List α)) (i : Nat) :
    (l.map (List.map f)).getD i [] = (l.getD i []).map f := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

lemma ivGroups_eq (P : Nat) (neg : Bool) (l : Nat) : ∀ (tcs : List TubeC) (vts : List (Int × Int)),
    (ivGroups P neg l tcs vts).map (List.map toTD) = C64Chk.ivGroups P neg l (tcs.map toTC) vts
  | [], _ => rfl
  | _ :: _, [] => rfl
  | tc :: tcs, vt :: vts => by
    simp only [ivGroups, C64Chk.ivGroups, List.map_cons, isZ2_eq, Bool.cond_decide]
    by_cases h : vt.1 = 0 ∧ vt.2 = 0
    · simp only [h, and_self, ↓reduceIte]
      exact ivGroups_eq P neg l tcs vts
    · simp only [h, ↓reduceIte, List.map_cons]
      rw [ivGroups_eq P neg l tcs vts]
      congr 1
      simp only [toTC, getD_map_map, List.map_map]
      refine List.map_congr_left fun x _ => ?_
      cases neg <;> simp [termD_eq, toTP, toC_neg, toC_conj, toC_intC]

lemma levels_eq (gn : GlobN) (tcs : List TubeC) : levels gn tcs = C64Chk.levels gn (tcs.map toTC) := by
  unfold levels C64Chk.levels
  rw [List.isEmpty_map]
  cases tcs.isEmpty <;> rfl

/-! ## Arc contexts -/

@[simp] lemma toAC_pins (A : ACtx) : (toAC A).pins = A.pins.map toPin := rfl
@[simp] lemma toAC_E1 (A : ACtx) : (toAC A).E1 = toE A.E1 := rfl
@[simp] lemma toAC_zc (A : ACtx) : (toAC A).zc = toC A.zc := rfl
@[simp] lemma toAC_Sc (A : ACtx) : (toAC A).Sc = toC A.Sc := rfl
@[simp] lemma toAC_S1c (A : ACtx) : (toAC A).S1c = toC A.S1c := rfl
@[simp] lemma toAC_zT (A : ACtx) : (toAC A).zT = toPt A.zT := rfl
@[simp] lemma toAC_r (A : ACtx) : (toAC A).r = A.r := rfl
@[simp] lemma toAC_s0 (A : ACtx) : (toAC A).s0 = A.s0 := rfl
@[simp] lemma toAC_s1 (A : ACtx) : (toAC A).s1 = A.s1 := rfl
@[simp] lemma toAC_sc (A : ACtx) : (toAC A).sc = A.sc := rfl

lemma yTermsD_eq (P : Nat) (neg : Bool) (pins : List (KCBall × PtT × Q)) (ys : List (Int × Int)) :
    ((yTerms P neg pins ys).map toD).map toTD = (C64Chk.yTerms P neg (pins.map toPin) ys).map C64Chk.toD := by
  rw [← yTerms_eq, List.map_map, List.map_map]
  rfl


/-! ## W1 records -/

lemma taPieceOKN_eq (g : Glob) (A : ACtx) (r' tn td : Nat) (u v : KCBall) (yts : List TermS) (hiY ivB : SI)
    (gs : List (List TermD)) (pd : Piece3) (T : PtT) (dz : Nat × Nat) :
    taPieceOKN g A r' tn td u v yts hiY ivB gs pd T dz =
      C64Chk.taPieceOKN g (toAC A) r' tn td (toC u) (toC v) (yts.map toTm) (SI.toInt hiY) (SI.toInt ivB)
        (gs.map (List.map toTD)) (toP3 pd) (toPt T) dz := by
  unfold taPieceOKN C64Chk.taPieceOKN
  simp only [tboundD_eq, SI.lt_eq, SI.toInt_sub, aTA3_eq, SI.toInt_ofNat, SI.toNat_eq, Nat.cast_zero, List.map_cons,
    List.map_map, termD_eq, toD_eq, termOf_eq, toC_conj, toC_neg, nmul, ndiv]
  all_goals rfl

lemma checkTAPieceN_eq (g : Glob) (A : ACtx) (E : EllB) (r' tn td : Nat) (u v : KCBall) (yts : List TermS)
    (hiY ivB : SI) (gs : List (List TermD)) (n0 n1 e : Nat) :
    checkTAPieceN g A E r' tn td u v yts hiY ivB gs n0 n1 e =
      C64Chk.checkTAPieceN g (toAC A) (toE E) r' tn td (toC u) (toC v) (yts.map toTm) (SI.toInt hiY) (SI.toInt ivB)
        (gs.map (List.map toTD)) n0 n1 e := by
  unfold checkTAPieceN C64Chk.checkTAPieceN
  exact any_sim (piece3_eq _ E n0 n1 e) fun pd => any_sim (ptT_eq _ g.D pd.z) fun T =>
    any_eq (dzOf_eq _ pd.z pd.rho) fun dz => taPieceOKN_eq g A r' tn td u v yts hiY ivB gs pd T dz

lemma checkTAN_eq (g : Glob) (A : ACtx) (E : EllB) (r' tn td : Nat) (u v : KCBall) (yts : List TermS)
    (hiY ivB : SI) (gs : List (List TermD)) : ∀ (fuel n0 n1 e : Nat),
    checkTAN g A E r' tn td u v yts hiY ivB gs fuel n0 n1 e =
      C64Chk.checkTAN g (toAC A) (toE E) r' tn td (toC u) (toC v) (yts.map toTm) (SI.toInt hiY) (SI.toInt ivB)
        (gs.map (List.map toTD)) fuel n0 n1 e
  | 0, n0, n1, e => checkTAPieceN_eq g A E r' tn td u v yts hiY ivB gs n0 n1 e
  | fuel + 1, n0, n1, e => by
    simp only [checkTAN, C64Chk.checkTAN, nmul, nadd]
    rw [checkTAPieceN_eq, checkTAN_eq g A E r' tn td u v yts hiY ivB gs fuel,
      checkTAN_eq g A E r' tn td u v yts hiY ivB gs fuel]

lemma taOKN_eq (gn : GlobN) (A : ACtx) (E : EllB) (r' tn td : Nat) (B : List Box4) (tcs : List TubeC) (q0 q1 : Nat)
    (u v : Int × Int) (ys vts : List (Int × Int)) :
    taOKN gn A E r' tn td B tcs q0 q1 u v ys vts =
      C64Chk.taOKN gn (toAC A) (toE E) r' tn td (B.map toB4) (tcs.map toTC) q0 q1 u v ys vts := by
  unfold taOKN C64Chk.taOKN
  simp only [blt_eq, nble, npow, SI.le_eq, reConjHi_eq, toC_intC, SI.toInt_ofNat, Nat.cast_zero, isZ2_eq, beq_zero2,
    toAC_Sc]
  congr 1
  refine any_sim (ivSum_eq gn true tcs vts) fun ivB => ?_
  rw [levels_eq]
  refine lany_eq _ fun l => ?_
  rw [checkTAN_eq, yTerms_eq, sumBox_eq, ivGroups_eq, toC_intC, toC_intC]
  all_goals rfl

lemma walkTA_eq (gn : GlobN) (A : ACtx) (E : EllB) (r' tn td : Nat) (B : List Box4) (tcs : List TubeC) :
    ∀ (fuel N q s : Nat) (hs : List (Nat × Nat)),
    walkTA gn A E r' tn td B tcs fuel N q s hs =
      C64Chk.walkTA gn (toAC A) (toE E) r' tn td (B.map toB4) (tcs.map toTC) fuel N q s hs
  | 0, _, _, _, _ => by simp [walkTA, C64Chk.walkTA]
  | fuel + 1, N, q, s, hs => by
    have hW : ∀ N q s (hs : List (Nat × Nat)),
        walkW1 gn A E r' tn td B tcs (walkTA gn A E r' tn td B tcs fuel) N q s hs =
          C64Chk.walkTA.walkW1 gn (toAC A) (toE E) r' tn td (B.map toB4) (tcs.map toTC) fuel N q s hs := by
      intro N q s hs
      cases N with
      | zero => simp [walkW1, C64Chk.walkTA.walkW1]
      | succ N' =>
        simp only [walkW1, C64Chk.walkTA.walkW1]
        rw [taOKN_eq, walkTA_eq gn A E r' tn td B tcs fuel]
        simp only [toAC_pins, List.length_map]
    unfold C64Chk.walkTA
    simp only [walkTA]
    split_ifs with hq
    · have hb : Nat.beq q (Nat.pow 2 gn.g.EQ) = true := by rw [nbeq]; exact decide_eq_true hq
      rw [hb, Bool.cond_true]
      cases N <;> rfl
    · have hb : Nat.beq q (Nat.pow 2 gn.g.EQ) = false := by rw [nbeq]; exact decide_eq_false hq
      rw [hb, Bool.cond_false]
      cases hs with
      | nil => exact hW N q s []
      | cons ab hs' =>
        obtain ⟨a, b⟩ := ab
        dsimp only
        split_ifs with ha
        · subst ha
          rw [Nat.beq_refl, Bool.cond_true, walkTA_eq gn A E r' tn td B tcs fuel, blt_eq, nble]
          rfl
        · have hb' : Nat.beq a q = false := by rw [nbeq]; exact decide_eq_false ha
          rw [hb', Bool.cond_false]
          exact hW N q s _

/-! ## Leaves -/

lemma tubeRepOK_eq (gn : GlobN) (as : List (Q × Q)) (tb : TubeD) (qm : Q × Q) :
    tubeRepOK gn as tb qm = C64Chk.tubeRepOK gn as tb qm := by
  dsimp only [tubeRepOK, C64Chk.tubeRepOK]
  congr 1
  refine any_sim (tileOf_eq gn.g tb.ti) fun Et => ?_
  have hz := ellPt_eq ⟨gn.g.P, gn.g.n, gn.g.k⟩ Et (qBall gn.g.P qm.1)
  rw [toBall_qBall, cfg_toC] at hz
  refine any_sim hz fun z => ?_
  have hs := toC_cS ⟨gn.g.P, gn.g.n, gn.g.k⟩ z
  rw [cfg_toC] at hs
  refine any_sim hs fun sz => ?_
  have hw := sumK_eq ⟨gn.g.P, gn.g.n, gn.g.k⟩ z as
  rw [cfg_toC] at hw
  refine any_sim hw fun w => ?_
  have hw0 := sumK_eq ⟨gn.g.P, gn.g.n, gn.g.k⟩ z tb.as
  rw [cfg_toC] at hw0
  refine any_sim hw0 fun w0 => ?_
  rw [nble, normHi_eq, toC_sub, toC_sub, toC_mulR, toC_sub, toBall_qBall, epsLo_eq]
  all_goals rfl

lemma witLocalN_sim (gn : GlobN) (A : ACtx) (tubes : List TubeD) (bx : List (Nat × Nat × Nat)) (h : WHdr)
    (n dat : Nat) (hards : List (Nat × Nat)) :
    witLocalN gn A tubes bx h n dat hards = C64Chk.witLocalN gn (toAC A) tubes bx h n dat hards := by
  dsimp only [witLocalN, C64Chk.witLocalN]
  refine any_sim (tileOf_eq gn.g h.ti) fun E => ?_
  refine any_eq rfl fun mm => ?_
  simp only [tubeRepOK_eq, toAC_pins, toAC_E1, toAC_zc, toAC_Sc, toAC_S1c, toAC_r, toAC_s0, toAC_s1, toAC_sc]
  congr 1
  rw [rBound_eq]
  refine any_eq rfl fun r' => ?_
  have hw := sumK_eq ⟨gn.g.P, gn.g.n, gn.g.k⟩ A.zc h.as
  rw [cfg_toC] at hw
  refine any_sim hw fun wz => ?_
  have hwalk : (tubes.mapM (tubeC gn)).any (fun tcs => walkTA gn A E r' h.tw.n.toNat h.tw.d (pinBoxes gn.g.P A.pins bx)
        tcs (Nat.add (Nat.add n hards.length) 1) n 0 dat hards) =
      (tubes.mapM (C64Chk.tubeC gn)).any (fun tcs => C64Chk.walkTA gn (toAC A) (toE E) r' h.tw.n.toNat h.tw.d
        (C64Chk.pinBoxes gn.g.P (A.pins.map toPin) bx) tcs (n + hards.length + 1) n 0 dat hards) :=
    any_sim (mapM_sim (fun tb => tubeC_eq gn tb) tubes) fun tcs => by rw [walkTA_eq, pinBoxes_eq]; rfl
  rw [hwalk, pinsIn_eq, pinBoxes_eq, windOdd_eq, nble, nble, normHi_eq, toC_sub, toC_mulR, toBall_qBall]
  all_goals rfl

lemma emptyN_eq (gn : GlobN) (A : ACtx) (tubes : List TubeD) (bx : List (Nat × Nat × Nat)) (tw : Q) (rX dat : Nat) :
    emptyN gn A tubes bx tw rX dat = C64Chk.emptyN gn (toAC A) tubes bx tw rX dat := by
  dsimp only [emptyN, C64Chk.emptyN]
  simp only [toAC_pins, toAC_E1, toAC_zc, toAC_Sc, toAC_S1c, toAC_zT, toAC_r, toAC_s0, toAC_s1, toAC_sc, List.length_map,
    SI.nonneg_eq, reConjLo_eq, toC_intC, isZ2_eq, beq_zero2]
  congr 1
  rw [rBound_eq]
  refine any_eq rfl fun r' => ?_
  rw [nble]
  congr 1
  refine any_sim (mapM_sim (fun tb => tubeC_eq gn tb) tubes) fun tcs => ?_
  refine any_sim (ivSum_eq gn false tcs _) fun ivB => ?_
  rw [levels_eq]
  congr 1
  · simp only [SI.lt_eq, SI.toInt_add, SI.toInt_sub, reConjLo_eq, SI.toInt_ofNat, Nat.cast_zero, normHi_eq, toC_intC,
      sumBox_eq, pinBoxes_eq, mulU_eq]
  · refine lany_eq _ fun l => ?_
    rw [tboundD_eq, ivGroups_eq]
    simp only [List.map_cons, yTermsD_eq, toD_eq, termOf_eq, toC_conj, toC_intC, SI.toInt_ofNat, SI.toNat_eq,
      SI.toInt_add, SI.toInt_sub, reConjLo_eq, normHi_eq, sumBox_eq, pinBoxes_eq, mulU_eq, nmul, ndiv]
    all_goals rfl

/-! ## Trees and arcs -/

lemma checkN_eq (gn : GlobN) (A : ACtx) : ∀ (fuel : Nat) (tubes : List TubeD) (bx : List (Nat × Nat × Nat))
    (t : NTree), checkN gn A fuel tubes bx t = C64Chk.checkN gn (toAC A) fuel tubes bx t
  | 0, _, _, _ => rfl
  | fuel + 1, tubes, bx, t => by
    cases t with
    | empty tw rX dat => exact emptyN_eq gn A tubes bx tw rX dat
    | wit h n dat hards kids =>
      simp only [checkN, C64Chk.checkN]
      rw [witLocalN_sim]
      simp only [checkN_eq gn A fuel]
    | split j c0 c1 c2 c3 =>
      simp only [checkN, C64Chk.checkN]
      rw [checkN_eq gn A fuel, checkN_eq gn A fuel, checkN_eq gn A fuel, checkN_eq gn A fuel]
    | ivsplit k qm lo hi =>
      simp only [checkN, C64Chk.checkN]
      cases tubes[k]? with
      | none => rfl
      | some tb =>
        dsimp only
        rw [checkN_eq gn A fuel, checkN_eq gn A fuel]
    | ext => rfl

/-- A subtree in the context of its arc: the kernel port computes exactly `C64Chk.checkSubN`. -/
theorem checkSubNK_eq (gn : GlobN) (s0 s1 sc : Nat) (pins : List (Q × Q)) (Rs : List Q) (rX : Nat)
    (tubes : List TubeD) (bx : List (Nat × Nat × Nat)) (t : NTree) :
    checkSubNK gn s0 s1 sc pins Rs rX tubes bx t = C64Chk.checkSubN gn s0 s1 sc pins Rs rX tubes bx t := by
  unfold checkSubNK C64Chk.checkSubN
  rw [hHead_eq, any_sim (arcCtx_eq gn.g s0 s1 sc pins Rs rX) (p' := fun A => C64Chk.checkN gn A gn.fuel tubes bx t)
    fun A => checkN_eq gn A gn.fuel tubes bx t]

/-- An arc of a nested certificate: the kernel port computes exactly `C64Chk.checkArcN`. -/
theorem checkArcNK_eq (gn : GlobN) (a : ArcN) : checkArcNK gn a = C64Chk.checkArcN gn a := by
  cases a with
  | old a => exact checkArc_eq gn.g a
  | N s0 s1 sc pins Rs rX t => exact checkSubNK_eq gn s0 s1 sc pins Rs rX [] _ t

/-- The global conditions: the kernel port computes exactly `C64Chk.checkGlobN`. -/
theorem checkGlobNK_eq (gn : GlobN) : checkGlobNK gn = C64Chk.checkGlobN gn := by
  unfold checkGlobNK C64Chk.checkGlobN
  rw [windOdd_eq, T1B_eq]

/-- Transfer: a kernel-checked subtree gives the statement of the N proof. -/
theorem checkSubN_of_K {gn : GlobN} {s0 s1 sc : Nat} {pins : List (Q × Q)} {Rs : List Q} {rX : Nat}
    {tubes : List TubeD} {bx : List (Nat × Nat × Nat)} {t : NTree}
    (h : checkSubNK gn s0 s1 sc pins Rs rX tubes bx t = true) : C64Chk.checkSubN gn s0 s1 sc pins Rs rX tubes bx t = true :=
  (checkSubNK_eq gn s0 s1 sc pins Rs rX tubes bx t) ▸ h

theorem checkArcN_of_K {gn : GlobN} {a : ArcN} (h : checkArcNK gn a = true) : C64Chk.checkArcN gn a = true :=
  (checkArcNK_eq gn a) ▸ h

theorem checkGlobN_of_K {gn : GlobN} (h : checkGlobNK gn = true) : C64Chk.checkGlobN gn = true :=
  (checkGlobNK_eq gn) ▸ h

end C64KChk
