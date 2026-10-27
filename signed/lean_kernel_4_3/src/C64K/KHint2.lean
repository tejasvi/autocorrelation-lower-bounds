import C64K.KSeg

/-!
# Hinted W1 records, tree hints (core Lean only): skip the tests that fail

The checker searches: `checkTAN` tests a piece of the tile arc and bisects it when the test fails; `cellsD` tests a
cell in `t` and splits it when the test fails.  A failing test is wasted work (in the samples of this study 40-60% of
the cell tests of a record).  A hint is the tree of the checker's own search with the failing tests marked as splits:
`CHint` for the cells (`.test`: test this cell; `.split l r`: split it without testing, and at the untested top
levels of `cellsD` always `.split`), `PHint` for the pieces of the
tile arc (`.piece c`: test this piece, `c` the hint of its cells; `.split l r`: bisect without testing).  The hinted
functions follow the tree; their soundness lemmas (`cellsDT_sound`, `checkTANT_sound`, `taOKNT_sound`, ...) say that a
hinted `true` gives the checker's `true`, whatever the hint, so hints are untrusted data like the certificate.
-/

namespace C64KChk

open KIval KIval.KBall KNum C64Chk

/-- A hint for `cellsD` below the first tested level. -/
inductive CHint where
  | test
  | split (l r : CHint)

/-- A hint for `checkTAN`. -/
inductive PHint where
  | piece (c : CHint)
  | split (l r : PHint)

/-- `cellsD` following a cell hint (the untested top levels, `skip > 0`, are split as in `cellsD`). -/
def cellsDT (P : Nat) (target : SI) : Nat → Nat → Nat → SI → List TermD → List (List TermD) → CHint → Bool
  | 0, _, _, _, _, _, _ => false
  | fuel + 1, skip, e, tn, ts, gs, ch =>
    match Nat.beq skip 0, ch with
    | true, .test => cellOKD P ts gs e tn target
    | true, .split l r =>
      cellsDT P target fuel (Nat.sub skip 1) (Nat.add e 1) (SI.sub (SI.mul (SI.ofNat 2) tn) (SI.ofNat 1))
          (ts.map (stepD P true)) (gs.map (·.map (stepD P true))) l &&
        cellsDT P target fuel (Nat.sub skip 1) (Nat.add e 1) (SI.add (SI.mul (SI.ofNat 2) tn) (SI.ofNat 1))
          (ts.map (stepD P false)) (gs.map (·.map (stepD P false))) r
    | false, .split l r =>
      cellsDT P target fuel (Nat.sub skip 1) (Nat.add e 1) (SI.sub (SI.mul (SI.ofNat 2) tn) (SI.ofNat 1))
          (ts.map (stepD P true)) (gs.map (·.map (stepD P true))) l &&
        cellsDT P target fuel (Nat.sub skip 1) (Nat.add e 1) (SI.add (SI.mul (SI.ofNat 2) tn) (SI.ofNat 1))
          (ts.map (stepD P false)) (gs.map (·.map (stepD P false))) r
    | false, .test => false

theorem cellsDT_sound (P : Nat) (target : SI) : ∀ (fuel skip e : Nat) (tn : SI) (ts : List TermD)
    (gs : List (List TermD)) (ch : CHint), cellsDT P target fuel skip e tn ts gs ch = true →
    cellsD P target fuel skip e tn ts gs = true
  | 0, _, _, _, _, _, _, hh => by simp [cellsDT] at hh
  | fuel + 1, skip, e, tn, ts, gs, ch, hh => by
    simp only [cellsD]
    cases hs : Nat.beq skip 0 with
    | true =>
      cases ch with
      | test =>
        simp only [cellsDT, hs] at hh
        simp only [hh, Bool.cond_true, Bool.true_or]
      | split l r =>
        simp only [cellsDT, hs, Bool.and_eq_true] at hh
        rw [cellsDT_sound P target fuel _ _ _ _ _ l hh.1, cellsDT_sound P target fuel _ _ _ _ _ r hh.2]
        simp
    | false =>
      cases ch with
      | test => simp [cellsDT, hs] at hh
      | split l r =>
        simp only [cellsDT, hs, Bool.and_eq_true] at hh
        rw [cellsDT_sound P target fuel _ _ _ _ _ l hh.1, cellsDT_sound P target fuel _ _ _ _ _ r hh.2]
        simp

/-- `taPieceOKN` with a hinted t-bound. -/
def taPieceOKNT (g : Glob) (A : ACtx) (r' tn td : Nat) (u v : KCBall) (yts : List TermS) (hiY ivB : SI)
    (gs : List (List TermD)) (pd : Piece3) (T : PtT) (dz : Nat × Nat) (ch : CHint) : Bool :=
  SI.lt (SI.ofNat 0) (SI.sub (aTA3 g A r' u v hiY pd) ivB) &&
    cellsDT g.P (SI.ofNat (Nat.div (Nat.mul (SI.toNat (SI.sub (aTA3 g A r' u v hiY pd) ivB)) td) tn)) (Nat.add g.D 1)
      4 1 (SI.ofNat 0)
      (termD (KCBall.conj u) T dz :: toD (termOf (KCBall.neg (KCBall.conj v)) A.zT) :: yts.map toD) gs ch

theorem taPieceOKNT_sound {g : Glob} {A : ACtx} {r' tn td : Nat} {u v : KCBall} {yts : List TermS} {hiY ivB : SI}
    {gs : List (List TermD)} {pd : Piece3} {T : PtT} {dz : Nat × Nat} {ch : CHint}
    (hh : taPieceOKNT g A r' tn td u v yts hiY ivB gs pd T dz ch = true) :
    taPieceOKN g A r' tn td u v yts hiY ivB gs pd T dz = true := by
  unfold taPieceOKNT at hh
  unfold taPieceOKN tboundD
  rw [Bool.and_eq_true] at hh ⊢
  exact ⟨hh.1, cellsDT_sound _ _ _ _ _ _ _ _ _ hh.2⟩

/-- `checkTAPieceN` with a hinted t-bound (same `Option.any` structure). -/
def checkTAPieceNT (g : Glob) (A : ACtx) (E : EllB) (r' tn td : Nat) (u v : KCBall) (yts : List TermS)
    (hiY ivB : SI) (gs : List (List TermD)) (n0 n1 e : Nat) (ch : CHint) : Bool :=
  (piece3 ⟨g.P, g.n, g.k⟩ E n0 n1 e).any fun pd => (ptT ⟨g.P, g.n, g.k⟩ g.D pd.z).any fun T =>
    (dzOf ⟨g.P, g.n, g.k⟩ pd.z pd.rho).any fun dz => taPieceOKNT g A r' tn td u v yts hiY ivB gs pd T dz ch

theorem any_mono {α : Type} {o : Option α} {p q : α → Bool} (hpq : ∀ a, p a = true → q a = true)
    (hp : o.any p = true) : o.any q = true := by
  cases o with
  | none => simp at hp
  | some a => exact hpq a hp

theorem checkTAPieceNT_sound {g : Glob} {A : ACtx} {E : EllB} {r' tn td : Nat} {u v : KCBall} {yts : List TermS}
    {hiY ivB : SI} {gs : List (List TermD)} {n0 n1 e : Nat} {ch : CHint}
    (hh : checkTAPieceNT g A E r' tn td u v yts hiY ivB gs n0 n1 e ch = true) :
    checkTAPieceN g A E r' tn td u v yts hiY ivB gs n0 n1 e = true :=
  any_mono (fun _ h1 => any_mono (fun _ h2 => any_mono (fun _ h3 => taPieceOKNT_sound h3) h2) h1) hh

/-- `checkTAN` following a piece hint. -/
def checkTANT (g : Glob) (A : ACtx) (E : EllB) (r' tn td : Nat) (u v : KCBall) (yts : List TermS)
    (hiY ivB : SI) (gs : List (List TermD)) : Nat → Nat → Nat → Nat → PHint → Bool
  | _, n0, n1, e, .piece ch => checkTAPieceNT g A E r' tn td u v yts hiY ivB gs n0 n1 e ch
  | 0, _, _, _, .split _ _ => false
  | fuel + 1, n0, n1, e, .split l r =>
    checkTANT g A E r' tn td u v yts hiY ivB gs fuel (Nat.mul 2 n0) (Nat.add n0 n1) (Nat.add e 1) l &&
      checkTANT g A E r' tn td u v yts hiY ivB gs fuel (Nat.add n0 n1) (Nat.mul 2 n1) (Nat.add e 1) r

theorem checkTANT_sound (g : Glob) (A : ACtx) (E : EllB) (r' tn td : Nat) (u v : KCBall) (yts : List TermS)
    (hiY ivB : SI) (gs : List (List TermD)) : ∀ (fuel n0 n1 e : Nat) (ph : PHint),
    checkTANT g A E r' tn td u v yts hiY ivB gs fuel n0 n1 e ph = true →
    checkTAN g A E r' tn td u v yts hiY ivB gs fuel n0 n1 e = true
  | 0, n0, n1, e, .piece ch, hh => by
    simp only [checkTANT] at hh
    simp only [checkTAN]
    exact checkTAPieceNT_sound hh
  | fuel + 1, n0, n1, e, .piece ch, hh => by
    simp only [checkTANT] at hh
    simp only [checkTAN, checkTAPieceNT_sound hh, Bool.true_or]
  | 0, _, _, _, .split _ _, hh => by simp [checkTANT] at hh
  | fuel + 1, n0, n1, e, .split l r, hh => by
    simp only [checkTANT, Bool.and_eq_true] at hh
    simp only [checkTAN]
    rw [checkTANT_sound g A E r' tn td u v yts hiY ivB gs fuel _ _ _ l hh.1,
      checkTANT_sound g A E r' tn td u v yts hiY ivB gs fuel _ _ _ r hh.2]
    simp

/-- `taOKN` at tube level 0 with a piece hint. -/
def taOKNT (gn : GlobN) (A : ACtx) (E : EllB) (r' tn td : Nat) (B : List Box4) (tcs : List TubeC) (q0 q1 : Nat)
    (u v : Int × Int) (ys vts : List (Int × Int)) (ph : PHint) : Bool :=
  blt q0 q1 && Nat.ble q1 (Nat.pow 2 gn.g.EQ) &&
    (SI.le (reConjHi gn.g.P (intC gn.g.P v) A.Sc) (SI.ofNat 0) || isZ2 v) &&
    (ivSum gn true tcs vts).any fun ivB =>
      decide (0 ∈ levels gn tcs) &&
      checkTANT gn.g A E r' tn td (intC gn.g.P u) (intC gn.g.P v) (yTerms gn.g.P true A.pins ys) (sumBox true B ys)
        ivB (ivGroups gn.g.P true 0 tcs vts) gn.g.dT q0 q1 gn.g.EQ ph

theorem taOKNT_sound {gn : GlobN} {A : ACtx} {E : EllB} {r' tn td : Nat} {B : List Box4} {tcs : List TubeC}
    {q0 q1 : Nat} {u v : Int × Int} {ys vts : List (Int × Int)} {ph : PHint}
    (hh : taOKNT gn A E r' tn td B tcs q0 q1 u v ys vts ph = true) :
    taOKN gn A E r' tn td B tcs q0 q1 u v ys vts = true := by
  unfold taOKNT at hh
  unfold taOKN
  rw [Bool.and_eq_true] at hh ⊢
  refine ⟨hh.1, any_mono (fun ivB hb => ?_) hh.2⟩
  rw [Bool.and_eq_true, decide_eq_true_eq] at hb
  exact List.any_eq_true.2 ⟨0, hb.1, checkTANT_sound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb.2⟩

/-- A step of the walk with a piece hint (used for W1 records; hard arcs ignore it), as `stepOK`. -/
def stepOKT (gn : GlobN) (A : ACtx) (E : EllB) (r' tn td : Nat) (B : List Box4) (tcs : List TubeC) (σ : WState)
    (ph : PHint) : Bool :=
  match σ.2.2.2 with
  | (a, b) :: _ =>
    cond (Nat.beq a σ.2.1) (blt σ.2.1 b && Nat.ble b (Nat.pow 2 gn.g.EQ)) (w1OKT gn A E r' tn td B tcs σ.1 σ.2.1 σ.2.2.1 ph)
  | [] => w1OKT gn A E r' tn td B tcs σ.1 σ.2.1 σ.2.2.1 ph
where
  w1OKT (gn : GlobN) (A : ACtx) (E : EllB) (r' tn td : Nat) (B : List Box4) (tcs : List TubeC) (N q s : Nat)
      (ph : PHint) : Bool :=
    match N with
    | 0 => false
    | _ + 1 =>
      taOKNT gn A E r' tn td B tcs q (rdTAN A.pins.length tcs.length s).1 (rdTAN A.pins.length tcs.length s).2.1
        (rdTAN A.pins.length tcs.length s).2.2.1 (rdTAN A.pins.length tcs.length s).2.2.2.1
        (rdTAN A.pins.length tcs.length s).2.2.2.2.1 ph

theorem w1OKT_sound {gn : GlobN} {A : ACtx} {E : EllB} {r' tn td : Nat} {B : List Box4} {tcs : List TubeC}
    {N q s : Nat} {ph : PHint} (hh : stepOKT.w1OKT gn A E r' tn td B tcs N q s ph = true) :
    w1OK gn A E r' tn td B tcs N q s = true := by
  cases N with
  | zero => simp [stepOKT.w1OKT] at hh
  | succ N' =>
    simp only [stepOKT.w1OKT] at hh
    simp only [w1OK]
    exact taOKNT_sound hh

theorem stepOKT_sound {gn : GlobN} {A : ACtx} {E : EllB} {r' tn td : Nat} {B : List Box4} {tcs : List TubeC}
    {σ : WState} {ph : PHint} (hh : stepOKT gn A E r' tn td B tcs σ ph = true) :
    stepOK gn A E r' tn td B tcs σ = true := by
  obtain ⟨N, q, s, hs⟩ := σ
  unfold stepOKT at hh
  unfold stepOK
  cases hs with
  | nil => exact w1OKT_sound hh
  | cons ab hs' =>
    obtain ⟨a, b⟩ := ab
    simp only at hh ⊢
    cases hab : Nat.beq a q
    · simp only [hab, Bool.cond_false] at hh ⊢
      exact w1OKT_sound hh
    · simp only [hab, Bool.cond_true] at hh ⊢
      exact hh

/-- `walkSeg` with one hint per step. -/
def walkSegT (gn : GlobN) (A : ACtx) (E : EllB) (r' tn td : Nat) (B : List Box4) (tcs : List TubeC) :
    List PHint → WState → Bool
  | [], _ => true
  | ph :: phs, σ => !(Nat.beq σ.2.1 (Nat.pow 2 gn.g.EQ)) && stepOKT gn A E r' tn td B tcs σ ph &&
      walkSegT gn A E r' tn td B tcs phs (stepState A tcs σ)

theorem walkSegT_sound {gn : GlobN} {A : ACtx} {E : EllB} {r' tn td : Nat} {B : List Box4} {tcs : List TubeC} :
    ∀ (phs : List PHint) (σ : WState), walkSegT gn A E r' tn td B tcs phs σ = true →
      walkSeg gn A E r' tn td B tcs phs.length σ = true
  | [], _, _ => rfl
  | ph :: phs, σ, hh => by
    simp only [walkSegT, Bool.and_eq_true] at hh
    obtain ⟨⟨hq, hok⟩, hrest⟩ := hh
    simp only [walkSeg, List.length_cons, Bool.and_eq_true]
    exact ⟨⟨hq, stepOKT_sound hok⟩, walkSegT_sound phs _ hrest⟩

/-- The hinted segment test (as `segF`, one hint per step). -/
def segFT (gn : GlobN) (J : Nat) (phs : List PHint) :
    ACtx → List (Nat × Nat × Nat) → WHdr → Nat → Nat → List (Nat × Nat) → EllB × Nat × List TubeC → Bool :=
  fun A bx h n dat hards w =>
    decide (J + phs.length ≤ n + hards.length) &&
      walkSegT gn A w.1 w.2.1 h.tw.n.toNat h.tw.d (pinBoxes gn.g.P A.pins bx) w.2.2 phs
        (skipN A w.2.2 J (n, 0, dat, hards))

theorem segF_of_segFT {gn : GlobN} {s0 s1 sc : Nat} {pins : List (Q × Q)} {Rs : List Q} {rX : Nat} {p : List Nat}
    {tubes : List TubeD} {bx : List (Nat × Nat × Nat)} {t : NTree} {J : Nat} {phs : List PHint}
    (hh : leafAny gn s0 s1 sc pins Rs rX p tubes bx t (segFT gn J phs) = true) :
    leafAny gn s0 s1 sc pins Rs rX p tubes bx t (segF gn J phs.length) = true :=
  leafAny_mono (fun A b h n d hards w hw => by
    simp only [segFT, segF, Bool.and_eq_true] at hw ⊢
    exact ⟨hw.1, walkSegT_sound phs _ hw.2⟩) hh

end C64KChk
