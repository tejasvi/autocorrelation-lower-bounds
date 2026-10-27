import C64K.KParts

/-!
# Segments of the tile-arc walk of a W leaf (core Lean only)

The local check of a W leaf, `witLocalN`, is its head (the exact checks, the representative in the node set, the radius,
the crossing disc, the pins, the winding number, the tube data) and the walk `walkTA` over its tile arcs: hard arcs and
W1 records, in the order of `q`.  For a leaf with many records the walk splits into segments of `k` steps, each its own
kernel theorem:
* `stepState` / `stepOK`: one step of the walk from the state `σ = (N, q, s, hs)` (`N` records left in the data `s`,
  current point `q`, remaining hard arcs `hs`), and its check;
* `walkSeg k σ`: `k` steps from `σ`, each before the end `q = 1`, each passing; `skipN k σ`: the state after `k` steps
  (decoding only);
* `walkSigma_of_seg`: `walkSeg k σ` and the walk from `skipN k σ` give the walk from `σ` (with `k` more fuel);
* `witLocalN_eq`: `witLocalN = witHead && (walkCtx ..).any (walk)`, so the local check of a W leaf is its head and its
  walk, the walk being given by segments (`partOK_wit_of`).
-/

namespace C64KChk

open KIval KIval.KBall KNum C64Chk

/-- A state of the walk: records left `N`, current point `q`, the data `s`, the remaining hard arcs `hs`. -/
abbrev WState := Nat × Nat × Nat × List (Nat × Nat)

/-- The state after the next W1 record (no change without records). -/
def w1State (A : ACtx) (tcs : List TubeC) (N q s : Nat) (hs : List (Nat × Nat)) : WState :=
  match N with
  | 0 => (0, q, s, hs)
  | N' + 1 => ((N', (rdTAN A.pins.length tcs.length s).1, (rdTAN A.pins.length tcs.length s).2.2.2.2.2, hs))

/-- The check of the next W1 record. -/
def w1OK (gn : GlobN) (A : ACtx) (E : EllB) (r' tn td : Nat) (B : List Box4) (tcs : List TubeC) (N q s : Nat) : Bool :=
  match N with
  | 0 => false
  | _ + 1 =>
    taOKN gn A E r' tn td B tcs q (rdTAN A.pins.length tcs.length s).1 (rdTAN A.pins.length tcs.length s).2.1
      (rdTAN A.pins.length tcs.length s).2.2.1 (rdTAN A.pins.length tcs.length s).2.2.2.1
      (rdTAN A.pins.length tcs.length s).2.2.2.2.1

/-- The state after one step: the hard arc `[q, b]` at the head of `hs`, else the next W1 record. -/
def stepState (A : ACtx) (tcs : List TubeC) (σ : WState) : WState :=
  match σ.2.2.2 with
  | (a, b) :: hs' => cond (Nat.beq a σ.2.1) (σ.1, b, σ.2.2.1, hs') (w1State A tcs σ.1 σ.2.1 σ.2.2.1 σ.2.2.2)
  | [] => w1State A tcs σ.1 σ.2.1 σ.2.2.1 σ.2.2.2

/-- The check of one step. -/
def stepOK (gn : GlobN) (A : ACtx) (E : EllB) (r' tn td : Nat) (B : List Box4) (tcs : List TubeC) (σ : WState) : Bool :=
  match σ.2.2.2 with
  | (a, b) :: _ =>
    cond (Nat.beq a σ.2.1) (blt σ.2.1 b && Nat.ble b (Nat.pow 2 gn.g.EQ)) (w1OK gn A E r' tn td B tcs σ.1 σ.2.1 σ.2.2.1)
  | [] => w1OK gn A E r' tn td B tcs σ.1 σ.2.1 σ.2.2.1

/-- `k` steps from `σ`, each before the end of the walk, each passing. -/
def walkSeg (gn : GlobN) (A : ACtx) (E : EllB) (r' tn td : Nat) (B : List Box4) (tcs : List TubeC) :
    Nat → WState → Bool
  | 0, _ => true
  | k + 1, σ => !(Nat.beq σ.2.1 (Nat.pow 2 gn.g.EQ)) && stepOK gn A E r' tn td B tcs σ &&
      walkSeg gn A E r' tn td B tcs k (stepState A tcs σ)

/-- The state after `k` steps (decoding only). -/
def skipN (A : ACtx) (tcs : List TubeC) : Nat → WState → WState
  | 0, σ => σ
  | k + 1, σ => skipN A tcs k (stepState A tcs σ)

/-- The walk from a state. -/
def walkSigma (gn : GlobN) (A : ACtx) (E : EllB) (r' tn td : Nat) (B : List Box4) (tcs : List TubeC) (fuel : Nat)
    (σ : WState) : Bool :=
  walkTA gn A E r' tn td B tcs fuel σ.1 σ.2.1 σ.2.2.1 σ.2.2.2

theorem walkTA_step {gn : GlobN} {A : ACtx} {E : EllB} {r' tn td : Nat} {B : List Box4} {tcs : List TubeC}
    (fuel N q s : Nat) (hs : List (Nat × Nat)) (hq : Nat.beq q (Nat.pow 2 gn.g.EQ) = false) :
    walkTA gn A E r' tn td B tcs (fuel + 1) N q s hs =
      (stepOK gn A E r' tn td B tcs (N, q, s, hs) &&
        walkSigma gn A E r' tn td B tcs fuel (stepState A tcs (N, q, s, hs))) := by
  simp only [walkTA, hq, Bool.cond_false, stepOK, stepState, walkSigma]
  cases hs with
  | nil => cases N <;> simp [walkW1, w1OK, w1State]
  | cons ab hs' =>
    obtain ⟨a, b⟩ := ab
    cases hab : Nat.beq a q
    · simp only [hab, Bool.cond_false]
      cases N <;> simp [walkW1, w1OK, w1State]
    · simp only [hab, Bool.cond_true, Bool.and_assoc]

/-- Glue: a segment of `k` steps and the walk after it give the walk from the start of the segment. -/
theorem walkSigma_of_seg {gn : GlobN} {A : ACtx} {E : EllB} {r' tn td : Nat} {B : List Box4} {tcs : List TubeC} :
    ∀ (k fuel : Nat) (σ : WState), walkSeg gn A E r' tn td B tcs k σ = true →
      walkSigma gn A E r' tn td B tcs fuel (skipN A tcs k σ) = true →
      walkSigma gn A E r' tn td B tcs (fuel + k) σ = true
  | 0, _, _, _, h => h
  | k + 1, fuel, σ, hs, h => by
    obtain ⟨N, q, s, hh⟩ := σ
    simp only [walkSeg, Bool.and_eq_true, Bool.not_eq_true'] at hs
    obtain ⟨⟨hq, hok⟩, hrest⟩ := hs
    have ih := walkSigma_of_seg k fuel _ hrest h
    show walkTA gn A E r' tn td B tcs (fuel + k + 1) N q s hh = true
    rw [walkTA_step _ _ _ _ _ hq, hok, ih]
    rfl

/-! ## Head and walk of a W leaf -/

/-- The context of the walk of a W leaf: tile, radius and tube data. -/
def walkCtx (gn : GlobN) (A : ACtx) (tubes : List TubeD) (h : WHdr) : Option (EllB × Nat × List TubeC) :=
  (tileOf gn.g h.ti).bind fun E =>
    (rBound gn.g A.E1 h.tw.n.toNat h.tw.d A.s0 A.s1 A.sc A.zc A.Sc A.S1c h.rX).bind fun r' =>
      (tubes.mapM (tubeC gn)).map fun tcs => (E, r', tcs)

/-- The local check of a W leaf without its walk. -/
def witHead (gn : GlobN) (A : ACtx) (tubes : List TubeD) (bx : List (Nat × Nat × Nat)) (h : WHdr) : Bool :=
  (tileOf gn.g h.ti).any fun E => (atomsOK h.as).any fun mm =>
    decide (0 < h.tw.n) && decide (0 < h.tw.d) && decide (gn.g.tau.n * h.tw.d ≤ h.tw.n * gn.g.tau.d) &&
    decide (mm.1 * h.tw.d ≤ h.tw.n * mm.2) && decide (0 < h.sg.d) && decide ((h.sg.d : Int) ≤ h.sg.n) &&
    decide (h.mus.length = tubes.length) && (tubes.zip h.mus).all (fun x => tubeRepOK gn h.as x.1 x.2) &&
    (rBound gn.g A.E1 h.tw.n.toNat h.tw.d A.s0 A.s1 A.sc A.zc A.Sc A.S1c h.rX).any fun r' =>
      (sumK ⟨gn.g.P, gn.g.n, gn.g.k⟩ A.zc h.as).any fun wz =>
        Nat.ble A.r r' && Nat.ble (normHi (KNum.KCBall.sub wz (KNum.KCBall.mulR gn.g.P (qBall gn.g.P h.sg) A.Sc))) r' &&
        pinsIn ⟨gn.g.P, gn.g.n, gn.g.k⟩ h.as A.pins (pinBoxes gn.g.P A.pins bx) &&
        windOdd gn.g E h.as (KIval.KBall.cdiv (Nat.mul mm.1.toNat (Nat.pow 2 gn.g.P)) mm.2) &&
        (tubes.mapM (tubeC gn)).isSome

/-- The walk of a W leaf in its context. -/
def witWalk (gn : GlobN) (A : ACtx) (tubes : List TubeD) (bx : List (Nat × Nat × Nat)) (h : WHdr) (n dat : Nat)
    (hards : List (Nat × Nat)) : Bool :=
  (walkCtx gn A tubes h).any fun c =>
    walkTA gn A c.1 c.2.1 h.tw.n.toNat h.tw.d (pinBoxes gn.g.P A.pins bx) c.2.2 (Nat.add (Nat.add n hards.length) 1)
      n 0 dat hards

theorem any_and_const {α : Type} (o : Option α) (f : α → Bool) (b : Bool) :
    o.any (fun x => f x && b) = (o.any f && b) := by
  cases o <;> simp

theorem witLocalN_eq (gn : GlobN) (A : ACtx) (tubes : List TubeD) (bx : List (Nat × Nat × Nat)) (h : WHdr)
    (n dat : Nat) (hards : List (Nat × Nat)) :
    witLocalN gn A tubes bx h n dat hards = (witHead gn A tubes bx h && witWalk gn A tubes bx h n dat hards) := by
  simp only [witLocalN, witHead, witWalk, walkCtx]
  cases tileOf gn.g h.ti with
  | none => rfl
  | some E =>
    simp only [Option.any_some, Option.bind_some]
    cases atomsOK h.as with
    | none =>
      simp only [Option.any_none, Bool.false_and]
    | some mm =>
      simp only [Option.any_some]
      cases rBound gn.g A.E1 h.tw.n.toNat h.tw.d A.s0 A.s1 A.sc A.zc A.Sc A.S1c h.rX with
      | none => simp
      | some r' =>
        simp only [Option.any_some, Option.bind_some]
        cases sumK ⟨gn.g.P, gn.g.n, gn.g.k⟩ A.zc h.as with
        | none => simp
        | some wz =>
          simp only [Option.any_some]
          cases tubes.mapM (tubeC gn) with
          | none => simp
          | some tcs => simp only [Option.any_some, Option.isSome_some, Option.map_some, Bool.and_true,
              Bool.and_assoc]

/-- The head check of the W node at the path `p` (`false` for other nodes). -/
def headAt (gn : GlobN) (A : ACtx) (p : List Nat) (tubes : List TubeD) (bx : List (Nat × Nat × Nat)) (t : NTree) :
    Bool :=
  (nodeAt p tubes bx t).any fun c => match c.2.2 with
    | .wit h _ _ hards kids => witHead gn A c.1 c.2.1 h && decide (kids.length = hards.length)
    | _ => false

/-- The local check of a W node at the path `p` from its head and its walk (e.g. by segments). -/
theorem partOK_wit_of {gn : GlobN} {A : ACtx} {p : List Nat} {tubes : List TubeD} {bx : List (Nat × Nat × Nat)}
    {t : NTree} (hhead : (nodeAt p tubes bx t).any (fun c => match c.2.2 with
      | .wit h _ _ hards kids => witHead gn A c.1 c.2.1 h && decide (kids.length = hards.length)
      | _ => false) = true)
    (hwalk : (nodeAt p tubes bx t).any (fun c => match c.2.2 with
      | .wit h n dat hards _ => witWalk gn A c.1 c.2.1 h n dat hards
      | _ => false) = true) :
    partOK gn A p tubes bx t = true := by
  unfold partOK
  cases hn : nodeAt p tubes bx t with
  | none => rw [hn] at hhead; simp at hhead
  | some c =>
    rw [hn] at hhead hwalk
    simp only [Option.any_some] at hhead hwalk ⊢
    obtain ⟨tb, b, nd⟩ := c
    cases nd with
    | wit h n dat hards kids =>
      simp only [Bool.and_eq_true] at hhead
      simp only [localOK, witLocalN_eq, Bool.and_eq_true]
      exact ⟨⟨hhead.1, hwalk⟩, hhead.2⟩
    | empty => simp at hhead
    | split => simp at hhead
    | ivsplit => simp at hhead
    | ext => simp at hhead

/-! ## Segments of a leaf's walk under the arc context -/

theorem skipN_add (A : ACtx) (tcs : List TubeC) : ∀ (j k : Nat) (σ : WState),
    skipN A tcs (j + k) σ = skipN A tcs k (skipN A tcs j σ)
  | 0, k, σ => by simp [skipN]
  | j + 1, k, σ => by
    rw [show j + 1 + k = j + k + 1 by omega]
    simp only [skipN]
    exact skipN_add A tcs j k _

/-- A test `F` of the walk context of the W leaf at the path `p`, under the arc context. -/
def leafAny (gn : GlobN) (s0 s1 sc : Nat) (pins : List (Q × Q)) (Rs : List Q) (rX : Nat) (p : List Nat)
    (tubes : List TubeD) (bx : List (Nat × Nat × Nat)) (t : NTree)
    (F : ACtx → List (Nat × Nat × Nat) → WHdr → Nat → Nat → List (Nat × Nat) → EllB × Nat × List TubeC → Bool) :
    Bool :=
  (arcCtx gn.g s0 s1 sc pins Rs rX).any fun A => (nodeAt p tubes bx t).any fun c =>
    match c.2.2 with
    | .wit h n dat hards _ => (walkCtx gn A c.1 h).any fun w => F A c.2.1 h n dat hards w
    | _ => false

theorem leafAny_and {gn : GlobN} {s0 s1 sc : Nat} {pins : List (Q × Q)} {Rs : List Q} {rX : Nat} {p : List Nat}
    {tubes : List TubeD} {bx : List (Nat × Nat × Nat)} {t : NTree} {F G}
    (hF : leafAny gn s0 s1 sc pins Rs rX p tubes bx t F = true)
    (hG : leafAny gn s0 s1 sc pins Rs rX p tubes bx t G = true) :
    leafAny gn s0 s1 sc pins Rs rX p tubes bx t (fun A b h n d hs w => F A b h n d hs w && G A b h n d hs w) = true := by
  unfold leafAny at *
  revert hF hG
  generalize arcCtx gn.g s0 s1 sc pins Rs rX = oA
  intro hF hG
  cases oA with
  | none => simp at hF
  | some A =>
    simp only [Option.any_some] at *
    revert hF hG
    generalize nodeAt p tubes bx t = oc
    intro hF hG
    cases oc with
    | none => simp at hF
    | some c =>
      simp only [Option.any_some] at *
      obtain ⟨tb, b, nd⟩ := c
      cases nd with
      | wit h n dat hards kids =>
        simp only at *
        revert hF hG
        generalize walkCtx gn A tb h = ow
        intro hF hG
        cases ow with
        | none => simp at hF
        | some w => simp only [Option.any_some, Bool.and_eq_true] at *; exact ⟨hF, hG⟩
      | _ => simp at hF

theorem leafAny_mono {gn : GlobN} {s0 s1 sc : Nat} {pins : List (Q × Q)} {Rs : List Q} {rX : Nat} {p : List Nat}
    {tubes : List TubeD} {bx : List (Nat × Nat × Nat)} {t : NTree} {F G}
    (hFG : ∀ A b h n d hs w, F A b h n d hs w = true → G A b h n d hs w = true)
    (hF : leafAny gn s0 s1 sc pins Rs rX p tubes bx t F = true) :
    leafAny gn s0 s1 sc pins Rs rX p tubes bx t G = true := by
  unfold leafAny at *
  revert hF
  generalize arcCtx gn.g s0 s1 sc pins Rs rX = oA
  intro hF
  cases oA with
  | none => simp at hF
  | some A =>
    simp only [Option.any_some] at *
    revert hF
    generalize nodeAt p tubes bx t = oc
    intro hF
    cases oc with
    | none => simp at hF
    | some c =>
      simp only [Option.any_some] at *
      obtain ⟨tb, b, nd⟩ := c
      cases nd with
      | wit h n dat hards kids =>
        simp only at *
        revert hF
        generalize walkCtx gn A tb h = ow
        intro hF
        cases ow with
        | none => simp at hF
        | some w => simp only [Option.any_some] at *; exact hFG _ _ _ _ _ _ _ hF
      | _ => simp at hF

/-- The segment of `k` steps after the first `J` steps of the leaf's walk (within its `n + |hards|` steps). -/
def segF (gn : GlobN) (J k : Nat) :
    ACtx → List (Nat × Nat × Nat) → WHdr → Nat → Nat → List (Nat × Nat) → EllB × Nat × List TubeC → Bool :=
  fun A bx h n dat hards w =>
    decide (J + k ≤ n + hards.length) &&
      walkSeg gn A w.1 w.2.1 h.tw.n.toNat h.tw.d (pinBoxes gn.g.P A.pins bx) w.2.2 k (skipN A w.2.2 J (n, 0, dat, hards))

/-- The rest of the leaf's walk after its first `J` steps (with the remaining fuel of `witLocalN`). -/
def restF (gn : GlobN) (J : Nat) :
    ACtx → List (Nat × Nat × Nat) → WHdr → Nat → Nat → List (Nat × Nat) → EllB × Nat × List TubeC → Bool :=
  fun A bx h n dat hards w =>
    walkSigma gn A w.1 w.2.1 h.tw.n.toNat h.tw.d (pinBoxes gn.g.P A.pins bx) w.2.2 (n + hards.length + 1 - J)
      (skipN A w.2.2 J (n, 0, dat, hards))

/-- Glue: a segment of `k` steps after `J` steps and the rest after `J + k` steps give the rest after `J` steps. -/
theorem rest_of_seg {gn : GlobN} {s0 s1 sc : Nat} {pins : List (Q × Q)} {Rs : List Q} {rX : Nat} {p : List Nat}
    {tubes : List TubeD} {bx : List (Nat × Nat × Nat)} {t : NTree} {J k : Nat}
    (hs : leafAny gn s0 s1 sc pins Rs rX p tubes bx t (segF gn J k) = true)
    (hr : leafAny gn s0 s1 sc pins Rs rX p tubes bx t (restF gn (J + k)) = true) :
    leafAny gn s0 s1 sc pins Rs rX p tubes bx t (restF gn J) = true := by
  refine leafAny_mono (fun A b h n d hs' w hw => ?_) (leafAny_and hs hr)
  simp only [segF, restF, Bool.and_eq_true, decide_eq_true_eq] at hw ⊢
  obtain ⟨⟨hle, hseg⟩, hrest⟩ := hw
  rw [skipN_add] at hrest
  have := walkSigma_of_seg k _ _ hseg hrest
  rwa [show n + hs'.length + 1 - (J + k) + k = n + hs'.length + 1 - J by omega] at this

/-- The local check of the W node at the path `p`, under the arc context, from its head and the rest of its walk after
`0` steps. -/
theorem partAny_wit_of {gn : GlobN} {s0 s1 sc : Nat} {pins : List (Q × Q)} {Rs : List Q} {rX : Nat} {p : List Nat}
    {tubes : List TubeD} {bx : List (Nat × Nat × Nat)} {t : NTree}
    (hhead : (arcCtx gn.g s0 s1 sc pins Rs rX).any (fun A => headAt gn A p tubes bx t) = true)
    (hwalk : leafAny gn s0 s1 sc pins Rs rX p tubes bx t (restF gn 0) = true) :
    (arcCtx gn.g s0 s1 sc pins Rs rX).any (fun A => partOK gn A p tubes bx t) = true := by
  unfold leafAny at hwalk
  cases hA : arcCtx gn.g s0 s1 sc pins Rs rX with
  | none => rw [hA] at hhead; simp at hhead
  | some A =>
    rw [hA] at hhead hwalk
    simp only [Option.any_some] at hhead hwalk ⊢
    refine partOK_wit_of (by simpa only [headAt] using hhead) ?_
    cases hn : nodeAt p tubes bx t with
    | none => rw [hn] at hwalk; simp at hwalk
    | some c =>
      rw [hn] at hwalk
      simp only [Option.any_some] at hwalk ⊢
      obtain ⟨tb, b, nd⟩ := c
      cases nd with
      | wit h n dat hards kids =>
        simp only [restF, Nat.sub_zero, skipN] at hwalk
        simpa only [witWalk, walkSigma, Nat.add_eq] using hwalk
      | empty => simp at hwalk
      | split => simp at hwalk
      | ivsplit => simp at hwalk
      | ext => simp at hwalk

end C64KChk
