import C64.Check.SoundNW
import C64.Check.SoundMain

/-!
# Soundness of the nested checker, part 5: trees, arcs and the main theorem

`checkN_ok` is Proposition 6.12 (with interval tubes) as an induction over the tree: every node set of the tree is settled,
given the facts at the `ext` positions (subtrees certified by separate statements, `ExtOK`).  `extList` computes the
contexts of the `ext` positions, so that an assembly can supply them from the statements `checkSubN … = true` of the
subtree modules (`checkSubN_ok`).  `main_of_checksN` gives `ess sup (f ⋆ f) > (∫ f)² / (1 - τ)`.
-/

namespace C64Chk

open Ival Ival.Ball C64Num Real MeasureTheory

/-! ### `ext` positions -/

/-- The facts `Q tubes boxes` required at the `ext` positions of a tree. -/
def ExtOK (Q : List TubeD → List (ℕ × ℕ × ℕ) → Prop) : ℕ → List TubeD → List (ℕ × ℕ × ℕ) → NTree → Prop
  | 0, _, _, _ => True
  | _ + 1, _, _, .empty _ _ _ => True
  | fuel + 1, tubes, bx, .wit h _ _ hards kids =>
      ∀ x ∈ hards.zip kids, ExtOK Q fuel (tubes ++ [⟨h.ti, x.1.1, x.1.2, h.as⟩]) bx x.2
  | fuel + 1, tubes, bx, .split j c0 c1 c2 c3 =>
      ExtOK Q fuel tubes (bx.set j (kid (bx.getD j (0, 0, 0)) 0)) c0 ∧
      ExtOK Q fuel tubes (bx.set j (kid (bx.getD j (0, 0, 0)) 1)) c1 ∧
      ExtOK Q fuel tubes (bx.set j (kid (bx.getD j (0, 0, 0)) 2)) c2 ∧
      ExtOK Q fuel tubes (bx.set j (kid (bx.getD j (0, 0, 0)) 3)) c3
  | fuel + 1, tubes, bx, .ivsplit k qm lo hi =>
      match tubes[k]? with
      | some tb => ExtOK Q fuel (tubes.set k { tb with q1 := qm }) bx lo ∧
          ExtOK Q fuel (tubes.set k { tb with q0 := qm }) bx hi
      | none => True
  | _ + 1, tubes, bx, .ext => Q tubes bx

/-- The contexts `(tubes, boxes)` of the `ext` positions of a tree. -/
def extList : ℕ → List TubeD → List (ℕ × ℕ × ℕ) → NTree → List (List TubeD × List (ℕ × ℕ × ℕ))
  | 0, _, _, _ => []
  | _ + 1, _, _, .empty _ _ _ => []
  | fuel + 1, tubes, bx, .wit h _ _ hards kids =>
      ((hards.zip kids).map fun x => extList fuel (tubes ++ [⟨h.ti, x.1.1, x.1.2, h.as⟩]) bx x.2).flatten
  | fuel + 1, tubes, bx, .split j c0 c1 c2 c3 =>
      extList fuel tubes (bx.set j (kid (bx.getD j (0, 0, 0)) 0)) c0 ++
      extList fuel tubes (bx.set j (kid (bx.getD j (0, 0, 0)) 1)) c1 ++
      extList fuel tubes (bx.set j (kid (bx.getD j (0, 0, 0)) 2)) c2 ++
      extList fuel tubes (bx.set j (kid (bx.getD j (0, 0, 0)) 3)) c3
  | fuel + 1, tubes, bx, .ivsplit k qm lo hi =>
      match tubes[k]? with
      | some tb => extList fuel (tubes.set k { tb with q1 := qm }) bx lo ++
          extList fuel (tubes.set k { tb with q0 := qm }) bx hi
      | none => []
  | _ + 1, tubes, bx, .ext => [(tubes, bx)]

theorem extList_ok {Q : List TubeD → List (ℕ × ℕ × ℕ) → Prop} : ∀ (fuel : ℕ) (tubes : List TubeD)
    (bx : List (ℕ × ℕ × ℕ)) (t : NTree), (∀ c ∈ extList fuel tubes bx t, Q c.1 c.2) → ExtOK Q fuel tubes bx t
  | 0, _, _, _, _ => trivial
  | _ + 1, _, _, .empty _ _ _, _ => trivial
  | fuel + 1, tubes, bx, .wit h _ _ hards kids, hc => by
    intro x hx
    exact extList_ok fuel _ bx x.2 (fun c hc' => hc c (List.mem_flatten.2 ⟨_, List.mem_map_of_mem hx, hc'⟩))
  | fuel + 1, tubes, bx, .split j c0 c1 c2 c3, hc => by
    simp only [extList, List.mem_append] at hc
    exact ⟨extList_ok fuel _ _ c0 (fun c h' => hc c (Or.inl (Or.inl (Or.inl h')))),
      extList_ok fuel _ _ c1 (fun c h' => hc c (Or.inl (Or.inl (Or.inr h')))),
      extList_ok fuel _ _ c2 (fun c h' => hc c (Or.inl (Or.inr h'))),
      extList_ok fuel _ _ c3 (fun c h' => hc c (Or.inr h'))⟩
  | fuel + 1, tubes, bx, .ivsplit k qm lo hi, hc => by
    unfold extList at hc
    unfold ExtOK
    split
    · rename_i tb htb
      rw [htb] at hc
      simp only [List.mem_append] at hc
      exact ⟨extList_ok fuel _ _ lo (fun c h' => hc c (Or.inl h')),
        extList_ok fuel _ _ hi (fun c h' => hc c (Or.inr h'))⟩
    · trivial
  | _ + 1, tubes, bx, .ext, hc => hc (tubes, bx) (by simp [extList])

/-! ### The tree (Proposition 6.12) -/

/-- The fact at an `ext` position: the node set is settled. -/
noncomputable def Qof (gn : GlobN) (zc : ℂ) (r : ℝ) (ps : List ℂ) (pins : List (CBall × PtT × Q)) :
    List TubeD → List (ℕ × ℕ × ℕ) → Prop :=
  fun tubes bx => C64.NodeSettled gn.g.tau.val zc r (pqL ps pins bx) gn.eps.val (tubes.map (tubeR gn.g))

theorem checkN_ok {gn : GlobN} (hgn : GlobNOK gn) {A : ACtx} {zc : ℂ} {ps : List ℂ} (hA : ACtxOK gn.g A zc ps)
    (hR : ∀ pb ∈ A.pins, 0 ≤ pb.2.2.val) :
    ∀ (fuel : ℕ) (tubes : List TubeD) (bx : List (ℕ × ℕ × ℕ)) (t : NTree), bx.length = ps.length →
    checkN gn A fuel tubes bx t = true → ExtOK (Qof gn zc ((A.r : ℝ) / 2 ^ gn.g.P) ps A.pins) fuel tubes bx t →
    C64.NodeSettled gn.g.tau.val zc ((A.r : ℝ) / 2 ^ gn.g.P) (pqL ps A.pins bx) gn.eps.val (tubes.map (tubeR gn.g))
  | 0, _, _, _, _, h, _ => by simp [checkN] at h
  | _ + 1, tubes, bx, .empty tw rX dat, hbx, h, _ => emptyN_ok hgn hA hbx h
  | fuel + 1, tubes, bx, .wit h n dat hards kids, hbx, hc, hext => by
    unfold checkN at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
    obtain ⟨⟨hloc, hlen⟩, hk⟩ := hc
    refine witLocalN_ok hgn hA hbx hloc (fun ab hab => ?_)
    obtain ⟨kd, hkd⟩ := exists_mem_zip hlen.symm ab hab
    exact checkN_ok hgn hA hR fuel _ bx kd hbx (hk _ hkd) (hext _ hkd)
  | fuel + 1, tubes, bx, .split j c0 c1 c2 c3, hbx, hc, hext => by
    unfold checkN at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨hj, h0⟩, h1⟩, h2⟩, h3⟩ := hc
    obtain ⟨e0, e1, e2, e3⟩ := hext
    have hlen : A.pins.length = ps.length := (List.Forall₂.length_eq hA.hpins).symm
    have hl : ∀ m, (bx.set j (kid (bx.getD j (0, 0, 0)) m)).length = ps.length := fun m => by
      rw [List.length_set, hbx]
    intro μ hμ
    obtain ⟨n, hn, hn'⟩ := pqL_split j ps A.pins bx hR hj hbx.symm (by rw [hlen, hbx]) hμ.1.2.2
    have hμ' : C64.NodeSet gn.g.tau.val zc ((A.r : ℝ) / 2 ^ gn.g.P)
        (pqL ps A.pins (bx.set j (kid (bx.getD j (0, 0, 0)) n))) gn.eps.val (tubes.map (tubeR gn.g)) μ :=
      ⟨⟨hμ.1.1, hμ.1.2.1, hn'⟩, hμ.2⟩
    interval_cases n
    · exact checkN_ok hgn hA hR fuel tubes _ c0 (hl 0) h0 e0 μ hμ'
    · exact checkN_ok hgn hA hR fuel tubes _ c1 (hl 1) h1 e1 μ hμ'
    · exact checkN_ok hgn hA hR fuel tubes _ c2 (hl 2) h2 e2 μ hμ'
    · exact checkN_ok hgn hA hR fuel tubes _ c3 (hl 3) h3 e3 μ hμ'
  | fuel + 1, tubes, bx, .ivsplit k qm lo hi, hbx, hc, hext => by
    unfold checkN at hc
    unfold ExtOK at hext
    rcases htb : tubes[k]? with _ | tb
    · rw [htb] at hc; simp at hc
    · rw [htb] at hc hext
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨hq0, hq1⟩, hlo⟩, hhi⟩ := hc
      obtain ⟨elo, ehi⟩ := hext
      have hk : (tubes.map (tubeR gn.g))[k]? = some (tubeR gn.g tb) := by
        rw [List.getElem?_map, htb]; rfl
      refine C64.nodeSettled_ivsplit hk (qm := (qm : ℝ) / 2 ^ gn.g.EQ) ?_ ?_
      · have := checkN_ok hgn hA hR fuel _ bx lo hbx hlo elo
        rw [List.map_set] at this; exact this
      · have := checkN_ok hgn hA hR fuel _ bx hi hbx hhi ehi
        rw [List.map_set] at this; exact this
  | _ + 1, tubes, bx, .ext, _, _, hext => hext

/-! ### Arcs -/

/-- The semantic content of an arc context (as in the three-level checker). -/
theorem arcCtx_sem {g : Glob} (hg : GlobOK g) {s0 s1 sc : ℕ} {pins : List (Q × Q)} {Rs : List Q} {rX : ℕ}
    (hhead : hHead g s0 s1 sc pins Rs = true) {A : ACtx} (hAc : arcCtx g s0 s1 sc pins Rs rX = some A) :
    ACtxOK g A (C64.ellipse (g.c.val : ℂ) g.a.val g.b.val ((sc : ℝ) / 2 ^ g.ES)) (pins.map pinVal) ∧
    (∀ pb ∈ A.pins, 0 ≤ pb.2.2.val) ∧
    (∀ μ : Measure ℝ, C64.ClassA g.tau.val μ → ∀ s ∈ Set.Icc ((s0 : ℝ) / 2 ^ g.ES) ((s1 : ℝ) / 2 ^ g.ES),
      ∀ lam ∈ Set.Ioc (0 : ℝ) 1, C64.S (C64.ellipse (g.c.val : ℂ) g.a.val g.b.val s) =
        lam * C64.hat μ (C64.ellipse (g.c.val : ℂ) g.a.val g.b.val s) →
      ∃ σ : ℝ, 1 ≤ σ ∧ ‖C64.hat μ (C64.ellipse (g.c.val : ℂ) g.a.val g.b.val ((sc : ℝ) / 2 ^ g.ES)) -
        (σ : ℂ) * C64.S (C64.ellipse (g.c.val : ℂ) g.a.val g.b.val ((sc : ℝ) / 2 ^ g.ES))‖ ≤ (A.r : ℝ) / 2 ^ g.P) ∧
    (∀ μ : Measure ℝ, C64.ClassA g.tau.val μ →
      ∀ x ∈ pqL (pins.map pinVal) A.pins (pins.map fun _ => ((0 : ℕ), (0 : ℕ), (0 : ℕ))),
        x.2.mem (C64.hat μ x.1)) := by
  unfold hHead at hhead
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hhead
  obtain ⟨⟨⟨⟨⟨h0c, hc1⟩, h01⟩, hlen⟩, hden⟩, hpinR⟩ := hhead
  unfold arcCtx at hAc
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hAc
  obtain ⟨zcB, hzc, ⟨Sc, S1c⟩, hss, zT, hzT, r, hr, pts, hpts, rfl⟩ := hAc
  have hP := two_pow_pos' g.P
  have hE1 := T1_ok hg
  set zc := C64.ellipse (g.c.val : ℂ) g.a.val g.b.val ((sc : ℝ) / 2 ^ g.ES)
  have hzcm : memC g.P zc zcB := by
    have := mem_dyB (P := g.P) (sc : ℤ) (show g.ES ≤ g.P by have := hg.hE; omega)
    push_cast at this
    exact memC_ellPt hE1 this hzc
  obtain ⟨-, hSc, hS1c⟩ := memC_cSS1 hzcm hss
  have hzTok := ptT_ok hzcm hg.D1 hg.hD hzT
  set ps := pins.map pinVal
  have hF := mapM_some hpts
  have hpinsF' := pins_forall2 hg pins Rs pts hlen hden hpinR hF
  have hpinsF : List.Forall₂ (fun p (pb : CBall × PtT × Q) => memC g.P p pb.1 ∧ PtOK g.P g.D p pb.2.1 ∧
      0 < pb.2.2.d) ps ((pins.map (pinBall g.P)).zip (pts.zip Rs)) :=
    hpinsF'.imp (fun _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
  have hτ0 := (tau_pos hg).le
  refine ⟨⟨hzcm, hSc, hS1c, hzTok, hpinsF⟩, forall2_snd (fun _ _ h => le_trans (mul_nonneg hτ0 (Real.exp_pos _).le)
    h.2.2.2) hpinsF', ?_, ?_⟩
  · have htd : 0 < g.tau.d := by have := lt_trans hg.tn hg.tlt; omega
    have hloc := rBound_ok hg h0c hc1 htd hzcm hSc hS1c hr
    rw [← tau_eq hg] at hloc
    exact hloc
  · intro μ hμ
    have key : ∀ (l1 : List ℂ) (l2 : List (CBall × PtT × Q)) (l0 : List (Q × Q)),
        List.Forall₂ (fun p (pb : CBall × PtT × Q) => memC g.P p pb.1 ∧ PtOK g.P g.D p pb.2.1 ∧
          0 < pb.2.2.d ∧ g.tau.val * Real.exp (π * |p.im|) ≤ pb.2.2.val) l1 l2 →
        ∀ x ∈ pqL l1 l2 (l0.map fun _ => ((0 : ℕ), (0 : ℕ), (0 : ℕ))), x.2.mem (C64.hat μ x.1) := by
      intro l1 l2 l0 hF2
      induction hF2 generalizing l0 with
      | nil => intro x hx; simp [pqL] at hx
      | @cons p pb l1 l2 hab _ ih =>
        cases l0 with
        | nil => intro x hx; simp [pqL] at hx
        | cons q l0 =>
          intro x hx
          simp only [List.map_cons, pqL, List.mem_cons] at hx
          rcases hx with rfl | hx
          · obtain ⟨hre, him⟩ := C64.pinned_bound hτ0 hμ hab.2.2.2
            exact boxR_root pb.2.2 hre him
          · exact ih l0 x hx
    exact key ps _ pins hpinsF'

/-- A subtree statement: in the context of its arc, the node set of `(tubes, boxes)` is settled. -/
def SubOK (gn : GlobN) (s0 s1 sc : ℕ) (pins : List (Q × Q)) (Rs : List Q) (rX : ℕ) (tubes : List TubeD)
    (bx : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ A, arcCtx gn.g s0 s1 sc pins Rs rX = some A →
    Qof gn (C64.ellipse (gn.g.c.val : ℂ) gn.g.a.val gn.g.b.val ((sc : ℝ) / 2 ^ gn.g.ES)) ((A.r : ℝ) / 2 ^ gn.g.P)
      (pins.map pinVal) A.pins tubes bx

/-- The `ext` facts of a subtree (or arc) tree, in terms of `SubOK`. -/
def ExtSub (gn : GlobN) (s0 s1 sc : ℕ) (pins : List (Q × Q)) (Rs : List Q) (rX : ℕ) (tubes : List TubeD)
    (bx : List (ℕ × ℕ × ℕ)) (t : NTree) : Prop :=
  ∀ c ∈ extList gn.fuel tubes bx t, SubOK gn s0 s1 sc pins Rs rX c.1 c.2

theorem checkSubN_ok {gn : GlobN} (hgn : GlobNOK gn) {s0 s1 sc : ℕ} {pins : List (Q × Q)} {Rs : List Q} {rX : ℕ}
    {tubes : List TubeD} {bx : List (ℕ × ℕ × ℕ)} {t : NTree} (hbx : bx.length = pins.length)
    (h : checkSubN gn s0 s1 sc pins Rs rX tubes bx t = true) (hext : ExtSub gn s0 s1 sc pins Rs rX tubes bx t) :
    SubOK gn s0 s1 sc pins Rs rX tubes bx := by
  unfold checkSubN at h
  simp only [Bool.and_eq_true, Option.any_eq_true] at h
  obtain ⟨hhead, A, hAc, hc⟩ := h
  intro A' hA'
  rw [hAc] at hA'
  cases hA'
  obtain ⟨hA, hR, -, -⟩ := arcCtx_sem hgn.g hhead hAc
  exact checkN_ok hgn hA hR gn.fuel tubes bx t (by simp [hbx]) hc
    (extList_ok gn.fuel tubes bx t (fun c hc' => hext c hc' A hAc))

theorem extSub_of {gn : GlobN} {s0 s1 sc : ℕ} {pins : List (Q × Q)} {Rs : List Q} {rX : ℕ} {tubes : List TubeD}
    {bx : List (ℕ × ℕ × ℕ)} {t : NTree} {L : List (List TubeD × List (ℕ × ℕ × ℕ))}
    (hL : extList gn.fuel tubes bx t = L) (h : ∀ c ∈ L, SubOK gn s0 s1 sc pins Rs rX c.1 c.2) :
    ExtSub gn s0 s1 sc pins Rs rX tubes bx t := by
  unfold ExtSub; rw [hL]; exact h

/-- The `ext` facts of an arc. -/
def ArcExt (gn : GlobN) : ArcN → Prop
  | .old _ => True
  | .N s0 s1 sc pins Rs rX t => ExtSub gn s0 s1 sc pins Rs rX [] (pins.map fun _ => (0, 0, 0)) t

theorem arcExt_of {gn : GlobN} {s0 s1 sc : ℕ} {pins : List (Q × Q)} {Rs : List Q} {rX : ℕ} {t : NTree}
    {L : List (List TubeD × List (ℕ × ℕ × ℕ))} (hL : extList gn.fuel [] (pins.map fun _ => (0, 0, 0)) t = L)
    (h : ∀ c ∈ L, SubOK gn s0 s1 sc pins Rs rX c.1 c.2) : ArcExt gn (.N s0 s1 sc pins Rs rX t) :=
  extSub_of hL h

theorem checkArcN_ok {gn : GlobN} (hgn : GlobNOK gn) (a : ArcN) (h : checkArcN gn a = true) (hext : ArcExt gn a) :
    C64.ArcSettled gn.g.tau.val gn.g.c.val gn.g.a.val gn.g.b.val ((a.s0 : ℝ) / 2 ^ gn.g.ES)
      ((a.s1 : ℝ) / 2 ^ gn.g.ES) := by
  cases a with
  | old a => exact checkArc_ok hgn.g a h
  | N s0 s1 sc pins Rs rX t =>
    have hsub := h
    unfold checkArcN checkSubN at hsub
    simp only [Bool.and_eq_true, Option.any_eq_true] at hsub
    obtain ⟨hhead, A, hAc, -⟩ := hsub
    obtain ⟨-, -, hloc, hroot⟩ := arcCtx_sem hgn.g hhead hAc
    have hS := checkSubN_ok hgn (by simp) h hext A hAc
    refine C64.settled_N (eps := gn.eps.val) hloc (fun μ hμ => ⟨_, hroot μ hμ, ?_⟩)
    have : ([] : List TubeD).map (tubeR gn.g) = [] := rfl
    unfold Qof at hS
    rw [this] at hS
    exact hS

/-! ### The main theorem -/

theorem main_of_checksN {gn : GlobN} {arcs : List ArcN} (hG : checkGlobN gn = true)
    (hcov : coverOK gn.g 0 (arcs.map fun a => (a.s0, a.s1)) = true)
    (hall : ∀ a ∈ arcs, checkArcN gn a = true ∧ ArcExt gn a) :
    ∀ f : ℝ → ℝ, C64.Admissible f → ∫ x, f x ≠ 0 → ∀ M : ℝ,
      (∀ᵐ t ∂(volume : Measure ℝ), C64.autoconv f t ≤ M) → (∫ x, f x) ^ 2 / (1 - gn.g.tau.val) < M := by
  obtain ⟨hgn, hw⟩ := checkGlobN_ok hG
  have hg := hgn.g
  obtain ⟨hS0, hSwind⟩ := glob_winding hg hw
  have ha : 0 < gn.g.a.val := by unfold Q.val; exact div_pos (by exact_mod_cast hg.an) (by exact_mod_cast hg.ad)
  have hb : 0 < gn.g.b.val := by unfold Q.val; exact div_pos (by exact_mod_cast hg.bn) (by exact_mod_cast hg.bd)
  obtain ⟨hhead, hcovR⟩ := coverOK_ok gn.g 0 _ hcov
  have hmap : (arcs.map fun a => (a.s0, a.s1)).map (toR gn.g.ES) =
      arcs.map fun a => ((a.s0 : ℝ) / 2 ^ gn.g.ES, (a.s1 : ℝ) / 2 ^ gn.g.ES) := by
    simp [List.map_map, toR, Function.comp_def]
  rw [hmap] at hhead hcovR
  refine C64.arcReduction gn.g.tau.val gn.g.c.val gn.g.a.val gn.g.b.val (tau_pos hg) (tau_lt_one hg) ha hb hS0
    hSwind _ (fun p hp => by simpa using hhead p hp) hcovR (fun p hp => ?_)
  obtain ⟨a, ha', rfl⟩ := List.mem_map.1 hp
  exact checkArcN_ok hgn a (hall a ha').1 (hall a ha').2

/-- The statements of `C64.Defs` (`τ = 1/4`, constant `4/3`) from the checks of a nested certificate. -/
theorem mainStatementN_of {gn : GlobN} {arcs : List ArcN} (hτ : gn.g.tau.val = 1 / 4) (hG : checkGlobN gn = true)
    (hcov : coverOK gn.g 0 (arcs.map fun a => (a.s0, a.s1)) = true)
    (hall : ∀ a ∈ arcs, checkArcN gn a = true ∧ ArcExt gn a) : C64.MainStatement :=
  mainStatement_of hτ (main_of_checksN hG hcov hall)

end C64Chk
