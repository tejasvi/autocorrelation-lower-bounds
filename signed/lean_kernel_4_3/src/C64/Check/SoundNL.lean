import C64.Check.SoundNP

/-!
# Soundness of the nested checker, part 3: W1 records and the tile arcs of a W leaf

`ivSum` gives, for the tubes of a leaf, the multipliers with the sign conditions and the bound terms on the whole arc
of each tube; `gpOf` is the semantic content of the groups (`ivGroups`): for every point of a tube arc there is a
piece whose disc contains it.  A W1 record then satisfies the separation condition of `C64.nodeSet_tile_ne` at every
point of its tile arc (`taOKN_ok`), and `walkTA_ok` covers `[0, 1]` by W1 arcs and hard arcs.
-/

namespace C64Chk

open Ival Ival.Ball C64Num Real MeasureTheory

variable {P : ℕ}

theorem dzOf_ok {c : Cfg} {z : CBall} {zm : ℂ} (hz : memC c.P zm z) {rho : ℕ} {dy : ℕ × ℕ}
    (h : dzOf c z rho = some dy) :
    2 * π * ((rho : ℝ) / 2 ^ c.P) * Real.exp (π * ((rho : ℝ) / 2 ^ c.P)) ≤ (dy.1 : ℝ) / 2 ^ c.P ∧
    2 * π * |zm.im| * Real.exp (π * |zm.im| / 16) ≤ (dy.2 : ℝ) / 2 ^ c.P := by
  unfold dzOf at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨ex, hex, ey, hey, rfl⟩ := h
  have hP := two_pow_pos' c.P
  constructor
  · have h1 : π * ((rho : ℝ) / 2 ^ c.P) ≤ (mulU c.P (piHi c.P) rho : ℝ) / 2 ^ c.P :=
      mulU_le Real.pi_pos.le (by positivity) pi_le_piHi le_rfl
    have h2 := exp_le_expPiHi hex (le_refl ((rho : ℝ) / 2 ^ c.P))
    have h3 := mulU_le (P := c.P) (x := 2 * (π * ((rho : ℝ) / 2 ^ c.P))) (y := Real.exp (π * ((rho : ℝ) / 2 ^ c.P)))
      (X := 2 * mulU c.P (piHi c.P) rho) (Y := ex) (by positivity) (by positivity)
      (by push_cast; rw [mul_div_assoc]; linarith) h2
    calc 2 * π * ((rho : ℝ) / 2 ^ c.P) * Real.exp (π * ((rho : ℝ) / 2 ^ c.P))
        = 2 * (π * ((rho : ℝ) / 2 ^ c.P)) * Real.exp (π * ((rho : ℝ) / 2 ^ c.P)) := by ring
      _ ≤ _ := h3
  · have him := abs_le_absHi hz.2
    set Y := |zm.im|
    have h1 : π * Y ≤ (mulU c.P (piHi c.P) z.im.absHi : ℝ) / 2 ^ c.P :=
      mulU_le Real.pi_pos.le (abs_nonneg _) pi_le_piHi him
    have h2 : Real.exp (π * Y / 16) ≤ (ey : ℝ) / 2 ^ c.P := by
      have := exp_le_expPiHi hey (y := Y / 16) (cdiv_le (by norm_num) him)
      rw [show π * Y / 16 = π * (Y / 16) by ring]; exact this
    have h3 := mulU_le (P := c.P) (x := 2 * (π * Y)) (y := Real.exp (π * Y / 16))
      (X := 2 * mulU c.P (piHi c.P) z.im.absHi) (Y := ey) (by positivity) (by positivity)
      (by push_cast; rw [mul_div_assoc]; linarith) h2
    calc 2 * π * Y * Real.exp (π * Y / 16) = 2 * (π * Y) * Real.exp (π * Y / 16) := by ring
      _ ≤ _ := h3

/-! ### The bound terms of the tubes -/

theorem ivSum_hi {gn : GlobN} (hgn : GlobNOK gn) : ∀ (tbs : List TubeD) (tcs : List TubeC) (vts : List (ℤ × ℤ))
    {ivB : ℤ}, List.Forall₂ (TubeCOK gn) tbs tcs → ivSum gn true tcs vts = some ivB →
    ∃ tv : List (C64.TubeR × ℂ × ℝ), tv.map Prod.fst = tbs.map (tubeR gn.g) ∧
      tv.map (fun x => x.2.1) = vts.map cOf ∧
      (∀ x ∈ tv, ∀ q ∈ Set.Icc x.1.q0 x.1.q1,
        ((starRingEnd ℂ) x.2.1 * (C64.S (x.1.pt q) - x.1.w0 (x.1.pt q))).re ≤ 0) ∧
      (∀ x ∈ tv, ∀ q ∈ Set.Icc x.1.q0 x.1.q1, ((starRingEnd ℂ) x.2.1 * C64.S (x.1.pt q)).re ≤ x.2.2) ∧
      (tv.map fun x => x.2.2 + ‖x.2.1‖ * gn.eps.val).sum ≤ (ivB : ℝ) / 2 ^ gn.g.P
  | [], [], [], ivB, _, h => by
    simp only [ivSum, Option.some.injEq] at h; subst h
    exact ⟨[], rfl, rfl, by simp, by simp, by simp⟩
  | [], [], _ :: _, _, _, h => by simp [ivSum] at h
  | _ :: _, _ :: _, [], _, _, h => by simp [ivSum] at h
  | tb :: tbs, tc :: tcs, vt :: vts, ivB, htc, h => by
    obtain ⟨hok, hrest⟩ := List.forall₂_cons.1 htc
    unfold ivSum at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨b, hb, s, hs, rfl⟩ := h
    obtain ⟨tv, h1, h2, h3, h4, h5⟩ := ivSum_hi hgn tbs tcs vts hrest hs
    have hP := two_pow_pos' gn.g.P
    by_cases hz : vt.1 = 0 ∧ vt.2 = 0
    · rw [if_pos hz] at hb
      simp only [Option.some.injEq] at hb
      subst hb
      have hv0 : cOf vt = 0 := by apply Complex.ext <;> simp [cOf, hz.1, hz.2]
      refine ⟨(tubeR gn.g tb, cOf vt, 0) :: tv, by simp [h1], by simp [h2], ?_, ?_, ?_⟩
      · intro x hx q hq
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · simp [hv0]
        · exact h3 x hx q hq
      · intro x hx q hq
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · simp [hv0]
        · exact h4 x hx q hq
      · simp only [List.map_cons, List.sum_cons, hv0, norm_zero, zero_mul, add_zero, zero_add]
        push_cast; simpa using h5
    · rw [if_neg hz] at hb
      simp only [Option.map_eq_some_iff] at hb
      obtain ⟨b0, hb0, rfl⟩ := hb
      have hv := memC_intC (P := gn.g.P) vt
      have hall := ivAll_ok hok.E (by rw [hok.as]; exact hok.hA) (by rw [hok.as]; exact hok.mS) hv tc.ps
        (fun p hp => by rw [hok.as]; exact hok.ps p hp) hb0
      rw [hok.as] at hall
      have hcond : ∀ q ∈ Set.Icc ((tb.q0 : ℝ) / 2 ^ gn.g.EQ) ((tb.q1 : ℝ) / 2 ^ gn.g.EQ),
          IvCond true (tileR gn.g tb.ti).1 (tileR gn.g tb.ti).2.1 (tileR gn.g tb.ti).2.2 tb.as (cOf vt)
            ((b0 : ℝ) / 2 ^ gn.g.P) q := by
        intro q hq
        obtain ⟨p, hp, hqp⟩ := hok.cover q hq
        exact hall p hp q hqp
      refine ⟨(tubeR gn.g tb, cOf vt, (b0 : ℝ) / 2 ^ gn.g.P) :: tv, by simp [h1], by simp [h2], ?_, ?_, ?_⟩
      · intro x hx q hq
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · have := hcond q hq; simp only [IvCond, ↓reduceIte] at this; exact this.1
        · exact h3 x hx q hq
      · intro x hx q hq
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · have := hcond q hq; simp only [IvCond, ↓reduceIte] at this; exact this.2
        · exact h4 x hx q hq
      · simp only [List.map_cons, List.sum_cons]
        have he := mulU_le (P := gn.g.P) (norm_nonneg (cOf vt)) (eps_nonneg hgn) (norm_le_normHi hv)
          (eps_le_epsHi hgn)
        push_cast
        rw [add_div, add_div]
        linarith

theorem ivSum_lo {gn : GlobN} (hgn : GlobNOK gn) : ∀ (tbs : List TubeD) (tcs : List TubeC) (vts : List (ℤ × ℤ))
    {ivB : ℤ}, List.Forall₂ (TubeCOK gn) tbs tcs → ivSum gn false tcs vts = some ivB →
    ∃ tv : List (C64.TubeR × ℂ × ℝ), tv.map Prod.fst = tbs.map (tubeR gn.g) ∧
      tv.map (fun x => x.2.1) = vts.map cOf ∧
      (∀ x ∈ tv, ∀ q ∈ Set.Icc x.1.q0 x.1.q1,
        0 ≤ ((starRingEnd ℂ) x.2.1 * (C64.S (x.1.pt q) - x.1.w0 (x.1.pt q))).re) ∧
      (∀ x ∈ tv, ∀ q ∈ Set.Icc x.1.q0 x.1.q1, x.2.2 ≤ ((starRingEnd ℂ) x.2.1 * C64.S (x.1.pt q)).re) ∧
      (ivB : ℝ) / 2 ^ gn.g.P ≤ (tv.map fun x => x.2.2 - ‖x.2.1‖ * gn.eps.val).sum
  | [], [], [], ivB, _, h => by
    simp only [ivSum, Option.some.injEq] at h; subst h
    exact ⟨[], rfl, rfl, by simp, by simp, by simp⟩
  | [], [], _ :: _, _, _, h => by simp [ivSum] at h
  | _ :: _, _ :: _, [], _, _, h => by simp [ivSum] at h
  | tb :: tbs, tc :: tcs, vt :: vts, ivB, htc, h => by
    obtain ⟨hok, hrest⟩ := List.forall₂_cons.1 htc
    unfold ivSum at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨b, hb, s, hs, rfl⟩ := h
    obtain ⟨tv, h1, h2, h3, h4, h5⟩ := ivSum_lo hgn tbs tcs vts hrest hs
    have hP := two_pow_pos' gn.g.P
    by_cases hz : vt.1 = 0 ∧ vt.2 = 0
    · rw [if_pos hz] at hb
      simp only [Option.some.injEq] at hb
      subst hb
      have hv0 : cOf vt = 0 := by apply Complex.ext <;> simp [cOf, hz.1, hz.2]
      refine ⟨(tubeR gn.g tb, cOf vt, 0) :: tv, by simp [h1], by simp [h2], ?_, ?_, ?_⟩
      · intro x hx q hq
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · simp [hv0]
        · exact h3 x hx q hq
      · intro x hx q hq
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · simp [hv0]
        · exact h4 x hx q hq
      · simp only [List.map_cons, List.sum_cons, hv0, norm_zero, zero_mul, sub_zero, zero_add]
        push_cast; simpa using h5
    · rw [if_neg hz] at hb
      simp only [Option.map_eq_some_iff] at hb
      obtain ⟨b0, hb0, rfl⟩ := hb
      have hv := memC_intC (P := gn.g.P) vt
      have hall := ivAll_ok hok.E (by rw [hok.as]; exact hok.hA) (by rw [hok.as]; exact hok.mS) hv tc.ps
        (fun p hp => by rw [hok.as]; exact hok.ps p hp) hb0
      rw [hok.as] at hall
      have hcond : ∀ q ∈ Set.Icc ((tb.q0 : ℝ) / 2 ^ gn.g.EQ) ((tb.q1 : ℝ) / 2 ^ gn.g.EQ),
          IvCond false (tileR gn.g tb.ti).1 (tileR gn.g tb.ti).2.1 (tileR gn.g tb.ti).2.2 tb.as (cOf vt)
            ((b0 : ℝ) / 2 ^ gn.g.P) q := by
        intro q hq
        obtain ⟨p, hp, hqp⟩ := hok.cover q hq
        exact hall p hp q hqp
      refine ⟨(tubeR gn.g tb, cOf vt, (b0 : ℝ) / 2 ^ gn.g.P) :: tv, by simp [h1], by simp [h2], ?_, ?_, ?_⟩
      · intro x hx q hq
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · have := hcond q hq; simp only [IvCond, Bool.false_eq_true, ↓reduceIte] at this; exact this.1
        · exact h3 x hx q hq
      · intro x hx q hq
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · have := hcond q hq; simp only [IvCond, Bool.false_eq_true, ↓reduceIte] at this; exact this.2
        · exact h4 x hx q hq
      · simp only [List.map_cons, List.sum_cons]
        have he := mulU_le (P := gn.g.P) (norm_nonneg (cOf vt)) (eps_nonneg hgn) (norm_le_normHi hv)
          (eps_le_epsHi hgn)
        push_cast
        rw [add_div, sub_div]
        linarith

/-! ### The groups -/

/-- The semantic groups of `ivGroups`. -/
noncomputable def gpOf (g : Glob) (neg : Bool) (l : ℕ) : List TubeD → List TubeC → List (ℤ × ℤ) → List (List DTerm)
  | tb :: tbs, tc :: tcs, vt :: vts =>
    if vt.1 = 0 ∧ vt.2 = 0 then gpOf g neg l tbs tcs vts
    else ((tc.ts.getD l []).map fun x =>
        ((if neg then -(starRingEnd ℂ) (cOf vt) else (starRingEnd ℂ) (cOf vt),
          tpZ (tileR g tb.ti).1 (tileR g tb.ti).2.1 (tileR g tb.ti).2.2 x, (x.rho : ℝ) / 2 ^ g.P),
         termD (if neg then CBall.neg (CBall.conj (intC g.P vt)) else CBall.conj (intC g.P vt)) x.T (x.dz, x.yz))) ::
      gpOf g neg l tbs tcs vts
  | _, _, _ => []

theorem gpOf_snd (g : Glob) (neg : Bool) (l : ℕ) : ∀ (tbs : List TubeD) (tcs : List TubeC) (vts : List (ℤ × ℤ)),
    tbs.length = tcs.length → (gpOf g neg l tbs tcs vts).map (·.map Prod.snd) = ivGroups g.P neg l tcs vts
  | [], [], _, _ => by cases ‹List (ℤ × ℤ)› <;> rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | tb :: tbs, tc :: tcs, [], _ => rfl
  | tb :: tbs, tc :: tcs, vt :: vts, h => by
    have ih := gpOf_snd g neg l tbs tcs vts (by simpa using h)
    by_cases hz : vt.1 = 0 ∧ vt.2 = 0
    · simp only [gpOf, ivGroups, hz, and_self, ↓reduceIte, ih]
    · simp only [gpOf, ivGroups, hz, ↓reduceIte, List.map_cons, List.map_map, Function.comp_def, ih]

theorem gpOf_ok {gn : GlobN} {neg : Bool} {l : ℕ} (hl : l < gn.nL) : ∀ (tbs : List TubeD) (tcs : List TubeC)
    (vts : List (ℤ × ℤ)), List.Forall₂ (TubeCOK gn) tbs tcs →
    ∀ G ∈ gpOf gn.g neg l tbs tcs vts, ∀ p ∈ G, DOK gn.g.P 0 1 p ∧ p.2.st.length = gn.g.D
  | [], _, _, _ => by intro G hG; simp [gpOf] at hG
  | _ :: _, [], _, h => by simp at h
  | _ :: _, _ :: _, [], _ => by intro G hG; simp [gpOf] at hG
  | tb :: tbs, tc :: tcs, vt :: vts, htc => by
    obtain ⟨hok, hrest⟩ := List.forall₂_cons.1 htc
    have ih := gpOf_ok (neg := neg) hl tbs tcs vts hrest
    intro G hG p hp
    by_cases hz : vt.1 = 0 ∧ vt.2 = 0
    · simp only [gpOf, hz, and_self, ↓reduceIte] at hG
      exact ih G hG p hp
    · simp only [gpOf, hz, ↓reduceIte, List.mem_cons] at hG
      rcases hG with rfl | hG
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hp
        have hT := (hok.ts l hl).1 x hx
        have hc : memC gn.g.P (if neg then -(starRingEnd ℂ) (cOf vt) else (starRingEnd ℂ) (cOf vt))
            (if neg then CBall.neg (CBall.conj (intC gn.g.P vt)) else CBall.conj (intC gn.g.P vt)) := by
          cases neg
          · exact C64Num.CBall.memC_conj (memC_intC vt)
          · exact C64Num.CBall.memC_neg (C64Num.CBall.memC_conj (memC_intC vt))
        exact ⟨termD_ok hT.pt hc (by positivity) hT.dz (fun _ => hT.yz), hT.pt.len⟩
      · exact ih G hG p hp

theorem groups_sel {gn : GlobN} {neg : Bool} {l : ℕ} : ∀ (tbs : List TubeD) (tcs : List TubeC)
    (vts : List (ℤ × ℤ)) (tv : List (C64.TubeR × ℂ × ℝ)) (zs : List ℂ),
    (tbs = [] ∨ l < gn.nL) → List.Forall₂ (TubeCOK gn) tbs tcs → tv.map Prod.fst = tbs.map (tubeR gn.g) →
    tv.map (fun x => x.2.1) = vts.map cOf → C64.TubePts zs tv →
    ∃ sel : List (ℂ × ℂ), List.Forall₂ (fun (cz : ℂ × ℂ) (G : List DTerm) =>
        ∃ p ∈ G, cz.1 = p.1.1 ∧ ‖cz.2 - p.1.2.1‖ ≤ p.1.2.2) sel (gpOf gn.g neg l tbs tcs vts) ∧
      ∀ t, fsum sel t = (if neg then -1 else 1) * C64.TL (C64.tvz zs tv) t
  | [], _, _, tv, zs, _, htc, h1, _, hz => by
    cases htc
    have : tv = [] := by simpa using h1
    subst this
    cases hz
    exact ⟨[], by simp [gpOf], by intro t; simp [fsum, C64.TL, C64.tvz]⟩
  | tb :: tbs, tc :: tcs, vts, tv, zs, hl, htc, h1, h2, hz => by
    obtain ⟨hok, hrest⟩ := List.forall₂_cons.1 htc
    have hl' : l < gn.nL := hl.resolve_left (List.cons_ne_nil _ _)
    obtain ⟨x, tv', rfl⟩ : ∃ x tv', tv = x :: tv' := by
      cases tv with
      | nil => simp at h1
      | cons x tv' => exact ⟨x, tv', rfl⟩
    obtain ⟨vt, vts', rfl⟩ : ∃ vt vts', vts = vt :: vts' := by
      cases vts with
      | nil => simp at h2
      | cons vt vts' => exact ⟨vt, vts', rfl⟩
    simp only [List.map_cons, List.cons.injEq] at h1 h2
    obtain ⟨hx1, h1⟩ := h1
    obtain ⟨hx2, h2⟩ := h2
    cases hz with
    | cons hzx hzs =>
    rename_i z zs'
    obtain ⟨sel, hsel, hfs⟩ := groups_sel tbs tcs vts' tv' zs' (Or.inr hl') hrest h1 h2 hzs
    obtain ⟨q, hq, rfl⟩ := hzx
    by_cases hv : vt.1 = 0 ∧ vt.2 = 0
    · have hv0 : cOf vt = 0 := by apply Complex.ext <;> simp [cOf, hv.1, hv.2]
      refine ⟨sel, ?_, ?_⟩
      · unfold gpOf; rw [if_pos hv]; exact hsel
      · intro t
        rw [hfs t]
        simp [C64.TL, C64.tvz, hx2, hv0]
    · have hq' : q ∈ Set.Icc ((tb.q0 : ℝ) / 2 ^ gn.g.EQ) ((tb.q1 : ℝ) / 2 ^ gn.g.EQ) := by
        rw [hx1] at hq; exact hq
      obtain ⟨y, hy, hqy⟩ := (hok.ts l hl').2 q hq'
      have hT := (hok.ts l hl').1 y hy
      set coef : ℂ := if neg then -(starRingEnd ℂ) (cOf vt) else (starRingEnd ℂ) (cOf vt)
      refine ⟨(coef, x.1.pt q) :: sel, ?_, ?_⟩
      · unfold gpOf; rw [if_neg hv]
        refine List.Forall₂.cons ⟨_, List.mem_map_of_mem hy, rfl, ?_⟩ hsel
        have := hT.arc q hqy
        rw [hx1]; exact this
      · intro t
        rw [fsum_cons, hfs t]
        simp only [C64.TL, C64.tvz, List.zipWith_cons_cons, List.map_cons, List.sum_cons, hx2]
        cases neg <;> simp [coef] <;> ring

/-! ### Pin terms as disc terms -/

def pinDT (czs : List (ℂ × ℂ)) (ts : List TermS) : List DTerm :=
  List.zipWith (fun cz T => ((cz.1, cz.2, (0 : ℝ)), toD T)) czs ts

theorem pinDT_ok {P : ℕ} : ∀ {czs : List (ℂ × ℂ)} {ts : List TermS},
    List.Forall₂ (fun cz T => TermOK P 0 1 cz.1 cz.2 T) czs ts →
    (∀ p ∈ pinDT czs ts, DOK P 0 1 p) ∧ (pinDT czs ts).map Prod.snd = ts.map toD ∧
    List.Forall₂ (fun z (p : DTerm) => ‖z - p.1.2.1‖ ≤ p.1.2.2) (czs.map Prod.snd) (pinDT czs ts) ∧
    List.zipWith (fun z (p : DTerm) => (p.1.1, z)) (czs.map Prod.snd) (pinDT czs ts) = czs
  | [], [], _ => by simp [pinDT]
  | cz :: czs, T :: ts, h => by
    obtain ⟨hT, hrest⟩ := List.forall₂_cons.1 h
    obtain ⟨i1, i2, i3, i4⟩ := pinDT_ok hrest
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p hp
      simp only [pinDT, List.zipWith_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact toD_ok hT
      · exact i1 p hp
    · simp only [pinDT, List.zipWith_cons_cons, List.map_cons] at i2 ⊢; rw [i2]
    · simp only [pinDT, List.zipWith_cons_cons, List.map_cons] at i3 ⊢
      exact List.Forall₂.cons (by simp) i3
    · simp only [pinDT, List.zipWith_cons_cons, List.map_cons] at i4 ⊢; rw [i4]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

end C64Chk
