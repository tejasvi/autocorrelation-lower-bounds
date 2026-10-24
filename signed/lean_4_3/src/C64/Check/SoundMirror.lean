import C64.Check.SoundNMain

/-!
# Reflection: the lower half of `T₁` is the mirror of the upper half

For `μ` in `𝒜_τ` put `μ^R = map (t ↦ -t) μ`.  Then `μ^R ∈ 𝒜_τ`, `μ̂^R(z) = conj(μ̂(conj z))`, `S(conj z) = conj(S z)`,
hence `G_{μ^R}(z) = conj(G_μ(conj z))`.  `T₁` has a real centre, so `z(1 - s) = conj(z(s))`.  A crossing of `μ` at
`z(1 - s)` is a crossing of `μ^R` at `z(s)`, and an odd-winding ellipse `(c, a, b)` of `μ^R` gives the odd-winding
ellipse `(conj c, a, b)` of `μ` (traversed with `q ↦ 1 - q`, same winding number).  So an arc `[s₀, s₁]` settled at
level `τ` has its mirror `[1 - s₁, 1 - s₀]` settled, and the checks of the upper half (arcs covering `[0, 1/2]`)
give the main theorem (`main_of_checksN_mirror`).
-/

open MeasureTheory Set Complex Real ComplexConjugate

namespace C64

/-- `μ^R = map (t ↦ -t) μ`. -/
noncomputable def reflect (μ : Measure ℝ) : Measure ℝ := Measure.map (fun t => -t) μ

theorem classA_reflect {τ : ℝ} {μ : Measure ℝ} (h : ClassA τ μ) : ClassA τ (reflect μ) := by
  obtain ⟨hfin, hsupp, hmass⟩ := h
  have hm : Measurable (fun t : ℝ => -t) := measurable_neg
  refine ⟨?_, ?_, ?_⟩
  · unfold reflect; haveI := hfin; infer_instance
  · unfold reflect
    rw [Measure.map_apply hm measurableSet_Icc.compl]
    have : (fun t : ℝ => -t) ⁻¹' (Icc (-1/2 : ℝ) (1/2))ᶜ = (Icc (-1/2 : ℝ) (1/2))ᶜ := by
      ext t
      simp only [mem_preimage, mem_compl_iff, mem_Icc]
      constructor
      · intro h h'; exact h ⟨by linarith [h'.2], by linarith [h'.1]⟩
      · intro h h'; exact h ⟨by linarith [h'.2], by linarith [h'.1]⟩
    rw [this]; exact hsupp
  · unfold reflect
    rw [Measure.map_apply hm MeasurableSet.univ, preimage_univ]; exact hmass

theorem Kt_neg_conj (t : ℝ) (z : ℂ) : Kt (-t) z = conj (Kt t (conj z)) := by
  unfold Kt
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I, Complex.conj_conj, map_ofNat]
  push_cast; ring

theorem hat_reflect {τ : ℝ} {μ : Measure ℝ} (h : ClassA τ μ) (z : ℂ) :
    hat (reflect μ) z = conj (hat μ (conj z)) := by
  have := h.1
  unfold hat reflect
  rw [integral_map measurable_neg.aemeasurable (continuous_Kt_t z).aestronglyMeasurable]
  simp_rw [Kt_neg_conj]
  exact integral_conj

theorem S_conj (z : ℂ) : S (conj z) = conj (S z) := by
  unfold S
  by_cases hz : z = 0
  · subst hz; simp
  · have hz' : conj z ≠ 0 := by simpa using hz
    rw [if_neg hz', if_neg hz, map_div₀, ← Complex.sin_conj]
    simp only [map_mul, Complex.conj_ofReal]

theorem G_reflect {τ : ℝ} {μ : Measure ℝ} (h : ClassA τ μ) (z : ℂ) :
    G (reflect μ) z = conj (G μ (conj z)) := by
  unfold G
  rw [hat_reflect h, map_sub, S_conj, Complex.conj_conj]

theorem ellipse_conj (c : ℂ) (a b q : ℝ) : conj (ellipse c a b q) = ellipse (conj c) a b (1 - q) := by
  unfold ellipse
  have h1 : Real.cos (2 * π * (1 - q)) = Real.cos (2 * π * q) := by
    rw [show 2 * π * (1 - q) = 2 * π - 2 * π * q by ring, Real.cos_two_pi_sub]
  have h2 : Real.sin (2 * π * (1 - q)) = -Real.sin (2 * π * q) := by
    rw [show 2 * π * (1 - q) = 2 * π - 2 * π * q by ring, Real.sin_two_pi_sub]
  rw [h1, h2]
  apply Complex.ext <;> simp only [Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] <;> ring

/-- Only the parity of the winding number matters; reflection keeps the number itself. -/
theorem oddLoop_of_reflect {τ : ℝ} {μ : Measure ℝ} (hA : ClassA τ μ) (h : OddLoop (reflect μ)) : OddLoop μ := by
  obtain ⟨c, a, b, ha, hb, hne, n, hn, L, hLc, hL, hL1⟩ := h
  have key : ∀ q, G μ (ellipse (conj c) a b q) = conj (G (reflect μ) (ellipse c a b (1 - q))) := by
    intro q
    have e : ellipse (conj c) a b q = conj (ellipse c a b (1 - q)) := by rw [ellipse_conj]; congr 1; ring
    rw [e, G_reflect hA, Complex.conj_conj]
  have hmap : MapsTo (fun q : ℝ => 1 - q) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := fun q hq =>
    ⟨by linarith [hq.2], by linarith [hq.1]⟩
  refine ⟨conj c, a, b, ha, hb, fun q hq => ?_, n, hn, fun q => conj (L (1 - q)), ?_, fun q hq => ?_, ?_⟩
  · rw [key]
    exact (map_ne_zero _).2 (hne (1 - q) (hmap hq))
  · exact Complex.continuous_conj.comp_continuousOn
      (hLc.comp (continuous_const.sub continuous_id).continuousOn hmap)
  · simp only
    rw [Complex.exp_conj, hL (1 - q) (hmap hq), key]
  · simp only [sub_self, sub_zero]
    rw [← map_sub, show L 0 - L 1 = -(L 1 - L 0) by ring, hL1]
    simp only [map_neg, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast]
    ring

/-- The mirror of a settled arc of an ellipse with a real centre is settled. -/
theorem arcSettled_mirror {τ c a b s₀ s₁ : ℝ} (h : ArcSettled τ c a b s₀ s₁) :
    ArcSettled τ c a b (1 - s₁) (1 - s₀) := by
  intro μ hμ s hs lam hlam hcr
  set s' := 1 - s with hs'def
  have hs' : s' ∈ Icc s₀ s₁ := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hw : ellipse (c : ℂ) a b s' = conj (ellipse (c : ℂ) a b s) := by
    rw [ellipse_conj, Complex.conj_ofReal]
  have hcr' : S (ellipse (c : ℂ) a b s') = lam * hat (reflect μ) (ellipse (c : ℂ) a b s') := by
    rw [hw, hat_reflect hμ, Complex.conj_conj, S_conj, hcr, map_mul, Complex.conj_ofReal]
  exact oddLoop_of_reflect hμ (h (reflect μ) (classA_reflect hμ) s' hs' lam hlam hcr')

end C64

namespace C64Chk

open Ival Ival.Ball C64Num

/-! ### Covers of `[0, 1/2]` and their mirrors -/

/-- `l` is a chain of arcs from `a` to `b`: the first starts at `a`, each next one starts where the previous ends, the
last ends at `b`. -/
def Chain : ℝ → ℝ → List (ℝ × ℝ) → Prop
  | _, _, [] => False
  | a, b, [p] => p.1 = a ∧ p.2 = b
  | a, b, p :: q :: rest => p.1 = a ∧ Chain p.2 b (q :: rest)

theorem chain_append : ∀ {a b c : ℝ} {l l' : List (ℝ × ℝ)}, Chain a b l → Chain b c l' → Chain a c (l ++ l')
  | _, _, _, [], _, h, _ => h.elim
  | _, _, _, [_], [], _, h' => h'.elim
  | _, _, _, [p], q :: rest, h, h' => ⟨h.1, by rw [h.2]; exact h'⟩
  | _, _, _, p :: q :: rest, _, h, h' => ⟨h.1, chain_append h.2 h'⟩

/-- The mirror arc `(1 - s₁, 1 - s₀)`. -/
def mirA (p : ℝ × ℝ) : ℝ × ℝ := (1 - p.2, 1 - p.1)

theorem chain_mirror : ∀ {a b : ℝ} {l : List (ℝ × ℝ)}, Chain a b l → Chain (1 - b) (1 - a) ((l.map mirA).reverse)
  | _, _, [], h => h.elim
  | _, _, [p], h => by
    simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append, Chain, mirA]
    exact ⟨by rw [h.2], by rw [h.1]⟩
  | _, _, p :: q :: rest, h => by
    have ih := chain_mirror h.2
    rw [List.map_cons, List.reverse_cons]
    exact chain_append ih ⟨rfl, by simp only [mirA]; rw [h.1]⟩

theorem chain_coversUnit : ∀ {a : ℝ} {l : List (ℝ × ℝ)}, Chain a 1 l → C64.CoversUnit l
  | _, [], h => h.elim
  | _, [_], h => h.2
  | _, p :: q :: rest, h => by
    have h2 := h.2
    refine ⟨?_, chain_coversUnit h2⟩
    cases rest with
    | nil => exact h2.1.symm
    | cons r rest => exact h2.1.symm

theorem chain_head : ∀ {a b : ℝ} {l : List (ℝ × ℝ)}, Chain a b l → ∀ p ∈ l.head?, p.1 = a
  | _, _, [], h => h.elim
  | _, _, [_], h => by intro p hp; simp at hp; rw [← hp]; exact h.1
  | _, _, _ :: _ :: _, h => by intro p hp; simp at hp; rw [← hp]; exact h.1

theorem coverHalfOK_ok (g : Glob) : ∀ (x : ℕ) (L : List (ℕ × ℕ)), coverHalfOK g x L = true →
    Chain ((x : ℝ) / 2 ^ g.ES) (1 / 2) (L.map (toR g.ES))
  | _, [], h => by simp [coverHalfOK] at h
  | x, [(a, b)], h => by
    simp only [coverHalfOK, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hb⟩ := h
    refine ⟨rfl, ?_⟩
    have hb' : (2 : ℝ) * b = 2 ^ g.ES := by exact_mod_cast hb
    simp only [toR]
    rw [div_eq_iff (by positivity)]; linarith
  | x, (a, b) :: q :: rest, h => by
    simp only [coverHalfOK, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h'⟩ := h
    exact ⟨rfl, coverHalfOK_ok g b (q :: rest) h'⟩

/-! ### The main theorem from the upper half -/

theorem main_of_checksN_mirror {gn : GlobN} {arcs : List ArcN} (hG : checkGlobN gn = true)
    (hcov : coverHalfOK gn.g 0 (arcs.map fun a => (a.s0, a.s1)) = true)
    (hall : ∀ a ∈ arcs, checkArcN gn a = true ∧ ArcExt gn a) :
    ∀ f : ℝ → ℝ, C64.Admissible f → ∫ x, f x ≠ 0 → ∀ M : ℝ,
      (∀ᵐ t ∂(volume : Measure ℝ), C64.autoconv f t ≤ M) → (∫ x, f x) ^ 2 / (1 - gn.g.tau.val) < M := by
  obtain ⟨hgn, hw⟩ := checkGlobN_ok hG
  have hg := hgn.g
  obtain ⟨hS0, hSwind⟩ := glob_winding hg hw
  have ha : 0 < gn.g.a.val := by unfold Q.val; exact div_pos (by exact_mod_cast hg.an) (by exact_mod_cast hg.ad)
  have hb : 0 < gn.g.b.val := by unfold Q.val; exact div_pos (by exact_mod_cast hg.bn) (by exact_mod_cast hg.bd)
  set PR := (arcs.map fun a => (a.s0, a.s1)).map (toR gn.g.ES)
  have hch : Chain 0 (1 / 2) PR := by
    have := coverHalfOK_ok gn.g 0 _ hcov
    simp only [Nat.cast_zero, zero_div] at this
    exact this
  have hmir : Chain (1 / 2) 1 ((PR.map mirA).reverse) := by
    have := chain_mirror hch
    have e1 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    have e2 : (1 : ℝ) - 0 = 1 := by norm_num
    rw [e1, e2] at this
    exact this
  have hLR := chain_append hch hmir
  have hset : ∀ p ∈ PR, C64.ArcSettled gn.g.tau.val gn.g.c.val gn.g.a.val gn.g.b.val p.1 p.2 := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hp
    obtain ⟨a, ha', rfl⟩ := List.mem_map.1 hx
    exact checkArcN_ok hgn a (hall a ha').1 (hall a ha').2
  refine C64.arcReduction gn.g.tau.val gn.g.c.val gn.g.a.val gn.g.b.val (tau_pos hg) (tau_lt_one hg) ha hb hS0
    hSwind _ (chain_head hLR) (chain_coversUnit hLR) (fun p hp => ?_)
  rcases List.mem_append.1 hp with hp | hp
  · exact hset p hp
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hp)
    exact C64.arcSettled_mirror (hset q hq)

/-- The statements of `C64.Defs` (`τ = 1/4`, constant `4/3`) from the checks of the upper half. -/
theorem mainStatementN_mirror_of {gn : GlobN} {arcs : List ArcN} (hτ : gn.g.tau.val = 1 / 4)
    (hG : checkGlobN gn = true) (hcov : coverHalfOK gn.g 0 (arcs.map fun a => (a.s0, a.s1)) = true)
    (hall : ∀ a ∈ arcs, checkArcN gn a = true ∧ ArcExt gn a) : C64.MainStatement :=
  mainStatement_of hτ (main_of_checksN_mirror hG hcov hall)

end C64Chk
