import C64.Check.SoundWind

/-!
# Third-order bounds of `S` and second-order bounds of atom sums on discs

* `S3 = S'''` and `|S'''(w)| ≤ (π³/3) e^{π |Im w|}`; the closed form of `S''` used by the checker;
* growth along a segment: a polynomial bound of the derivative integrates to a polynomial bound of the increment;
* for `ζ` in the disc `D(z₀, ρ)` where `|S'''| ≤ C`:
  `|S(ζ) - S(z₀)| ≤ |S'(z₀)| ρ + |S''(z₀)| ρ²/2 + C ρ³/6`;
* for `G = S - Σ m_k K_{t_k}` and `|Im| ≤ Y` on the disc:
  `|G(ζ) - G(z₀)| ≤ |G'(z₀)| ρ + (|S''(z₀)| + Σ m_k · π² e^{π Y}) ρ²/2 + C ρ³/6`.
-/

open MeasureTheory Set Complex Real Filter Topology
open scoped Interval

namespace C64

/-- `S'''(z) = ∫ (-2πit)³ K_t(z) dt`. -/
noncomputable def S3 (z : ℂ) : ℂ := ∫ t in (-1/2 : ℝ)..(1/2), (-2 * π * I * t) ^ 3 * Kt t z

lemma hasDerivAt_S2 (z : ℂ) : HasDerivAt S2 (S3 z) z := by
  have h := hasDerivAt_integral_mul_Kt (g := fun t : ℝ => (-2 * π * I * t : ℂ) ^ 2)
    ((continuous_const.mul Complex.continuous_ofReal).pow 2) (G := π ^ 2) (fun t ht => by
      rw [norm_pow]
      have h1 : ‖(-2 * π * I * t : ℂ)‖ = 2 * π * |t| := by simp [Real.pi_pos.le]
      rw [h1]
      have h2 := abs_t_le ht
      exact pow_le_pow_left₀ (by positivity) (by nlinarith [Real.pi_pos]) 2) z
  have e3 : (fun t : ℝ => (-2 * π * I * t : ℂ) ^ 2 * ((-2 * π * I * t) * Kt t z)) =
      fun t : ℝ => (-2 * π * I * t : ℂ) ^ 3 * Kt t z := by funext t; ring
  rw [e3] at h
  exact h

/-- `|S'''(w)| ≤ (π³/3) e^{π |Im w|}` (from `|t|³ ≤ t²/2` on `[-1/2, 1/2]`). -/
theorem norm_S3_le (w : ℂ) : ‖S3 w‖ ≤ π ^ 3 / 3 * Real.exp (π * |w.im|) := by
  have h : ‖S3 w‖ ≤ ∫ t in (-1/2 : ℝ)..(1/2), (4 * π ^ 3 * Real.exp (π * |w.im|)) * t ^ 2 := by
    rw [S3]
    refine intervalIntegral.norm_integral_le_of_norm_le (by norm_num) ?_ ?_
    · refine Eventually.of_forall (fun t ht => ?_)
      rw [norm_mul, norm_pow]
      have h1 : ‖(-2 * π * I * t : ℂ)‖ = 2 * π * |t| := by simp [Real.pi_pos.le]
      rw [h1]
      have h2 : ‖Kt t w‖ ≤ Real.exp (π * |w.im|) := by
        have : t ∈ Ι (-1/2 : ℝ) (1/2) := by rw [uIoc_of_le (by norm_num)]; exact ht
        exact norm_Kt_le' this w
      have ht2 : |t| ≤ 1 / 2 := by
        have h3 := ht.1; have h4 := ht.2; rw [abs_le]; constructor <;> linarith
      have hc : |t| ^ 3 = |t| * t ^ 2 := by rw [← sq_abs]; ring
      have h3 : (2 * π * |t|) ^ 3 ≤ 4 * π ^ 3 * t ^ 2 := by
        have h5 : |t| ^ 3 ≤ t ^ 2 / 2 := by
          rw [hc]; nlinarith [mul_le_mul_of_nonneg_right ht2 (sq_nonneg t)]
        have h6 : (2 * π * |t|) ^ 3 = 8 * π ^ 3 * |t| ^ 3 := by ring
        rw [h6]; nlinarith [pow_pos Real.pi_pos 3]
      calc (2 * π * |t|) ^ 3 * ‖Kt t w‖ ≤ (4 * π ^ 3 * t ^ 2) * Real.exp (π * |w.im|) :=
            mul_le_mul h3 h2 (norm_nonneg _) (by positivity)
        _ = 4 * π ^ 3 * Real.exp (π * |w.im|) * t ^ 2 := by ring
    · exact (continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_const_mul, integral_pow] at h
  norm_num at h
  linarith

/-- The checker's formula: `S''(z) = ((2 - (πz)²) sin(πz) - 2πz cos(πz)) / (πz · z²)` for `z ≠ 0`. -/
theorem S2_eq {z : ℂ} (hz : z ≠ 0) :
    S2 z = ((2 - (π * z) ^ 2) * Complex.sin (π * z) - (π * z + π * z) * Complex.cos (π * z)) /
      (π * z * (z * z)) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have heq : S1 =ᶠ[𝓝 z] fun w => (π * w * Complex.cos (π * w) - Complex.sin (π * w)) / (π * w ^ 2) := by
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw
    exact S1_eq hw
  have hsin : HasDerivAt (fun w : ℂ => Complex.sin (π * w)) (Complex.cos (π * z) * π) z := by
    have := (Complex.hasDerivAt_sin (π * z)).comp z ((hasDerivAt_id z).const_mul (π : ℂ))
    simp only [Function.comp_def, id, mul_one] at this
    exact this
  have hcos : HasDerivAt (fun w : ℂ => Complex.cos (π * w)) (-Complex.sin (π * z) * π) z := by
    have := (Complex.hasDerivAt_cos (π * z)).comp z ((hasDerivAt_id z).const_mul (π : ℂ))
    simp only [Function.comp_def, id, mul_one] at this
    exact this
  have hlin : HasDerivAt (fun w : ℂ => (π : ℂ) * w) π z := by
    simpa using (hasDerivAt_id z).const_mul (π : ℂ)
  have hN : HasDerivAt (fun w : ℂ => π * w * Complex.cos (π * w) - Complex.sin (π * w))
      (π * Complex.cos (π * z) + π * z * (-Complex.sin (π * z) * π) - Complex.cos (π * z) * π) z :=
    (hlin.mul hcos).sub hsin
  have hD : HasDerivAt (fun w : ℂ => (π : ℂ) * w ^ 2) (π * (2 * z)) z := by
    convert (hasDerivAt_pow 2 z).const_mul (π : ℂ) using 1
    simp
  have hD0 : (π : ℂ) * z ^ 2 ≠ 0 := by simp [hz, hπ]
  have hd := hN.div hD hD0
  rw [(hasDerivAt_S1 z).unique (hd.congr_of_eventuallyEq heq)]
  field_simp
  ring

/-- Growth along a segment: if `‖F'(z₀ + s h) h‖ ≤ a + b s + c s²` on `[0, 1]`, then
`‖F(z₀ + s h) - F(z₀)‖ ≤ a s + b s²/2 + c s³/3` on `[0, 1]`. -/
theorem norm_sub_le_of_poly {F F' : ℂ → ℂ} {z₀ h : ℂ} {a b c : ℝ}
    (hF : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt F (F' (z₀ + s * h)) (z₀ + s * h))
    (hb : ∀ s ∈ Icc (0 : ℝ) 1, ‖F' (z₀ + s * h) * h‖ ≤ a + b * s + c * s ^ 2) :
    ∀ s ∈ Icc (0 : ℝ) 1, ‖F (z₀ + s * h) - F z₀‖ ≤ a * s + b * s ^ 2 / 2 + c * s ^ 3 / 3 := by
  have hγ : ∀ s : ℝ, HasDerivAt (fun s : ℝ => z₀ + (s : ℂ) * h) h s := fun s => by
    have he : HasDerivAt (fun w : ℂ => z₀ + w * h) h (s : ℂ) := by
      simpa using ((hasDerivAt_id (s : ℂ)).mul_const h).const_add z₀
    exact he.comp_ofReal
  have hf : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => F (z₀ + (s : ℂ) * h) - F z₀) (F' (z₀ + s * h) * h) s :=
    fun s hs => ((hF s hs).comp s (hγ s)).sub_const (F z₀)
  have hB : ∀ s : ℝ, HasDerivAt (fun s : ℝ => a * s + b * s ^ 2 / 2 + c * s ^ 3 / 3) (a + b * s + c * s ^ 2) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => a * s) a s := by simpa using (hasDerivAt_id s).const_mul a
    have h2 : HasDerivAt (fun s : ℝ => b * s ^ 2 / 2) (b * s) s := by
      refine (((hasDerivAt_pow 2 s).const_mul b).div_const 2).congr_deriv ?_
      norm_num
      try ring
    have h3 : HasDerivAt (fun s : ℝ => c * s ^ 3 / 3) (c * s ^ 2) s := by
      refine (((hasDerivAt_pow 3 s).const_mul c).div_const 3).congr_deriv ?_
      norm_num
      try ring
    exact (h1.add h2).add h3
  intro s hs
  exact image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := 1)
    (f := fun s : ℝ => F (z₀ + (s : ℂ) * h) - F z₀) (f' := fun s => F' (z₀ + s * h) * h)
    (B := fun s : ℝ => a * s + b * s ^ 2 / 2 + c * s ^ 3 / 3) (B' := fun s => a + b * s + c * s ^ 2)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hf x ⟨hx.1, hx.2.le⟩).hasDerivWithinAt) (by simp) hB
    (fun x hx => hb x ⟨hx.1, hx.2.le⟩) hs

theorem norm_seg {z₀ h : ℂ} {ρ : ℝ} (hh : ‖h‖ ≤ ρ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖(z₀ + s * h) - z₀‖ ≤ s * ρ := by
  rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
  exact mul_le_mul_of_nonneg_left hh hs.1

/-- `S'` along a segment of the disc: `|S'(z₀ + s h) - S'(z₀)| ≤ |S''(z₀)| ρ s + C ρ² s²/2`. -/
theorem norm_S1_seg {z₀ h : ℂ} {ρ C : ℝ} (hh : ‖h‖ ≤ ρ) (hC : ∀ w, ‖w - z₀‖ ≤ ρ → ‖S3 w‖ ≤ C) :
    ∀ s ∈ Icc (0 : ℝ) 1, ‖S1 (z₀ + s * h) - S1 z₀‖ ≤ ‖S2 z₀‖ * ρ * s + C * ρ ^ 2 * s ^ 2 / 2 := by
  have hρ : 0 ≤ ρ := le_trans (norm_nonneg _) hh
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC z₀ (by simp; exact hρ))
  have hS2 : ∀ s ∈ Icc (0 : ℝ) 1, ‖S2 (z₀ + s * h)‖ ≤ ‖S2 z₀‖ + C * (s * ρ) := by
    intro s hs
    have hw := norm_seg (z₀ := z₀) hh hs
    have hw' : ‖(z₀ + s * h) - z₀‖ ≤ ρ := hw.trans (by nlinarith [hs.2])
    have h1 := (convex_closedBall z₀ ρ).norm_image_sub_le_of_norm_hasDerivWithin_le (f := S2) (f' := S3) (C := C)
      (fun w _ => (hasDerivAt_S2 w).hasDerivWithinAt)
      (fun w hw2 => hC w (by rw [Metric.mem_closedBall, dist_eq_norm] at hw2; exact hw2))
      (Metric.mem_closedBall_self hρ) (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hw')
    have h2 := norm_sub_norm_le (S2 (z₀ + s * h)) (S2 z₀)
    nlinarith [mul_le_mul_of_nonneg_left hw hC0]
  have := norm_sub_le_of_poly (F := S1) (F' := S2) (z₀ := z₀) (h := h) (a := ‖S2 z₀‖ * ρ) (b := C * ρ ^ 2)
    (c := 0) (fun s _ => hasDerivAt_S1 _) (fun s hs => by
      rw [norm_mul]
      have h1 := hS2 s hs
      have h3 : 0 ≤ ‖S2 z₀‖ + C * (s * ρ) := by have := hs.1; positivity
      calc ‖S2 (z₀ + s * h)‖ * ‖h‖ ≤ (‖S2 z₀‖ + C * (s * ρ)) * ρ := mul_le_mul h1 hh (norm_nonneg _) h3
        _ = ‖S2 z₀‖ * ρ + C * ρ ^ 2 * s + 0 * s ^ 2 := by ring)
  intro s hs
  have h1 := this s hs
  linarith

/-- Third-order bound of `S` on a disc where `|S'''| ≤ C`. -/
theorem norm_sub_S_le3 {z₀ ζ : ℂ} {ρ C : ℝ} (hζ : ‖ζ - z₀‖ ≤ ρ) (hC : ∀ w, ‖w - z₀‖ ≤ ρ → ‖S3 w‖ ≤ C) :
    ‖S ζ - S z₀‖ ≤ ‖S1 z₀‖ * ρ + ‖S2 z₀‖ * ρ ^ 2 / 2 + C * ρ ^ 3 / 6 := by
  set h := ζ - z₀ with hh_def
  have hρ : 0 ≤ ρ := le_trans (norm_nonneg _) hζ
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC z₀ (by simp; exact hρ))
  have hS1 := norm_S1_seg (z₀ := z₀) (h := h) hζ hC
  have := norm_sub_le_of_poly (F := S) (F' := S1) (z₀ := z₀) (h := h) (a := ‖S1 z₀‖ * ρ) (b := ‖S2 z₀‖ * ρ ^ 2)
    (c := C * ρ ^ 3 / 2) (fun s _ => hasDerivAt_S _) (fun s hs => by
      rw [norm_mul]
      have h1 := hS1 s hs
      have h2 := norm_sub_norm_le (S1 (z₀ + s * h)) (S1 z₀)
      have hA : ‖S1 (z₀ + s * h)‖ ≤ ‖S1 z₀‖ + (‖S2 z₀‖ * ρ * s + C * ρ ^ 2 * s ^ 2 / 2) := by linarith
      have h3 : 0 ≤ ‖S1 z₀‖ + (‖S2 z₀‖ * ρ * s + C * ρ ^ 2 * s ^ 2 / 2) := by have := hs.1; positivity
      calc ‖S1 (z₀ + s * h)‖ * ‖h‖ ≤ (‖S1 z₀‖ + (‖S2 z₀‖ * ρ * s + C * ρ ^ 2 * s ^ 2 / 2)) * ρ :=
            mul_le_mul hA hζ (norm_nonneg _) h3
        _ = ‖S1 z₀‖ * ρ + ‖S2 z₀‖ * ρ ^ 2 * s + C * ρ ^ 3 / 2 * s ^ 2 := by ring) 1 ⟨zero_le_one, le_rfl⟩
  have e : z₀ + ((1 : ℝ) : ℂ) * h = ζ := by simp [hh_def]
  rw [e] at this
  linarith

/-- `|S'''| ≤ (π³/3) e^{π Y}` on a disc where `|Im| ≤ Y`. -/
theorem norm_S3_le_disc {z₀ : ℂ} {ρ Y : ℝ} (hY : ∀ w, ‖w - z₀‖ ≤ ρ → |w.im| ≤ Y) :
    ∀ w, ‖w - z₀‖ ≤ ρ → ‖S3 w‖ ≤ π ^ 3 / 3 * Real.exp (π * Y) := fun w hw =>
  (norm_S3_le w).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hY w hw)
    Real.pi_pos.le)) (by positivity))

end C64

namespace C64Chk

open Ival Ival.Ball C64Num

/-- `Σ m_k (-2πi t_k) K_{t_k}(z)`, the derivative of `wsum`. -/
noncomputable def wsum1 (as : List (Q × Q)) (z : ℂ) : ℂ :=
  (as.map fun a => (a.2.val : ℂ) * ((-2 * π * Complex.I * a.1.val) * C64.Kt a.1.val z)).sum

/-- `Σ m_k (-2πi t_k)² K_{t_k}(z)`. -/
noncomputable def wsum2 (as : List (Q × Q)) (z : ℂ) : ℂ :=
  (as.map fun a => (a.2.val : ℂ) * ((-2 * π * Complex.I * a.1.val) ^ 2 * C64.Kt a.1.val z)).sum

theorem hasDerivAt_wsum (as : List (Q × Q)) (z : ℂ) : HasDerivAt (wsum as) (wsum1 as z) z := by
  induction as with
  | nil =>
    unfold wsum wsum1; simp only [List.map_nil, List.sum_nil]; exact hasDerivAt_const z (0 : ℂ)
  | cons a as ih =>
    exact ((C64.hasDerivAt_Kt a.1.val z).const_mul (a.2.val : ℂ)).add ih

theorem hasDerivAt_wsum1 (as : List (Q × Q)) (z : ℂ) : HasDerivAt (wsum1 as) (wsum2 as z) z := by
  induction as with
  | nil =>
    unfold wsum1 wsum2; simp only [List.map_nil, List.sum_nil]; exact hasDerivAt_const z (0 : ℂ)
  | cons a as ih =>
    have h := (((C64.hasDerivAt_Kt a.1.val z).const_mul (-2 * π * Complex.I * a.1.val)).const_mul
      (a.2.val : ℂ)).add ih
    have e : (a.2.val : ℂ) * ((-2 * π * Complex.I * a.1.val) * ((-2 * π * Complex.I * a.1.val) *
        C64.Kt a.1.val z)) = (a.2.val : ℂ) * ((-2 * π * Complex.I * a.1.val) ^ 2 * C64.Kt a.1.val z) := by ring
    rw [e] at h
    exact h

theorem norm_wsum2_le {as : List (Q × Q)} (hA : AtomsOK as) (w : ℂ) :
    ‖wsum2 as w‖ ≤ msum as * (π ^ 2 * Real.exp (π * |w.im|)) := by
  induction as with
  | nil => simp [wsum2, msum]
  | cons a as ih =>
    have ha := hA a (by simp)
    have ih' := ih (fun b hb => hA b (by simp [hb]))
    simp only [wsum2, msum, List.map_cons, List.sum_cons] at ih' ⊢
    have ht : a.1.val ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2) := by
      have := abs_le.1 ha.2.1; constructor <;> linarith [this.1, this.2]
    have hK := C64.norm_Kt_le ht w
    have h1 : ‖(-2 * π * Complex.I * a.1.val : ℂ)‖ ^ 2 ≤ π ^ 2 := by
      have : ‖(-2 * π * Complex.I * a.1.val : ℂ)‖ = 2 * π * |a.1.val| := by simp [Real.pi_pos.le]
      rw [this]
      exact pow_le_pow_left₀ (by positivity) (by nlinarith [ha.2.1, Real.pi_pos]) 2
    refine (norm_add_le _ _).trans ?_
    rw [add_mul]
    refine add_le_add ?_ ih'
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha.2.2.2]
    exact mul_le_mul_of_nonneg_left (mul_le_mul h1 hK (norm_nonneg _) (by positivity)) ha.2.2.2

/-- Second-order bound of `G = S - wsum` on a disc where `|S'''| ≤ C` and `|Im| ≤ Y`. -/
theorem norm_sub_G_le {as : List (Q × Q)} (hA : AtomsOK as) {z₀ ζ : ℂ} {ρ C Y : ℝ} (hζ : ‖ζ - z₀‖ ≤ ρ)
    (hC : ∀ w, ‖w - z₀‖ ≤ ρ → ‖C64.S3 w‖ ≤ C) (hY : ∀ w, ‖w - z₀‖ ≤ ρ → |w.im| ≤ Y) :
    ‖(C64.S ζ - wsum as ζ) - (C64.S z₀ - wsum as z₀)‖ ≤ ‖C64.S1 z₀ - wsum1 as z₀‖ * ρ +
      (‖C64.S2 z₀‖ + msum as * (π ^ 2 * Real.exp (π * Y))) * ρ ^ 2 / 2 + C * ρ ^ 3 / 6 := by
  set h := ζ - z₀ with hh_def
  have hρ : 0 ≤ ρ := le_trans (norm_nonneg _) hζ
  have hm : 0 ≤ msum as := by
    unfold msum; exact List.sum_nonneg (fun x hx => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx; exact (hA a ha).2.2.2)
  set M := msum as * (π ^ 2 * Real.exp (π * Y))
  have hM0 : 0 ≤ M := by positivity
  have hS1 := C64.norm_S1_seg (z₀ := z₀) (h := h) hζ hC
  have hW1 : ∀ s ∈ Icc (0 : ℝ) 1, ‖wsum1 as (z₀ + s * h) - wsum1 as z₀‖ ≤ M * (s * ρ) := by
    intro s hs
    have hw := C64.norm_seg (z₀ := z₀) hζ hs
    have hw' : ‖(z₀ + s * h) - z₀‖ ≤ ρ := hw.trans (by nlinarith [hs.2])
    have h1 := (convex_closedBall z₀ ρ).norm_image_sub_le_of_norm_hasDerivWithin_le (f := wsum1 as)
      (f' := wsum2 as) (C := M) (fun w _ => (hasDerivAt_wsum1 as w).hasDerivWithinAt)
      (fun w hw2 => by
        rw [Metric.mem_closedBall, dist_eq_norm] at hw2
        refine (norm_wsum2_le hA w).trans (mul_le_mul_of_nonneg_left ?_ hm)
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hY w hw2)
          Real.pi_pos.le)) (by positivity))
      (Metric.mem_closedBall_self hρ) (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hw')
    exact h1.trans (mul_le_mul_of_nonneg_left hw hM0)
  have hG : ∀ w, HasDerivAt (fun z => C64.S z - wsum as z) (C64.S1 w - wsum1 as w) w := fun w =>
    (C64.hasDerivAt_S w).sub (hasDerivAt_wsum as w)
  have := C64.norm_sub_le_of_poly (F := fun z => C64.S z - wsum as z) (F' := fun w => C64.S1 w - wsum1 as w)
    (z₀ := z₀) (h := h) (a := ‖C64.S1 z₀ - wsum1 as z₀‖ * ρ) (b := (‖C64.S2 z₀‖ + M) * ρ ^ 2)
    (c := C * ρ ^ 3 / 2) (fun s _ => hG _) (fun s hs => by
      rw [norm_mul]
      have h1 := hS1 s hs
      have h2 := hW1 s hs
      have e : C64.S1 (z₀ + s * h) - wsum1 as (z₀ + s * h) = (C64.S1 z₀ - wsum1 as z₀) +
          (C64.S1 (z₀ + s * h) - C64.S1 z₀) - (wsum1 as (z₀ + s * h) - wsum1 as z₀) := by ring
      have hA' : ‖C64.S1 (z₀ + s * h) - wsum1 as (z₀ + s * h)‖ ≤ ‖C64.S1 z₀ - wsum1 as z₀‖ +
          (‖C64.S2 z₀‖ * ρ * s + C * ρ ^ 2 * s ^ 2 / 2) + M * (s * ρ) := by
        rw [e]
        refine (norm_sub_le _ _).trans ?_
        refine add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl h1)) h2
      have h3 : 0 ≤ ‖C64.S1 z₀ - wsum1 as z₀‖ + (‖C64.S2 z₀‖ * ρ * s + C * ρ ^ 2 * s ^ 2 / 2) + M * (s * ρ) := by
        have := hs.1
        have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC z₀ (by simp; exact hρ))
        positivity
      calc ‖C64.S1 (z₀ + s * h) - wsum1 as (z₀ + s * h)‖ * ‖h‖ ≤
            (‖C64.S1 z₀ - wsum1 as z₀‖ + (‖C64.S2 z₀‖ * ρ * s + C * ρ ^ 2 * s ^ 2 / 2) + M * (s * ρ)) * ρ :=
            mul_le_mul hA' hζ (norm_nonneg _) h3
        _ = ‖C64.S1 z₀ - wsum1 as z₀‖ * ρ + (‖C64.S2 z₀‖ + M) * ρ ^ 2 * s + C * ρ ^ 3 / 2 * s ^ 2 := by ring)
    1 ⟨zero_le_one, le_rfl⟩
  have e : z₀ + ((1 : ℝ) : ℂ) * h = ζ := by simp [hh_def]
  simp only [e] at this
  linarith

end C64Chk
