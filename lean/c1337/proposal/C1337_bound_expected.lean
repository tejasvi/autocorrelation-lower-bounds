/-! The bound (generated as Autocorr.C1337.Main and Autocorr.C1337.Forms; merged here so that the import closure is loaded once). -/

open MeasureTheory ENNReal Set

namespace Autocorr.C1337

theorem rootOK : (Autocorr.Cert.rootBox (Autocorr.Cert.mkSpec 39)).isSome = true := by native_decide

theorem halfClaim : HalfClaim 39 (((1337 / 1000 : ℚ)) : ℝ) :=
  Autocorr.Cert.halfClaim_of_coveredX Autocorr.C1337.Jroot.covered rootOK

lemma ofReal_lam : ENNReal.ofReal (((1337 / 1000 : ℚ)) : ℝ) = (1337 / 1000 : ℝ≥0∞) := by
  rw [show (((1337 / 1000 : ℚ)) : ℝ) = (1337 : ℝ) / 1000 by norm_num, ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

/-- `C₁ ≥ 1337/1000`: for every measurable `f : ℝ → [0, ∞]`,
`1337/1000 · (∫_{-1/4}^{1/4} f)² ≤ sup_{t ∈ [-1/2, 1/2]} ∫ f(t - x) f(x) dx`. -/
theorem autocorr_lower (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (1337 / 1000 : ℝ≥0∞) * (∫⁻ x in Icc (-1/4 : ℝ) (1/4), f x) ^ 2 ≤
      ⨆ t ∈ Icc (-1/2 : ℝ) (1/2), ∫⁻ x, f (t - x) * f x := by
  rw [← ofReal_lam]
  exact autocorr_lower_of_halfClaim (by norm_num) (by norm_num) halfClaim f hf


/-- Essential-supremum form: for every measurable `f : ℝ → [0, ∞]`,
`1337/1000 · (∫_{-1/4}^{1/4} f)² ≤ ‖f ⋆ f‖_{L^∞(-1/2, 1/2)}` (`essSup`; at most the pointwise supremum). -/
theorem autocorr_lower_ess (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (1337 / 1000 : ℝ≥0∞) * (∫⁻ x in Icc (-1/4 : ℝ) (1/4), f x) ^ 2 ≤
      essSup (fun t => ∫⁻ x, f (t - x) * f x) (volume.restrict (Icc (-1/2 : ℝ) (1/2))) := by
  rw [← ofReal_lam]
  exact autocorr_lower_ess_of_halfClaim (by norm_num) (by positivity) halfClaim f hf

/-- Real-valued form with Mathlib's convolution: for `f : ℝ → ℝ` measurable, nonnegative and vanishing outside
`[-1/4, 1/4]`, `1337/1000 · (∫ f)² ≤ ‖f ⋆ f‖_{L^∞(-1/2, 1/2)}` (the norm in `ℝ≥0∞`). -/
theorem autocorr_lower_real (f : ℝ → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hsupp : ∀ x, x ∉ Icc (-1/4 : ℝ) (1/4) → f x = 0) :
    ENNReal.ofReal (1337 / 1000 * (∫ x, f x) ^ 2) ≤
      eLpNorm (convolution f f (ContinuousLinearMap.mul ℝ ℝ) volume) ⊤
        (volume.restrict (Icc (-1/2 : ℝ) (1/2))) := by
  have h := autocorr_lower_real_of_halfClaim (by norm_num) (by positivity) halfClaim f hf hf0 hsupp
  convert h using 3 <;> norm_num

end Autocorr.C1337
