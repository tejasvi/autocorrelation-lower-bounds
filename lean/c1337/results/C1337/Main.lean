import Autocorr.C1337.Gro.Groot
import Autocorr.Cert.SoundX

/-!
# The certificate `cert` (n = 39, lam = 1337/1000) checked in Lean

Composed from sharded modules (tools/export_shard.py): one `native_decide` per job (extended checker
`checkJobStrX`), composed through `Autocorr.Cert.CoveredX`.
-/

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

end Autocorr.C1337
