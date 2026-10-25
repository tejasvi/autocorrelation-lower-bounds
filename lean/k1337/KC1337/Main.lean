import KC1337.Sem
import AutocorrK39.Sound.Run
import Autocorr.Reduction

/-!
# C₁ ≥ 1337/1000: the certificate (n = 39) checked by the Lean kernel (K39 checker, no native code)

5033964 jobs, 89673710 leaves; one core-only module per job, every segment of its DFS log a `decide +kernel` check of
`AutocorrK.segCheck`, composed by `AutocorrK.StkK` in 252 G modules and `Top`.
-/

open MeasureTheory ENNReal Set

namespace Autocorr.KC1337

noncomputable def UP : ℕ := 1367254384758072717187602658204534509396859940755012624376266640837685359699933802609042646944135681180804172418347751936684231678734826684707281742849031681569729956888110898535391293934867188525186899557715302770613665816551620781789835037404421787912280239725761875030270728181319485863736534733538695027961007811962813731763846580927696112992931115868059502024501840979044082862551337476308524822779347212517986826221731746324341816362728054375406464776033583385854344577896919618831600300136278422178976489540972204244312500495823837016553083468883950603696919208185298256465841967689242875366169136454072885912911124966357044276094429773873610204026324613824499433317308472249561647929375643506708930411229335850593180563847053760790528

theorem hupP : ∀ b < P.nB, AutocorrK.get32 UP b = 2 ^ 30 := by decide +kernel

theorem root_eq : AutocorrK.propK P 0 0 UP = jb_root := by decide +kernel

theorem kpf : AutocorrK.KPFacts (Autocorr.Cert.mkSpec 39) P := AutocorrK.kpFacts kpok

theorem halfClaimK : HalfClaim 39 (((1337 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ)) := by
  have h := (okfull_root).head
  rw [← root_eq] at h
  have hup : ∀ b < (Autocorr.Cert.mkSpec 39).nB, AutocorrK.get32 UP b = 2 ^ 30 := by
    rw [← kpf.nB]; exact hupP
  have hn : (Autocorr.Cert.mkSpec 39).n = 39 := by rw [← kpf.n]; rfl
  have := AutocorrK.halfClaim_of_rootK kpf hup h
  rwa [hn] at this

theorem halfClaim : HalfClaim 39 (((1337 / 1000 : ℚ)) : ℝ) := by
  rw [show (((1337 / 1000 : ℚ)) : ℝ) = ((1337 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ) by push_cast; norm_num]
  exact halfClaimK

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

end Autocorr.KC1337
