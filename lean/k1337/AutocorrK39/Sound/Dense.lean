import AutocorrK39.Sound.Cut

/-!
# Soundness of the square cut with up to 126 blocks (K39)

`denseStep` (AutocorrK39/Core.lean) reads a cut `(v0, (b_1, v_1), ..., (b_k, v_k))`, `k ≤ 126`, with the dual
`y = M / 2^94 ≥ 0`, and adds `-y·coef` of every coefficient of the row
`Σ_i v_i² [m_bi m_bi] + Σ_{i<j} 2 v_i v_j [m_bi m_bj] + Σ_i 2 v0 v_i m_bi ≥ -v0²`
to the reduced costs (positive coefficients to `rn`, negative ones to `rp`) and `y·(-v0²)` to the row part (`an`).
At the true point every product column is the product of the block masses (`xval_canon`) and every `m` column the
mass (`xval_m`), so the left side plus `v0²` is `(v0 + Σ_i v_i m_bi)² ≥ 0` and the validity quantity of the step is
`-y (v0 + Σ_i v_i m_bi)² ≤ 0` (`denseStep_spec`).  The step adds at most `k (k + 3) / 2 ≤ 8127` entries of size at
most `2^107`.
-/

namespace AutocorrK

open Autocorr.Cert
open scoped BigOperators

variable {sp : Spec} {P : KP}

/-! ## Terms -/

/-- Block, sign bit and magnitude of the term at the low end of `td`, and the following terms. -/
def dtb (td : ℕ) : ℕ := Nat.mod td 128
def dts (td : ℕ) : ℕ := Nat.mod (Nat.shiftRight td 7) 2
def dta (td : ℕ) : ℕ := Nat.mod (Nat.shiftRight td 8) 2097152
def dtn (td : ℕ) : ℕ := Nat.shiftRight td 29

lemma dts_lt (td : ℕ) : dts td < 2 := by unfold dts; rw [raw_mod]; exact Nat.mod_lt _ (by norm_num)
lemma dta_lt (td : ℕ) : dta td < 2 ^ 21 := by unfold dta; rw [raw_mod]; exact Nat.mod_lt _ (by norm_num)

/-- Every block among the next `cnt` terms of `td` is `< nB`. -/
def dAll (nB : ℕ) : ℕ → ℕ → Prop
  | 0, _ => True
  | cnt + 1, td => dtb td < nB ∧ dAll nB cnt (dtn td)

lemma dValid_all : ∀ cnt td, dValid P cnt td = true → dAll P.nB cnt td := by
  intro cnt
  induction cnt with
  | zero => intro _ _; trivial
  | succ cnt ih =>
    intro td h
    change sel (Nat.blt (dtb td) P.nB) (dValid P cnt (dtn td)) false = true at h
    by_cases hb : dtb td < P.nB
    · rw [blt_true' hb, sel_true] at h
      exact ⟨hb, ih _ h⟩
    · rw [blt_false' hb, sel_false] at h
      exact absurd h (by simp)

/-! ## The mixed terms of one term (`dMix`) -/

/-- The entries `dMix` adds to `pos` and to `neg`. -/
def mixP (P : KP) (b s ma : ℕ) : ℕ → ℕ → List (ℕ × ℕ)
  | 0, _ => []
  | cnt + 1, td => (if s = dts td then [] else [(canonT P b (dtb td), ma * dta td)]) ++ mixP P b s ma cnt (dtn td)

def mixN (P : KP) (b s ma : ℕ) : ℕ → ℕ → List (ℕ × ℕ)
  | 0, _ => []
  | cnt + 1, td => (if s = dts td then [(canonT P b (dtb td), ma * dta td)] else []) ++ mixN P b s ma cnt (dtn td)

lemma dMix_eq (b s ma : ℕ) : ∀ cnt td pos neg,
    dMix P b s ma cnt td pos neg = (pos + packL (mixP P b s ma cnt td), neg + packL (mixN P b s ma cnt td)) := by
  intro cnt
  induction cnt with
  | zero => intro td pos neg; simp [dMix, mixP, mixN]
  | succ cnt ih =>
    intro td pos neg
    change sel (Nat.beq s (dts td))
        (dMix P b s ma cnt (dtn td) pos (Nat.add neg (atc (Nat.mul ma (dta td)) (canonT P b (dtb td)))))
        (dMix P b s ma cnt (dtn td) (Nat.add pos (atc (Nat.mul ma (dta td)) (canonT P b (dtb td)))) neg) = _
    by_cases hs : s = dts td
    · rw [beq_true' hs, sel_true, ih, atc_eq, raw_add, raw_mul]
      simp only [mixP, mixN, if_pos hs, List.nil_append, List.singleton_append, packL_cons, packL_nil,
        Prod.mk.injEq]
      constructor <;> first | trivial | ring
    · rw [beq_false' hs, sel_false, ih, atc_eq, raw_add, raw_mul]
      simp only [mixP, mixN, if_neg hs, List.nil_append, List.singleton_append, packL_cons, packL_nil,
        Prod.mk.injEq]
      constructor <;> first | trivial | ring

lemma mix_length (b s ma : ℕ) : ∀ cnt td,
    (mixP P b s ma cnt td).length + (mixN P b s ma cnt td).length = cnt := by
  intro cnt
  induction cnt with
  | zero => intro td; rfl
  | succ cnt ih =>
    intro td
    have := ih (dtn td)
    by_cases hs : s = dts td
    · simp only [mixP, mixN, if_pos hs, List.length_append, List.length_nil, List.length_singleton]; omega
    · simp only [mixP, mixN, if_neg hs, List.length_append, List.length_nil, List.length_singleton]; omega

lemma mix_bound (hkp : KPFacts sp P) {b s ma : ℕ} (hb : b < sp.nB) : ∀ cnt td, dAll P.nB cnt td →
    ∀ e ∈ mixP P b s ma cnt td ++ mixN P b s ma cnt td, e.1 < sp.oT ∧ e.2 ≤ ma * 2 ^ 21 := by
  intro cnt
  induction cnt with
  | zero => intro td _ e he; simp [mixP, mixN] at he
  | succ cnt ih =>
    intro td hall e he
    obtain ⟨hd, hrest⟩ := hall
    have hd' : dtb td < sp.nB := hkp.nB ▸ hd
    have hhead : (canonT P b (dtb td), ma * dta td).1 < sp.oT ∧ (canonT P b (dtb td), ma * dta td).2 ≤ ma * 2 ^ 21 :=
      ⟨by rw [canonT_eq hkp hb hd']; exact canon_lt hkp.wf hb hd',
        Nat.mul_le_mul_left _ (dta_lt td).le⟩
    have htail := ih (dtn td) hrest
    simp only [mixP, mixN, List.mem_append] at he
    rcases he with (he | he) | (he | he)
    · split_ifs at he <;> simp at he; subst he; exact hhead
    · exact htail e (List.mem_append_left _ he)
    · split_ifs at he <;> simp at he; subst he; exact hhead
    · exact htail e (List.mem_append_right _ he)

/-- `Σ` over the next `cnt` terms of `v · m_b` at the point `p`. -/
noncomputable def dxm (sp : Spec) (p : ℕ → ℝ) (td : ℕ) : ℝ := sgn (dts td) * (dta td : ℝ) * mass sp p (dtb td)

noncomputable def dxS (sp : Spec) (p : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | cnt + 1, td => dxm sp p td + dxS sp p cnt (dtn td)

lemma sgn_ne {s s' : ℕ} (hs : s < 2) (hs' : s' < 2) (h : s ≠ s') : sgn s * sgn s' = -1 := by
  interval_cases s <;> interval_cases s' <;> simp_all [sgn]

lemma mix_dot (hkp : KPFacts sp P) {b s ma : ℕ} (hb : b < sp.nB) (hs : s < 2) (p : ℕ → ℝ) (t : ℝ) :
    ∀ cnt td, dAll P.nB cnt td →
      dotL (mixP P b s ma cnt td) (xval sp p t) - dotL (mixN P b s ma cnt td) (xval sp p t) =
        -((ma : ℝ) * sgn s * mass sp p b * dxS sp p cnt td) := by
  intro cnt
  induction cnt with
  | zero => intro td _; simp [mixP, mixN, dxS]
  | succ cnt ih =>
    intro td hall
    obtain ⟨hd, hrest⟩ := hall
    have hd' : dtb td < sp.nB := hkp.nB ▸ hd
    have hx : xval sp p t (canonT P b (dtb td)) = mass sp p b * mass sp p (dtb td) := by
      rw [canonT_eq hkp hb hd']; exact xval_canon hkp.wf hb hd'
    have htail := ih (dtn td) hrest
    by_cases h : s = dts td
    · have h1 : sgn s * sgn (dts td) = 1 := by rw [← h]; exact sgn_sq
      simp only [mixP, mixN, if_pos h, List.nil_append, List.singleton_append, dotL_cons, hx, dxS, dxm]
      push_cast
      linear_combination htail + ((ma : ℝ) * (dta td : ℝ) * mass sp p b * mass sp p (dtb td)) * h1
    · have h1 : sgn s * sgn (dts td) = -1 := sgn_ne hs (dts_lt td) h
      simp only [mixP, mixN, if_neg h, List.nil_append, List.singleton_append, dotL_cons, hx, dxS, dxm]
      push_cast
      linear_combination htail + ((ma : ℝ) * (dta td : ℝ) * mass sp p b * mass sp p (dtb td)) * h1

/-! ## All terms (`dOuter`) -/

/-- The entries `dOuter` adds to `pos` and to `neg`. -/
def outP (P : KP) (s0 ma0 M : ℕ) : ℕ → ℕ → List (ℕ × ℕ)
  | 0, _ => []
  | n + 1, td =>
    mixP P (dtb td) (dts td) (2 * (M * dta td)) n (dtn td) ++
      ((if s0 = dts td then [] else [(dtb td, ma0 * dta td)]) ++ outP P s0 ma0 M n (dtn td))

def outN (P : KP) (s0 ma0 M : ℕ) : ℕ → ℕ → List (ℕ × ℕ)
  | 0, _ => []
  | n + 1, td =>
    (canonT P (dtb td) (dtb td), M * (dta td * dta td)) ::
      (mixN P (dtb td) (dts td) (2 * (M * dta td)) n (dtn td) ++
        ((if s0 = dts td then [(dtb td, ma0 * dta td)] else []) ++ outN P s0 ma0 M n (dtn td)))

lemma dOuter_eq (s0 ma0 M : ℕ) : ∀ cnt td pos neg,
    dOuter P s0 ma0 M cnt td pos neg =
      (pos + packL (outP P s0 ma0 M cnt td), neg + packL (outN P s0 ma0 M cnt td)) := by
  intro cnt
  induction cnt with
  | zero => intro td pos neg; simp [dOuter, outP, outN]
  | succ n ih =>
    intro td pos neg
    change sel (Nat.beq s0 (dts td))
        (dOuter P s0 ma0 M n (dtn td)
          (dMix P (dtb td) (dts td) (Nat.mul 2 (Nat.mul M (dta td))) n (dtn td) pos
            (Nat.add neg (atc (Nat.mul M (Nat.mul (dta td) (dta td))) (canonT P (dtb td) (dtb td))))).1
          (Nat.add (dMix P (dtb td) (dts td) (Nat.mul 2 (Nat.mul M (dta td))) n (dtn td) pos
            (Nat.add neg (atc (Nat.mul M (Nat.mul (dta td) (dta td))) (canonT P (dtb td) (dtb td))))).2
            (atc (Nat.mul ma0 (dta td)) (dtb td))))
        (dOuter P s0 ma0 M n (dtn td)
          (Nat.add (dMix P (dtb td) (dts td) (Nat.mul 2 (Nat.mul M (dta td))) n (dtn td) pos
            (Nat.add neg (atc (Nat.mul M (Nat.mul (dta td) (dta td))) (canonT P (dtb td) (dtb td))))).1
            (atc (Nat.mul ma0 (dta td)) (dtb td)))
          (dMix P (dtb td) (dts td) (Nat.mul 2 (Nat.mul M (dta td))) n (dtn td) pos
            (Nat.add neg (atc (Nat.mul M (Nat.mul (dta td) (dta td))) (canonT P (dtb td) (dtb td))))).2) = _
    simp only [dMix_eq, raw_add, raw_mul]
    by_cases hs : s0 = dts td
    · rw [beq_true' hs, sel_true, ih, atc_eq, atc_eq]
      simp only [outP, outN, if_pos hs, List.nil_append, List.singleton_append, List.cons_append, packL_cons,
        packL_nil, packL_append, Prod.mk.injEq]
      constructor <;> ring
    · rw [beq_false' hs, sel_false, ih, atc_eq, atc_eq]
      simp only [outP, outN, if_neg hs, List.nil_append, List.singleton_append, List.cons_append, packL_cons,
        packL_nil, packL_append, Prod.mk.injEq]
      constructor <;> ring

lemma out_length (s0 ma0 M : ℕ) : ∀ cnt td,
    2 * ((outP P s0 ma0 M cnt td).length + (outN P s0 ma0 M cnt td).length) = cnt * (cnt + 3) := by
  intro cnt
  induction cnt with
  | zero => intro td; rfl
  | succ n ih =>
    intro td
    have h1 := ih (dtn td)
    have h2 := mix_length (P := P) (dtb td) (dts td) (2 * (M * dta td)) n (dtn td)
    by_cases hs : s0 = dts td
    · simp only [outP, outN, if_pos hs, List.length_append, List.length_cons, List.length_nil,
        List.length_singleton]
      nlinarith
    · simp only [outP, outN, if_neg hs, List.length_append, List.length_cons, List.length_nil,
        List.length_singleton]
      nlinarith

lemma out_bound (hkp : KPFacts sp P) {s0 ma0 M B : ℕ} (hB1 : M * 2 ^ 42 ≤ B)
    (hB2 : 2 * (M * 2 ^ 21) * 2 ^ 21 ≤ B) (hB3 : ma0 * 2 ^ 21 ≤ B) : ∀ cnt td, dAll P.nB cnt td →
    ∀ e ∈ outP P s0 ma0 M cnt td ++ outN P s0 ma0 M cnt td, e.1 < sp.oT ∧ e.2 ≤ B := by
  intro cnt
  induction cnt with
  | zero => intro td _ e he; simp [outP, outN] at he
  | succ n ih =>
    intro td hall e he
    obtain ⟨hd, hrest⟩ := hall
    have hd' : dtb td < sp.nB := hkp.nB ▸ hd
    have ha := dta_lt td
    have hmix := mix_bound (s := dts td) (ma := 2 * (M * dta td)) hkp hd' n (dtn td) hrest
    have hmixB : 2 * (M * dta td) * 2 ^ 21 ≤ B :=
      le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ha.le))) hB2
    have htail := ih (dtn td) hrest
    have hm : (dtb td, ma0 * dta td).1 < sp.oT ∧ (dtb td, ma0 * dta td).2 ≤ B :=
      ⟨lt_of_lt_of_le hd' nB_le_oT, le_trans (Nat.mul_le_mul_left _ ha.le) hB3⟩
    simp only [outP, outN, List.mem_append, List.mem_cons] at he
    rcases he with (he | he | he) | (he | he | he | he)
    · exact ⟨(hmix e (List.mem_append_left _ he)).1, le_trans (hmix e (List.mem_append_left _ he)).2 hmixB⟩
    · split_ifs at he <;> simp at he; subst he; exact hm
    · exact htail e (List.mem_append_left _ he)
    · subst he
      refine ⟨by rw [canonT_eq hkp hd' hd']; exact canon_lt hkp.wf hd' hd', le_trans ?_ hB1⟩
      exact Nat.mul_le_mul_left _ (by
        calc dta td * dta td ≤ 2 ^ 21 * 2 ^ 21 := Nat.mul_le_mul ha.le ha.le
          _ = 2 ^ 42 := by norm_num)
    · exact ⟨(hmix e (List.mem_append_right _ he)).1, le_trans (hmix e (List.mem_append_right _ he)).2 hmixB⟩
    · split_ifs at he <;> simp at he; subst he; exact hm
    · exact htail e (List.mem_append_right _ he)

lemma out_dot (hkp : KPFacts sp P) {s0 a0 M : ℕ} (hs0 : s0 < 2) (p : ℕ → ℝ) (t : ℝ) :
    ∀ cnt td, dAll P.nB cnt td →
      dotL (outP P s0 (2 * (M * a0)) M cnt td) (xval sp p t) -
          dotL (outN P s0 (2 * (M * a0)) M cnt td) (xval sp p t) =
        -((M : ℝ) * (dxS sp p cnt td ^ 2 + 2 * (sgn s0 * a0) * dxS sp p cnt td)) := by
  intro cnt
  induction cnt with
  | zero => intro td _; simp [outP, outN, dxS]
  | succ n ih =>
    intro td hall
    obtain ⟨hd, hrest⟩ := hall
    have hd' : dtb td < sp.nB := hkp.nB ▸ hd
    have hmix := mix_dot (ma := 2 * (M * dta td)) hkp hd' (dts_lt td) p t n (dtn td) hrest
    have htail := ih (dtn td) hrest
    have hxd : xval sp p t (canonT P (dtb td) (dtb td)) = mass sp p (dtb td) * mass sp p (dtb td) := by
      rw [canonT_eq hkp hd' hd']; exact xval_canon hkp.wf hd' hd'
    have hxm : xval sp p t (dtb td) = mass sp p (dtb td) := xval_m hd'
    have hss : sgn (dts td) * sgn (dts td) = 1 := sgn_sq
    by_cases hs : s0 = dts td
    · have h1 : sgn s0 * sgn (dts td) = 1 := by rw [hs]; exact sgn_sq
      simp only [outP, outN, if_pos hs, List.nil_append, List.singleton_append, dotL_cons, dotL_append,
        hxd, hxm, dxS, dxm] at hmix htail ⊢
      push_cast at hmix htail ⊢
      linear_combination hmix + htail +
        (2 * (M : ℝ) * a0 * (dta td : ℝ) * mass sp p (dtb td)) * h1 +
        ((M : ℝ) * (dta td : ℝ) ^ 2 * mass sp p (dtb td) ^ 2) * hss
    · have h1 : sgn s0 * sgn (dts td) = -1 := sgn_ne hs0 (dts_lt td) hs
      simp only [outP, outN, if_neg hs, List.nil_append, List.singleton_append, dotL_cons, dotL_append,
        hxd, hxm, dxS, dxm] at hmix htail ⊢
      push_cast at hmix htail ⊢
      linear_combination hmix + htail +
        (2 * (M : ℝ) * a0 * (dta td : ℝ) * mass sp p (dtb td)) * h1 +
        ((M : ℝ) * (dta td : ℝ) ^ 2 * mass sp p (dtb td) ^ 2) * hss

/-! ## The step -/

/-- What `denseStep` does, when it accepts. -/
theorem denseStep_spec (hkp : KPFacts sp P) (data : ℕ) (k : K) (rp rn tp tn ap an : ℕ)
    (h : denseStep P data k rp rn tp tn ap an = true) :
    ∃ (data' : ℕ) (Lp Ln : List (ℕ × ℕ)) (dan : ℕ),
      k data' (rp + packL Lp) (rn + packL Ln) (tp + 0) (tn + 0) (ap + 0) (an + dan) = true ∧
      (∀ e ∈ Lp ++ Ln, e.1 < sp.oT ∧ e.2 ≤ 2 ^ 108) ∧ Lp.length + Ln.length ≤ 8192 ∧
      (∀ p t, vq sp p t Lp Ln 0 0 0 dan ≤ 0) := by
  unfold denseStep at h
  simp only [] at h
  generalize hk : Nat.mod (Nat.shiftRight data 16) 128 = kk at h
  generalize hs0 : Nat.mod (Nat.shiftRight data 23) 2 = s0 at h
  generalize ha0 : Nat.mod (Nat.shiftRight data 24) 2097152 = a0 at h
  generalize hM : Nat.mod (Nat.shiftRight data 45) 18446744073709551616 = M at h
  generalize htd : Nat.land (Nat.shiftRight data 109) (Nat.sub (Nat.pow 2 (Nat.mul 29 kk)) 1) = td at h
  have bs0 : s0 < 2 := by rw [← hs0, raw_mod]; exact Nat.mod_lt _ (by norm_num)
  have ba0 : a0 < 2 ^ 21 := by rw [← ha0, raw_mod]; exact Nat.mod_lt _ (by norm_num)
  have bM : M < 2 ^ 64 := by rw [← hM, raw_mod]; exact Nat.mod_lt _ (by norm_num)
  by_cases hkk : kk ≤ 126
  swap
  · rw [ble_false hkk, sel_false] at h
    exact absurd h (by simp)
  rw [ble_true hkk, sel_true] at h
  cases hv : dValid P kk td
  · rw [hv, sel_false] at h
    exact absurd h (by simp)
  rw [hv, sel_true] at h
  have hall := dValid_all kk td hv
  generalize hD : Nat.shiftRight data (Nat.mul 88 (Nat.div (Nat.add (Nat.mul 29 kk) 196) 88)) = data' at h
  rw [dOuter_eq] at h
  simp only [zero_add, raw_add, raw_mul, raw_shiftLeft, Nat.shiftLeft_eq] at h
  have bM' : M ≤ 2 ^ 64 := bM.le
  have ba0' : a0 ≤ 2 ^ 21 := ba0.le
  refine ⟨data', outP P s0 (2 * (M * a0)) M kk td, outN P s0 (2 * (M * a0)) M kk td, M * (a0 * a0) * 2 ^ 30,
    by simpa only [add_zero] using h, ?_, ?_, ?_⟩
  · -- index and size bounds
    refine out_bound hkp ?_ ?_ ?_ kk td hall
    · calc M * 2 ^ 42 ≤ 2 ^ 64 * 2 ^ 42 := Nat.mul_le_mul_right _ bM'
        _ ≤ 2 ^ 108 := by norm_num
    · calc 2 * (M * 2 ^ 21) * 2 ^ 21 ≤ 2 * (2 ^ 64 * 2 ^ 21) * 2 ^ 21 := by gcongr
        _ ≤ 2 ^ 108 := by norm_num
    · calc 2 * (M * a0) * 2 ^ 21 ≤ 2 * (2 ^ 64 * 2 ^ 21) * 2 ^ 21 := by gcongr
        _ ≤ 2 ^ 108 := by norm_num
  · have hl := out_length (P := P) s0 (2 * (M * a0)) M kk td
    have hq : kk * (kk + 3) ≤ 126 * (126 + 3) := Nat.mul_le_mul hkk (by omega)
    generalize kk * (kk + 3) = q at hl hq
    omega
  · intro p t
    have hd := out_dot (M := M) (a0 := a0) hkp bs0 p t kk td hall
    unfold vq
    rw [hd]
    set S := dxS sp p kk td with hS
    have hsq := sq_nonneg (sgn s0 * (a0 : ℝ) + S)
    have hss : sgn s0 * sgn s0 = 1 := sgn_sq
    have hM0 : (0 : ℝ) ≤ M := by positivity
    have key : (a0 : ℝ) * a0 + (S ^ 2 + 2 * (sgn s0 * a0) * S) = (sgn s0 * (a0 : ℝ) + S) ^ 2 := by
      linear_combination (-(a0 : ℝ) * a0) * hss
    have hk2 : 0 ≤ (M : ℝ) * ((a0 : ℝ) * a0 + (S ^ 2 + 2 * (sgn s0 * a0) * S)) := by
      rw [key]; exact mul_nonneg hM0 hsq
    have h94 : (0 : ℝ) < 2 ^ 94 := by positivity
    have hfin : -((M : ℝ) * (a0 * a0)) / 2 ^ 94 + -((M : ℝ) * (S ^ 2 + 2 * (sgn s0 * a0) * S)) / 2 ^ 94 ≤ 0 := by
      rw [← add_div, div_le_iff₀ h94, zero_mul]
      have hre : -((M : ℝ) * (a0 * a0)) + -((M : ℝ) * (S ^ 2 + 2 * (sgn s0 * a0) * S)) =
          -((M : ℝ) * ((a0 : ℝ) * a0 + (S ^ 2 + 2 * (sgn s0 * a0) * S))) := by ring
      rw [hre]; linarith [hk2]
    have e1 : -(((M * (a0 * a0) * 2 ^ 30 : ℕ) : ℝ)) / 2 ^ 124 = -((M : ℝ) * (a0 * a0)) / 2 ^ 94 := by
      push_cast
      rw [show (2 : ℝ) ^ 124 = 2 ^ 30 * 2 ^ 94 by norm_num, div_eq_div_iff (by positivity) (by positivity)]
      ring
    simp only [Nat.cast_zero, zero_sub, sub_self, zero_div, zero_mul, add_zero]
    rw [e1]
    exact hfin

end AutocorrK
