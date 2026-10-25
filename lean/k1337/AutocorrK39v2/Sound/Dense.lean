import AutocorrK39v2.Sound.Cut

/-!
# Soundness of the square cut with up to 126 blocks (K39)

`denseStep` (AutocorrK39v2/Core.lean) reads a cut `(v0, (b_1, v_1), ..., (b_k, v_k))`, `k ≤ 126`, with the dual
`y = M / 2^94 ≥ 0`, and adds `-y·coef` of every coefficient of the row
`Σ_i v_i² [m_bi m_bi] + Σ_{i<j} 2 v_i v_j [m_bi m_bj] + Σ_i 2 v0 v_i m_bi ≥ -v0²`
to the reduced costs (positive coefficients to `rn`, negative ones to `rp`) and `y·(-v0²)` to the row part (`an`).
At the true point every product column is the product of the block masses (`xval_canon`) and every `m` column the
mass (`xval_m`), so the left side plus `v0²` is `(v0 + Σ_i v_i m_bi)² ≥ 0` and the validity quantity of the step is
`-y (v0 + Σ_i v_i m_bi)² ≤ 0` (`denseStep_spec`).  The step adds at most `k (k + 3) / 2 ≤ 8127` entries of size at
most `2^107`.
-/

namespace AutocorrK2

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

/-! ## v2: the product path computes the pairwise path exactly -/

/-! ## Block-tree fact used -/

/-- The product column of two leaves (from the definition of `Spec.canon`). Distinct positions and positions `< n`
need no tree facts: the kernel checks them (`seen`, `p < n`). -/
theorem canon_leaf {b c : ℕ} (hlb : sp.isLeaf b = true) (hlc : sp.isLeaf c = true) :
    sp.canon b c = sp.oZ + min (sp.blk b).lo (sp.blk c).lo * sp.n + max (sp.blk b).lo (sp.blk c).lo := by
  simp [Spec.canon, Spec.zIdx, hlb, hlc]

/-! ## The term loop -/

/-- Entries `(n p_i, M a_i)` of the terms with sign bit `s`. -/
def termsA (sp : Spec) (M s : ℕ) : ℕ → ℕ → List (ℕ × ℕ)
  | 0, _ => []
  | cnt + 1, td =>
    (if dts td = s then [(sp.n * (sp.blk (dtb td)).lo, M * dta td)] else []) ++ termsA sp M s cnt (dtn td)

/-- Entries `(p_i, a_i)` of the terms with sign bit `s`. -/
def termsB (sp : Spec) (s : ℕ) : ℕ → ℕ → List (ℕ × ℕ)
  | 0, _ => []
  | cnt + 1, td => (if dts td = s then [((sp.blk (dtb td)).lo, dta td)] else []) ++ termsB sp s cnt (dtn td)

/-- Linear entries `(b_i, ma0 a_i)` of the terms with `(s_i = s0) = same` (those of `outN`, resp. `outP`). -/
def linL (s0 ma0 : ℕ) (same : Bool) : ℕ → ℕ → List (ℕ × ℕ)
  | 0, _ => []
  | cnt + 1, td => (if decide (s0 = dts td) = same then [(dtb td, ma0 * dta td)] else []) ++ linL s0 ma0 same cnt (dtn td)

/-- All terms are leaves, with pairwise distinct positions, none of them in `seen`. -/
def LeafDistinct (sp : Spec) : ℕ → ℕ → ℕ → Prop
  | 0, _, _ => True
  | cnt + 1, td, seen => sp.isLeaf (dtb td) = true ∧ (sp.blk (dtb td)).lo < sp.n ∧
      Nat.testBit seen (sp.blk (dtb td)).lo = false ∧ LeafDistinct sp cnt (dtn td) (seen ||| 2 ^ (sp.blk (dtb td)).lo)

theorem raw_or (a b : ℕ) : Nat.lor a b = a ||| b := rfl

theorem sel_ok {c a : Bool} : sel c a false = true ↔ c = true ∧ a = true := by
  cases c <;> simp [sel]

theorem beq_eq_decide (a b : ℕ) : Nat.beq a b = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · have : Nat.beq a b = false := by
      cases hb : Nat.beq a b
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h
    simp [this, h]

theorem kStep_ok_eq (lpos n M ma0 s0 : ℕ) (acc : KAcc) (td : ℕ) :
    (kStep lpos n M ma0 s0 acc td).ok =
      sel (sel (Nat.blt (get8 lpos (dtb td)) n)
        (Nat.beq (Nat.land acc.seen (Nat.shiftLeft 1 (get8 lpos (dtb td)))) 0) false) acc.ok false := by
  rw [show kStep lpos n M ma0 s0 acc td = kStepA n (get8 lpos (dtb td)) (dtb td) (dts td) (dta td) M ma0 s0 acc
    from rfl]
  unfold kStepA
  cases Nat.beq (dts td) 0 <;> rfl

theorem kStep_ok {lpos n M ma0 s0 : ℕ} {acc : KAcc} {td : ℕ} (h : (kStep lpos n M ma0 s0 acc td).ok = true) :
    get8 lpos (dtb td) < n ∧ acc.seen &&& 2 ^ get8 lpos (dtb td) = 0 ∧ acc.ok = true := by
  rw [kStep_ok_eq, sel_ok, sel_ok] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨Nat.blt_eq.mp h1, ?_, h3⟩
  have := Nat.eq_of_beq_eq_true h2
  simpa [Nat.shiftLeft_eq, raw_land] using this

theorem kStep_fields (lpos n M ma0 s0 : ℕ) (acc : KAcc) (td : ℕ) :
    (kStep lpos n M ma0 s0 acc td).ap =
        acc.ap + (if dts td = 0 then M * dta td * 2 ^ (136 * (n * get8 lpos (dtb td))) else 0) ∧
      (kStep lpos n M ma0 s0 acc td).an =
        acc.an + (if dts td = 0 then 0 else M * dta td * 2 ^ (136 * (n * get8 lpos (dtb td)))) ∧
      (kStep lpos n M ma0 s0 acc td).bp =
        acc.bp + (if dts td = 0 then dta td * 2 ^ (136 * get8 lpos (dtb td)) else 0) ∧
      (kStep lpos n M ma0 s0 acc td).bn =
        acc.bn + (if dts td = 0 then 0 else dta td * 2 ^ (136 * get8 lpos (dtb td))) ∧
      (kStep lpos n M ma0 s0 acc td).lp =
        acc.lp + (if s0 = dts td then 0 else ma0 * dta td * 2 ^ (136 * dtb td)) ∧
      (kStep lpos n M ma0 s0 acc td).ln =
        acc.ln + (if s0 = dts td then ma0 * dta td * 2 ^ (136 * dtb td) else 0) ∧
      (kStep lpos n M ma0 s0 acc td).seen = acc.seen ||| 2 ^ get8 lpos (dtb td) := by
  rw [show kStep lpos n M ma0 s0 acc td = kStepA n (get8 lpos (dtb td)) (dtb td) (dts td) (dta td) M ma0 s0 acc
    from rfl]
  unfold kStepA
  generalize get8 lpos (dtb td) = p
  rw [beq_eq_decide s0 (dts td), beq_eq_decide (dts td) 0]
  by_cases h0 : dts td = 0
  · by_cases h : s0 = 0 <;> simp [h0, h, sel, Nat.shiftLeft_eq, atc_eq]
  · by_cases h : s0 = dts td <;> simp [h0, h, sel, Nat.shiftLeft_eq, atc_eq]

theorem kLoop_spec {lpos maskD maskU : ℕ} (hP : ProdFacts sp lpos maskD maskU) (hn : sp.n < 255)
    (M ma0 s0 : ℕ) : ∀ cnt td (acc : KAcc), dAll sp.nB cnt td →
      (kLoop lpos sp.n M ma0 s0 cnt td acc).ok = true →
      acc.ok = true ∧ LeafDistinct sp cnt td acc.seen ∧
      (kLoop lpos sp.n M ma0 s0 cnt td acc).ap = acc.ap + packL (termsA sp M 0 cnt td) ∧
      (kLoop lpos sp.n M ma0 s0 cnt td acc).an = acc.an + packL (termsA sp M 1 cnt td) ∧
      (kLoop lpos sp.n M ma0 s0 cnt td acc).bp = acc.bp + packL (termsB sp 0 cnt td) ∧
      (kLoop lpos sp.n M ma0 s0 cnt td acc).bn = acc.bn + packL (termsB sp 1 cnt td) ∧
      (kLoop lpos sp.n M ma0 s0 cnt td acc).lp = acc.lp + packL (linL s0 ma0 false cnt td) ∧
      (kLoop lpos sp.n M ma0 s0 cnt td acc).ln = acc.ln + packL (linL s0 ma0 true cnt td) := by
  intro cnt
  induction cnt with
  | zero =>
    intro td acc _ h
    simp only [kLoop] at h ⊢
    exact ⟨h, trivial, by simp [termsA, termsB, linL]⟩
  | succ cnt ih =>
    intro td acc hall h
    obtain ⟨hb, hrest⟩ := hall
    change (kLoop lpos sp.n M ma0 s0 cnt (dtn td) (kStep lpos sp.n M ma0 s0 acc td)).ok = true at h
    obtain ⟨hok', hdist, hap, han, hbp, hbn, hlp, hln⟩ := ih (dtn td) _ hrest h
    obtain ⟨hp, hfresh, hok⟩ := kStep_ok hok'
    obtain ⟨fap, fan, fbp, fbn, flp, fln, fseen⟩ := kStep_fields lpos sp.n M ma0 s0 acc td
    have hb' : dtb td < sp.nB := hb
    have hpos := hP.lpos (dtb td) hb'
    have hleaf : sp.isLeaf (dtb td) = true := by
      by_contra hl
      rw [if_neg hl] at hpos; omega
    rw [if_pos hleaf] at hpos
    rw [hpos] at hp hfresh fap fan fbp fbn fseen
    have hs := dts_lt td
    refine ⟨hok, ⟨hleaf, hp, ?_, fseen ▸ hdist⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Nat.and_two_pow] at hfresh
      cases h' : acc.seen.testBit (sp.blk (dtb td)).lo
      · rfl
      · rw [h'] at hfresh; simp at hfresh
    · show (kLoop lpos sp.n M ma0 s0 cnt (dtn td) (kStep lpos sp.n M ma0 s0 acc td)).ap = _
      rw [hap, fap]; simp only [termsA, packL_append]
      by_cases h0 : dts td = 0 <;> simp [h0, packL_cons] <;> ring
    · show (kLoop lpos sp.n M ma0 s0 cnt (dtn td) (kStep lpos sp.n M ma0 s0 acc td)).an = _
      rw [han, fan]; simp only [termsA, packL_append]
      by_cases h0 : dts td = 0
      · simp [h0]
      · have h1 : dts td = 1 := by omega
        simp [h0, h1, packL_cons]; ring
    · show (kLoop lpos sp.n M ma0 s0 cnt (dtn td) (kStep lpos sp.n M ma0 s0 acc td)).bp = _
      rw [hbp, fbp]; simp only [termsB, packL_append]
      by_cases h0 : dts td = 0 <;> simp [h0, packL_cons] <;> ring
    · show (kLoop lpos sp.n M ma0 s0 cnt (dtn td) (kStep lpos sp.n M ma0 s0 acc td)).bn = _
      rw [hbn, fbn]; simp only [termsB, packL_append]
      by_cases h0 : dts td = 0
      · simp [h0]
      · have h1 : dts td = 1 := by omega
        simp [h0, h1, packL_cons]; ring
    · show (kLoop lpos sp.n M ma0 s0 cnt (dtn td) (kStep lpos sp.n M ma0 s0 acc td)).lp = _
      rw [hlp, flp]; simp only [linL, packL_append]
      by_cases h : s0 = dts td <;> simp [h, packL_cons] <;> ring
    · show (kLoop lpos sp.n M ma0 s0 cnt (dtn td) (kStep lpos sp.n M ma0 s0 acc td)).ln = _
      rw [hln, fln]; simp only [linL, packL_append]
      by_cases h : s0 = dts td <;> simp [h, packL_cons] <;> ring

/-! ## Product identity and digit extraction -/

theorem packL_map_pair (x : ℕ × ℕ) (B : List (ℕ × ℕ)) :
    packL (B.map (fun y => (x.1 + y.1, x.2 * y.2))) = x.2 * 2 ^ (136 * x.1) * packL B := by
  induction B with
  | nil => simp [packL]
  | cons y B ih =>
    simp only [List.map_cons, packL_cons, ih]
    rw [mul_add, pow_add]
    ring

theorem packL_mul (A B : List (ℕ × ℕ)) :
    packL A * packL B = packL (A.flatMap (fun x => B.map (fun y => (x.1 + y.1, x.2 * y.2)))) := by
  induction A with
  | nil => simp [packL]
  | cons x A ih =>
    rw [List.flatMap_cons, packL_append, packL_map_pair, ← ih, packL_cons]
    ring

/-- No carries: masking a packed vector with distinct columns and one-digit values keeps exactly the entries
whose column satisfies `q`. -/
theorem accD_eq_zero_of_not_mem {L : List (ℕ × ℕ)} {c : ℕ} (h : c ∉ L.map Prod.fst) : accD L c = 0 := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [accD_cons, if_neg (fun he => h.1 he.symm), ih h.2]

theorem accD_lt_of_nodup {L : List (ℕ × ℕ)} (hcol : (L.map Prod.fst).Nodup) (hlt : ∀ e ∈ L, e.2 < 2 ^ 136)
    (c : ℕ) : accD L c < 2 ^ 136 := by
  induction L with
  | nil => simp [accD]
  | cons e L ih =>
    simp only [List.map_cons, List.nodup_cons] at hcol
    rw [accD_cons]
    by_cases he : e.1 = c
    · rw [if_pos he, accD_eq_zero_of_not_mem (he ▸ hcol.1), add_zero]
      exact hlt e (List.mem_cons_self ..)
    · rw [if_neg he, zero_add]
      exact ih hcol.2 (fun f hf => hlt f (List.mem_cons_of_mem _ hf))

theorem accD_filter (L : List (ℕ × ℕ)) (q : ℕ → Prop) [DecidablePred q] (c : ℕ) :
    accD (L.filter (fun e => q e.1)) c = if q c then accD L c else 0 := by
  induction L with
  | nil => simp [accD]
  | cons e L ih =>
    by_cases hq : q e.1
    · rw [List.filter_cons_of_pos (by simpa using hq), accD_cons, accD_cons, ih]
      by_cases he : e.1 = c
      · subst he; simp [hq]
      · simp [he]
    · rw [List.filter_cons_of_neg (by simpa using hq), ih, accD_cons]
      by_cases he : e.1 = c
      · subst he; simp [hq]
      · simp [he]

theorem packL_land_mask (L : List (ℕ × ℕ)) (S : ℕ) (q : ℕ → Prop) [DecidablePred q]
    (hcol : (L.map Prod.fst).Nodup) (hlt : ∀ e ∈ L, e.1 < S ∧ e.2 < 2 ^ 136) :
    packL L &&& pk 136 (fun c => if q c then 2 ^ 136 - 1 else 0) S = packL (L.filter (fun e => q e.1)) := by
  have hacc := accD_lt_of_nodup hcol (fun e he => (hlt e he).2)
  have hm : ∀ c < S, (if q c then 2 ^ 136 - 1 else 0) < 2 ^ 136 := by
    intro c _; split_ifs <;> omega
  rw [packL_eq_pk (fun e he => (hlt e he).1), pk_land (fun c _ => hacc c) hm,
    packL_eq_pk (S := S) (fun e he => (hlt e (List.mem_of_mem_filter he)).1)]
  refine pk_congr fun c _ => ?_
  rw [accD_filter]
  split_ifs
  · rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hacc c)]
  · simp

/-! ## Index forms of the term lists -/

/-- The data of the `i`-th term of `td` starts at `tdi td i`. -/
def tdi (td i : ℕ) : ℕ := dtn^[i] td

theorem tdi_zero (td : ℕ) : tdi td 0 = td := rfl

theorem tdi_succ (td i : ℕ) : tdi td (i + 1) = tdi (dtn td) i := Function.iterate_succ_apply dtn i td

/-- `2^(136 c)`, the place of column `c`. -/
abbrev Xc (c : ℕ) : ℕ := 2 ^ (136 * c)

theorem packL_termsA (sp : Spec) (M s : ℕ) : ∀ cnt td, packL (termsA sp M s cnt td) =
    ∑ i ∈ Finset.range cnt, if dts (tdi td i) = s then
      M * dta (tdi td i) * Xc (sp.n * (sp.blk (dtb (tdi td i))).lo) else 0 := by
  intro cnt
  induction cnt with
  | zero => intro td; simp [termsA]
  | succ cnt ih =>
    intro td
    rw [Finset.sum_range_succ', termsA, packL_append, ih (dtn td)]
    simp only [tdi_succ, tdi_zero]
    by_cases h : dts td = s <;> simp [h, packL_cons, add_comm, Xc]

theorem packL_termsB (sp : Spec) (s : ℕ) : ∀ cnt td, packL (termsB sp s cnt td) =
    ∑ i ∈ Finset.range cnt, if dts (tdi td i) = s then dta (tdi td i) * Xc (sp.blk (dtb (tdi td i))).lo else 0 := by
  intro cnt
  induction cnt with
  | zero => intro td; simp [termsB]
  | succ cnt ih =>
    intro td
    rw [Finset.sum_range_succ', termsB, packL_append, ih (dtn td)]
    simp only [tdi_succ, tdi_zero]
    by_cases h : dts td = s <;> simp [h, packL_cons, add_comm, Xc]

theorem packL_linL_true (s0 ma0 : ℕ) : ∀ cnt td, packL (linL s0 ma0 true cnt td) =
    ∑ i ∈ Finset.range cnt, if s0 = dts (tdi td i) then ma0 * dta (tdi td i) * Xc (dtb (tdi td i)) else 0 := by
  intro cnt
  induction cnt with
  | zero => intro td; simp [linL]
  | succ cnt ih =>
    intro td
    rw [Finset.sum_range_succ', linL, packL_append, ih (dtn td)]
    simp only [tdi_succ, tdi_zero]
    by_cases h : s0 = dts td <;> simp [h, packL_cons, add_comm, Xc]

theorem packL_linL_false (s0 ma0 : ℕ) : ∀ cnt td, packL (linL s0 ma0 false cnt td) =
    ∑ i ∈ Finset.range cnt, if s0 = dts (tdi td i) then 0 else ma0 * dta (tdi td i) * Xc (dtb (tdi td i)) := by
  intro cnt
  induction cnt with
  | zero => intro td; simp [linL]
  | succ cnt ih =>
    intro td
    rw [Finset.sum_range_succ', linL, packL_append, ih (dtn td)]
    simp only [tdi_succ, tdi_zero]
    by_cases h : s0 = dts td <;> simp [h, packL_cons, add_comm, Xc]

theorem packL_mixP (P : KP) (b s ma : ℕ) : ∀ cnt td, packL (mixP P b s ma cnt td) =
    ∑ j ∈ Finset.range cnt, if s = dts (tdi td j) then 0 else ma * dta (tdi td j) * Xc (canonT P b (dtb (tdi td j))) := by
  intro cnt
  induction cnt with
  | zero => intro td; simp [mixP]
  | succ cnt ih =>
    intro td
    rw [Finset.sum_range_succ', mixP, packL_append, ih (dtn td)]
    simp only [tdi_succ, tdi_zero]
    by_cases h : s = dts td <;> simp [h, packL_cons, add_comm, Xc]

theorem packL_mixN (P : KP) (b s ma : ℕ) : ∀ cnt td, packL (mixN P b s ma cnt td) =
    ∑ j ∈ Finset.range cnt, if s = dts (tdi td j) then ma * dta (tdi td j) * Xc (canonT P b (dtb (tdi td j))) else 0 := by
  intro cnt
  induction cnt with
  | zero => intro td; simp [mixN]
  | succ cnt ih =>
    intro td
    rw [Finset.sum_range_succ', mixN, packL_append, ih (dtn td)]
    simp only [tdi_succ, tdi_zero]
    by_cases h : s = dts td <;> simp [h, packL_cons, add_comm, Xc]

theorem sum_lt_succ (F : ℕ → ℕ → ℕ) (cnt : ℕ) :
    (∑ i ∈ Finset.range (cnt + 1), ∑ j ∈ Finset.range (cnt + 1), if i < j then F i j else 0) =
      (∑ j ∈ Finset.range cnt, F 0 (j + 1)) +
        ∑ i ∈ Finset.range cnt, ∑ j ∈ Finset.range cnt, if i < j then F (i + 1) (j + 1) else 0 := by
  rw [Finset.sum_range_succ']
  simp only [Finset.sum_range_succ', lt_irrefl, Nat.not_lt_zero, if_false, add_zero, Nat.succ_lt_succ_iff,
    Nat.zero_lt_succ, if_true]
  ring

/-- The pairwise path's additions to `pos` in index form. -/
theorem packL_outP (P : KP) (s0 ma0 M : ℕ) : ∀ cnt td, packL (outP P s0 ma0 M cnt td) =
    (∑ i ∈ Finset.range cnt, ∑ j ∈ Finset.range cnt, if i < j then
        (if dts (tdi td i) = dts (tdi td j) then 0 else
          2 * (M * dta (tdi td i)) * dta (tdi td j) * Xc (canonT P (dtb (tdi td i)) (dtb (tdi td j)))) else 0) +
      ∑ i ∈ Finset.range cnt, if s0 = dts (tdi td i) then 0 else ma0 * dta (tdi td i) * Xc (dtb (tdi td i)) := by
  intro cnt
  induction cnt with
  | zero => intro td; simp [outP]
  | succ cnt ih =>
    intro td
    rw [outP, packL_append, packL_append, packL_mixP, ih (dtn td), sum_lt_succ, Finset.sum_range_succ' _ cnt]
    simp only [tdi_succ, tdi_zero]
    by_cases h : s0 = dts td <;> simp [h, packL_cons, Xc] <;> ring

/-- The pairwise path's additions to `neg` in index form. -/
theorem packL_outN (P : KP) (s0 ma0 M : ℕ) : ∀ cnt td, packL (outN P s0 ma0 M cnt td) =
    (∑ i ∈ Finset.range cnt, M * (dta (tdi td i) * dta (tdi td i)) * Xc (canonT P (dtb (tdi td i)) (dtb (tdi td i)))) +
    (∑ i ∈ Finset.range cnt, ∑ j ∈ Finset.range cnt, if i < j then
        (if dts (tdi td i) = dts (tdi td j) then
          2 * (M * dta (tdi td i)) * dta (tdi td j) * Xc (canonT P (dtb (tdi td i)) (dtb (tdi td j))) else 0) else 0) +
      ∑ i ∈ Finset.range cnt, if s0 = dts (tdi td i) then ma0 * dta (tdi td i) * Xc (dtb (tdi td i)) else 0 := by
  intro cnt
  induction cnt with
  | zero => intro td; simp [outN]
  | succ cnt ih =>
    intro td
    rw [outN, packL_cons, packL_append, packL_append, packL_mixN, ih (dtn td), sum_lt_succ,
      Finset.sum_range_succ' _ cnt, Finset.sum_range_succ' _ cnt]
    simp only [tdi_succ, tdi_zero]
    by_cases h : s0 = dts td <;> simp [h, packL_cons, Xc] <;> ring

/-! ## Digit masks on sums over pairs of distinct positions -/

theorem sum_eq_pk (s : Finset (ℕ × ℕ)) (col : ℕ × ℕ → ℕ) (f : ℕ × ℕ → ℕ) (N : ℕ)
    (hcol : ∀ x ∈ s, col x < N) :
    ∑ x ∈ s, f x * Xc (col x) = pk 136 (fun c => ∑ x ∈ s.filter (fun x => col x = c), f x) N := by
  unfold pk
  rw [← Finset.sum_fiberwise_of_maps_to (g := col) (t := Finset.range N) (fun x hx => Finset.mem_range.mpr (hcol x hx))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [(Finset.mem_filter.mp hx).2]

theorem col_div {n a b : ℕ} (hb : b < n) : (n * a + b) / n = a := by
  have hn : 0 < n := by omega
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hb, Nat.zero_add]

theorem col_mod {n a b : ℕ} (hb : b < n) : (n * a + b) % n = b := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]

/-- Masking a sum over ordered pairs of distinct positions (`n p_i + p_j`, one-digit weights) keeps the pairs whose
positions satisfy `Q`. -/
theorem mask_pairs (n : ℕ) (R : Finset ℕ) (p : ℕ → ℕ) (w : ℕ → ℕ → ℕ) (Q : ℕ → ℕ → Prop) [DecidableRel Q]
    (hp : ∀ i ∈ R, p i < n) (hinj : ∀ i ∈ R, ∀ j ∈ R, p i = p j → i = j) (hw : ∀ i j, w i j < 2 ^ 136) :
    (∑ i ∈ R, ∑ j ∈ R, w i j * Xc (n * p i + p j)) &&&
        pk 136 (fun c => if Q (c / n) (c % n) then 2 ^ 136 - 1 else 0) (n * n) =
      ∑ i ∈ R, ∑ j ∈ R, if Q (p i) (p j) then w i j * Xc (n * p i + p j) else 0 := by
  have hcol : ∀ x ∈ R ×ˢ R, n * p x.1 + p x.2 < n * n := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hx
    have := hp _ h1; have := hp _ h2
    nlinarith
  have hinj2 : ∀ x ∈ R ×ˢ R, ∀ y ∈ R ×ˢ R, n * p x.1 + p x.2 = n * p y.1 + p y.2 → x = y := by
    intro x hx y hy hxy
    obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hx
    obtain ⟨hy1, hy2⟩ := Finset.mem_product.mp hy
    have e1 := congrArg (· / n) hxy; have e2 := congrArg (· % n) hxy
    simp only [col_div (hp _ hx2), col_div (hp _ hy2)] at e1
    simp only [col_mod (hp _ hx2), col_mod (hp _ hy2)] at e2
    exact Prod.ext (hinj _ hx1 _ hy1 e1) (hinj _ hx2 _ hy2 e2)
  -- digits of the sum: at most one pair per column
  have hdig : ∀ c, (∑ x ∈ (R ×ˢ R).filter (fun x => n * p x.1 + p x.2 = c), w x.1 x.2) < 2 ^ 136 := by
    intro c
    rcases Finset.eq_empty_or_nonempty ((R ×ˢ R).filter (fun x => n * p x.1 + p x.2 = c)) with he | ⟨x, hx⟩
    · rw [he, Finset.sum_empty]; positivity
    · have hsingle : (R ×ˢ R).filter (fun x => n * p x.1 + p x.2 = c) = {x} := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · intro hy
          have hx' := Finset.mem_filter.mp hx
          exact hinj2 y hy.1 x hx'.1 (hy.2.trans hx'.2.symm)
        · intro hy; subst hy; exact Finset.mem_filter.mp hx
      rw [hsingle, Finset.sum_singleton]; exact hw _ _
  have hL := sum_eq_pk (R ×ˢ R) (fun x => n * p x.1 + p x.2) (fun x => w x.1 x.2) (n * n) hcol
  have hR := sum_eq_pk (R ×ˢ R) (fun x => n * p x.1 + p x.2)
    (fun x => if Q (p x.1) (p x.2) then w x.1 x.2 else 0) (n * n) hcol
  rw [← Finset.sum_product' (f := fun i j => w i j * Xc (n * p i + p j)), hL]
  rw [show (∑ i ∈ R, ∑ j ∈ R, if Q (p i) (p j) then w i j * Xc (n * p i + p j) else 0) =
      ∑ x ∈ R ×ˢ R, (if Q (p x.1) (p x.2) then w x.1 x.2 else 0) * Xc (n * p x.1 + p x.2) by
    rw [← Finset.sum_product' (f := fun i j => if Q (p i) (p j) then w i j * Xc (n * p i + p j) else 0)]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp, hR]
  rw [pk_land (fun c _ => hdig c) (fun c _ => by split_ifs <;> omega)]
  refine pk_congr fun c hc => ?_
  by_cases hq : Q (c / n) (c % n)
  · rw [if_pos hq, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hdig c)]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := Finset.mem_filter.mp hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hx'.1
    rw [← hx'.2, col_div (hp _ hx2), col_mod (hp _ hx2)] at hq
    rw [if_pos hq]
  · rw [if_neg hq, Nat.and_zero]
    symm
    refine Finset.sum_eq_zero fun x hx => ?_
    have hx' := Finset.mem_filter.mp hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hx'.1
    rw [← hx'.2, col_div (hp _ hx2), col_mod (hp _ hx2)] at hq
    rw [if_neg hq]

/-- Ordered pairs with increasing positions = pairs with increasing indices, for a symmetric weight. -/
theorem sym_pairs (R : Finset ℕ) (p : ℕ → ℕ) (F : ℕ → ℕ → ℕ)
    (hinj : ∀ i ∈ R, ∀ j ∈ R, p i = p j → i = j) (hsym : ∀ i j, F i j = F j i) :
    (∑ i ∈ R, ∑ j ∈ R, if p i < p j then F i j else 0) = ∑ i ∈ R, ∑ j ∈ R, if i < j then F i j else 0 := by
  have hL : ∀ i ∈ R, ∀ j ∈ R, (if p i < p j then F i j else 0) =
      (if i < j ∧ p i < p j then F i j else 0) + (if j < i ∧ p i < p j then F i j else 0) := by
    intro i _ j _
    rcases lt_trichotomy i j with h | h | h
    · simp [h, Nat.lt_asymm h]
    · subst h; simp
    · simp [h, Nat.lt_asymm h]
  have hR : ∀ i ∈ R, ∀ j ∈ R, (if i < j then F i j else 0) =
      (if i < j ∧ p i < p j then F i j else 0) + (if i < j ∧ p j < p i then F i j else 0) := by
    intro i hi j hj
    by_cases h : i < j
    · have hne : p i ≠ p j := fun e => absurd (hinj i hi j hj e) (Nat.ne_of_lt h)
      rcases Nat.lt_or_gt_of_ne hne with h' | h'
      · simp [h, h', Nat.lt_asymm h']
      · simp [h, h', Nat.lt_asymm h']
    · simp [h]
  have hswap : (∑ i ∈ R, ∑ j ∈ R, if j < i ∧ p i < p j then F i j else 0) =
      ∑ i ∈ R, ∑ j ∈ R, if i < j ∧ p j < p i then F i j else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsym]
  calc (∑ i ∈ R, ∑ j ∈ R, if p i < p j then F i j else 0)
      = ∑ i ∈ R, ∑ j ∈ R, ((if i < j ∧ p i < p j then F i j else 0) +
          (if j < i ∧ p i < p j then F i j else 0)) :=
        Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => hL i hi j hj
    _ = (∑ i ∈ R, ∑ j ∈ R, if i < j ∧ p i < p j then F i j else 0) +
          ∑ i ∈ R, ∑ j ∈ R, if j < i ∧ p i < p j then F i j else 0 := by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
    _ = (∑ i ∈ R, ∑ j ∈ R, if i < j ∧ p i < p j then F i j else 0) +
          ∑ i ∈ R, ∑ j ∈ R, if i < j ∧ p j < p i then F i j else 0 := by rw [hswap]
    _ = ∑ i ∈ R, ∑ j ∈ R, if i < j then F i j else 0 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j hj => (hR i hi j hj).symm

/-! ## Positions of the terms -/

theorem leafDistinct_props (sp : Spec) : ∀ cnt td seen, LeafDistinct sp cnt td seen →
    (∀ i < cnt, sp.isLeaf (dtb (tdi td i)) = true ∧ (sp.blk (dtb (tdi td i))).lo < sp.n ∧
      Nat.testBit seen (sp.blk (dtb (tdi td i))).lo = false) ∧
    (∀ i < cnt, ∀ j < cnt, (sp.blk (dtb (tdi td i))).lo = (sp.blk (dtb (tdi td j))).lo → i = j) := by
  intro cnt
  induction cnt with
  | zero => intro td seen _; exact ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ cnt ih =>
    intro td seen h
    obtain ⟨hl, hlt, hbit, hrest⟩ := h
    obtain ⟨h1, h2⟩ := ih (dtn td) _ hrest
    have tail : ∀ i < cnt, Nat.testBit (seen ||| 2 ^ (sp.blk (dtb td)).lo) (sp.blk (dtb (tdi (dtn td) i))).lo = false :=
      fun i hi => (h1 i hi).2.2
    refine ⟨fun i hi => ?_, fun i hi j hj hij => ?_⟩
    · rcases i with _ | i
      · exact ⟨hl, hlt, hbit⟩
      · rw [tdi_succ]
        obtain ⟨a, b, c⟩ := h1 i (by omega)
        refine ⟨a, b, ?_⟩
        rw [Nat.testBit_lor, Bool.or_eq_false_iff] at c
        exact c.1
    · rcases i with _ | i <;> rcases j with _ | j
      · rfl
      · rw [tdi_succ, tdi_zero] at hij
        have := tail j (by omega)
        rw [← hij, Nat.testBit_lor, Nat.testBit_two_pow_self, Bool.or_true] at this
        exact absurd this (by simp)
      · rw [tdi_succ, tdi_zero] at hij
        have := tail i (by omega)
        rw [hij, Nat.testBit_lor, Nat.testBit_two_pow_self, Bool.or_true] at this
        exact absurd this (by simp)
      · rw [tdi_succ, tdi_succ] at hij
        exact congrArg (· + 1) (h2 i (by omega) j (by omega) hij)

/-- Products of the packed vectors as sums over ordered pairs of terms. -/
theorem prod_terms (sp : Spec) (M kk td s s' : ℕ) :
    packL (termsA sp M s kk td) * packL (termsB sp s' kk td) =
      ∑ i ∈ Finset.range kk, ∑ j ∈ Finset.range kk,
        (if dts (tdi td i) = s ∧ dts (tdi td j) = s' then M * dta (tdi td i) * dta (tdi td j) else 0) *
          Xc (sp.n * (sp.blk (dtb (tdi td i))).lo + (sp.blk (dtb (tdi td j))).lo) := by
  rw [packL_termsA, packL_termsB, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h1 : dts (tdi td i) = s <;> by_cases h2 : dts (tdi td j) = s' <;> simp [h1, h2, Xc, mul_add, pow_add] <;> ring

/-! ## The product path computes the pairwise path exactly -/

theorem dAll_tdi (nB : ℕ) : ∀ cnt td, dAll nB cnt td → ∀ i < cnt, dtb (tdi td i) < nB := by
  intro cnt
  induction cnt with
  | zero => intro td _ i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ cnt ih =>
    intro td h i hi
    obtain ⟨h0, hrest⟩ := h
    rcases i with _ | i
    · exact h0
    · rw [tdi_succ]; exact ih (dtn td) hrest i (by omega)

theorem atc_mul (v c : ℕ) : atc v c = v * 2 ^ (136 * c) := by
  simp [atc, raw_shiftLeft, raw_mul, Nat.shiftLeft_eq]

theorem denseFast_eq (hkp : KPFacts sp P) {lpos maskD maskU : ℕ} (hP : ProdFacts sp lpos maskD maskU)
    {M a0 s0 kk td : ℕ} (hM : M < 2 ^ 64) (hall : dAll P.nB kk td)
    (hok : (kLoop lpos sp.n M (2 * (M * a0)) s0 kk td acc0).ok = true) :
    denseFast sp.oZ maskD maskU (kLoop lpos sp.n M (2 * (M * a0)) s0 kk td acc0) =
      (packL (outP P s0 (2 * (M * a0)) M kk td), packL (outN P s0 (2 * (M * a0)) M kk td)) := by
  have hn : sp.n < 255 := by have := hkp.n64; rw [hkp.n] at this; omega
  have hall' : dAll sp.nB kk td := hkp.nB ▸ hall
  obtain ⟨-, hLD, hap, han, hbp, hbn, hlp, hln⟩ := kLoop_spec hP hn M (2 * (M * a0)) s0 kk td acc0 hall' hok
  obtain ⟨hpos, hinj⟩ := leafDistinct_props sp kk td 0 hLD
  have hblk := dAll_tdi sp.nB kk td hall'
  generalize kLoop lpos sp.n M (2 * (M * a0)) s0 kk td acc0 = f at hap han hbp hbn hlp hln ⊢
  simp only [show acc0.ap = 0 from rfl, show acc0.an = 0 from rfl, show acc0.bp = 0 from rfl,
    show acc0.bn = 0 from rfl, show acc0.lp = 0 from rfl, show acc0.ln = 0 from rfl, zero_add] at hap han hbp hbn hlp hln
  -- notation
  set R := Finset.range kk with hR
  set pos : ℕ → ℕ := fun i => (sp.blk (dtb (tdi td i))).lo with hpos_def
  set wS : ℕ → ℕ → ℕ := fun i j =>
    if dts (tdi td i) = dts (tdi td j) then M * dta (tdi td i) * dta (tdi td j) else 0 with hwS
  set wX : ℕ → ℕ → ℕ := fun i j =>
    if dts (tdi td i) = dts (tdi td j) then 0 else M * dta (tdi td i) * dta (tdi td j) with hwX
  have hposlt : ∀ i ∈ R, pos i < sp.n := fun i hi => (hpos i (Finset.mem_range.mp hi)).2.1
  have hinjR : ∀ i ∈ R, ∀ j ∈ R, pos i = pos j → i = j :=
    fun i hi j hj h => hinj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) h
  -- one-digit weights
  have hprod : ∀ i j, M * dta (tdi td i) * dta (tdi td j) < 2 ^ 136 := by
    intro i j
    have h1 := dta_lt (tdi td i); have h2 := dta_lt (tdi td j)
    calc M * dta (tdi td i) * dta (tdi td j) < 2 ^ 64 * 2 ^ 21 * 2 ^ 21 := by
          apply Nat.mul_lt_mul'' (Nat.mul_lt_mul'' hM h1) h2
      _ ≤ 2 ^ 136 := by norm_num
  have hwS_lt : ∀ i j, wS i j < 2 ^ 136 := fun i j => by
    simp only [hwS]; split_ifs
    · exact hprod i j
    · positivity
  have hwX_lt : ∀ i j, wX i j < 2 ^ 136 := fun i j => by
    simp only [hwX]; split_ifs
    · positivity
    · exact hprod i j
  -- products as pair sums
  have hS : f.ap * f.bp + f.an * f.bn = ∑ i ∈ R, ∑ j ∈ R, wS i j * Xc (sp.n * pos i + pos j) := by
    rw [hap, hbp, han, hbn, prod_terms, prod_terms, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hi := dts_lt (tdi td i); have hj := dts_lt (tdi td j)
    simp only [hwS, hpos_def]
    rcases (by omega : dts (tdi td i) = 0 ∨ dts (tdi td i) = 1) with h1 | h1 <;>
      rcases (by omega : dts (tdi td j) = 0 ∨ dts (tdi td j) = 1) with h2 | h2 <;> simp [h1, h2]
  have hX : f.ap * f.bn + f.an * f.bp = ∑ i ∈ R, ∑ j ∈ R, wX i j * Xc (sp.n * pos i + pos j) := by
    rw [hap, hbp, han, hbn, prod_terms, prod_terms, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hi := dts_lt (tdi td i); have hj := dts_lt (tdi td j)
    simp only [hwX, hpos_def]
    rcases (by omega : dts (tdi td i) = 0 ∨ dts (tdi td i) = 1) with h1 | h1 <;>
      rcases (by omega : dts (tdi td j) = 0 ∨ dts (tdi td j) = 1) with h2 | h2 <;> simp [h1, h2]
  -- the masks
  have hmD : maskD = pk 136 (fun c => if c / sp.n = c % sp.n then 2 ^ 136 - 1 else 0) (sp.n * sp.n) := hP.maskD
  have hmU : maskU = pk 136 (fun c => if c / sp.n < c % sp.n then 2 ^ 136 - 1 else 0) (sp.n * sp.n) := hP.maskU
  have mD := mask_pairs sp.n R pos wS (· = ·) hposlt hinjR hwS_lt
  have mU := mask_pairs sp.n R pos wS (· < ·) hposlt hinjR hwS_lt
  have mXU := mask_pairs sp.n R pos wX (· < ·) hposlt hinjR hwX_lt
  -- diagonal: only `i = j`
  have hdiag : (∑ i ∈ R, ∑ j ∈ R, if pos i = pos j then wS i j * Xc (sp.n * pos i + pos j) else 0) =
      ∑ i ∈ R, M * (dta (tdi td i) * dta (tdi td i)) * Xc (sp.n * pos i + pos i) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single i]
    · simp [hwS, mul_assoc]
    · intro j hj hji
      rw [if_neg (fun h => hji (hinjR i hi j hj h).symm)]
    · intro h; exact absurd hi h
  -- upper triangle: symmetrize
  have hsymU : ∀ w : ℕ → ℕ → ℕ, (∀ i j, w i j = w j i) →
      (∑ i ∈ R, ∑ j ∈ R, if pos i < pos j then w i j * Xc (sp.n * pos i + pos j) else 0) =
        ∑ i ∈ R, ∑ j ∈ R, if i < j then w i j * Xc (sp.n * min (pos i) (pos j) + max (pos i) (pos j)) else 0 := by
    intro w hw
    rw [← sym_pairs R pos (fun i j => w i j * Xc (sp.n * min (pos i) (pos j) + max (pos i) (pos j))) hinjR
      (fun i j => by rw [hw, min_comm, max_comm])]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : pos i < pos j
    · rw [if_pos h, if_pos h, min_eq_left h.le, max_eq_right h.le]
    · rw [if_neg h, if_neg h]
  have hwS_sym : ∀ i j, wS i j = wS j i := fun i j => by
    simp only [hwS]; by_cases h : dts (tdi td i) = dts (tdi td j)
    · rw [if_pos h, if_pos h.symm]; ring
    · rw [if_neg h, if_neg (Ne.symm h)]
  have hwX_sym : ∀ i j, wX i j = wX j i := fun i j => by
    simp only [hwX]; by_cases h : dts (tdi td i) = dts (tdi td j)
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]; ring
  -- columns of the pairwise path
  have hcanon : ∀ i ∈ R, ∀ j ∈ R, canonT P (dtb (tdi td i)) (dtb (tdi td j)) =
      sp.oZ + (sp.n * min (pos i) (pos j) + max (pos i) (pos j)) := by
    intro i hi j hj
    have hi' := Finset.mem_range.mp hi; have hj' := Finset.mem_range.mp hj
    rw [canonT_eq hkp (hblk i hi') (hblk j hj'), canon_leaf (hpos i hi').1 (hpos j hj').1]
    simp only [hpos_def]; ring
  have hX_split : ∀ a b, Xc (a + b) = Xc a * Xc b := fun a b => by simp only [Xc, mul_add, pow_add]
  unfold denseFast
  simp only [raw_add, raw_mul, raw_land, raw_shiftLeft, Nat.shiftLeft_eq, pow_one, atc_mul]
  refine Prod.ext ?_ ?_ <;> dsimp only
  · -- `pos`: opposite-sign pairs
    rw [hX, hmU, mXU, hsymU wX hwX_sym, packL_outP, hlp, packL_linL_false, add_comm]
    simp only [← hR]
    congr 1
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    by_cases hij : i < j
    · rw [if_pos hij, if_pos hij, hcanon i hi j hj, hX_split]
      simp only [hwX]
      by_cases h : dts (tdi td i) = dts (tdi td j)
      · simp [h]
      · simp [h, Xc]; ring
    · simp [hij]
  · -- `neg`: diagonal and same-sign pairs
    rw [hS, hmD, hmU, mD, mU, hdiag, hsymU wS hwS_sym, packL_outN, hln, packL_linL_true]
    simp only [← hR]
    have e1 : ∀ i ∈ R, M * (dta (tdi td i) * dta (tdi td i)) * Xc (canonT P (dtb (tdi td i)) (dtb (tdi td i))) =
        M * (dta (tdi td i) * dta (tdi td i)) * Xc (sp.n * pos i + pos i) * 2 ^ (136 * sp.oZ) := by
      intro i hi
      rw [hcanon i hi i hi, min_self, max_self, hX_split]
      simp only [Xc]; ring
    have e2 : ∀ i ∈ R, ∀ j ∈ R, (if i < j then (if dts (tdi td i) = dts (tdi td j) then
          2 * (M * dta (tdi td i)) * dta (tdi td j) * Xc (canonT P (dtb (tdi td i)) (dtb (tdi td j))) else 0)
        else 0) =
        (if i < j then wS i j * Xc (sp.n * min (pos i) (pos j) + max (pos i) (pos j)) else 0) * 2 *
          2 ^ (136 * sp.oZ) := by
      intro i hi j hj
      by_cases hij : i < j
      · rw [if_pos hij, if_pos hij, hcanon i hi j hj, hX_split]
        simp only [hwS]
        by_cases h : dts (tdi td i) = dts (tdi td j)
        · simp [h, Xc]; ring
        · simp [h]
      · simp [hij]
    have hd : (∑ i ∈ R, M * (dta (tdi td i) * dta (tdi td i)) * Xc (canonT P (dtb (tdi td i)) (dtb (tdi td i)))) =
        (∑ i ∈ R, M * (dta (tdi td i) * dta (tdi td i)) * Xc (sp.n * pos i + pos i)) * 2 ^ (136 * sp.oZ) := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl e1
    have hp : (∑ i ∈ R, ∑ j ∈ R, if i < j then (if dts (tdi td i) = dts (tdi td j) then
          2 * (M * dta (tdi td i)) * dta (tdi td j) * Xc (canonT P (dtb (tdi td i)) (dtb (tdi td j))) else 0)
        else 0) =
        (∑ i ∈ R, ∑ j ∈ R, if i < j then wS i j * Xc (sp.n * min (pos i) (pos j) + max (pos i) (pos j)) else 0) * 2 *
          2 ^ (136 * sp.oZ) := by
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j hj => e2 i hi j hj
    rw [hd, hp]
    ring

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
  -- v2: both paths add the pairwise sums (`denseFast_eq` for the product path)
  have h2 : k data' (rp + packL (outP P s0 (2 * (M * a0)) M kk td)) (rn + packL (outN P s0 (2 * (M * a0)) M kk td))
      tp tn ap (an + M * (a0 * a0) * 2 ^ 30) = true := by
    cases hok : (kLoop P.lpos P.n M (Nat.mul 2 (Nat.mul M a0)) s0 kk td acc0).ok
    · rw [hok, sel_false, dOuter_eq] at h
      simpa only [zero_add, raw_add, raw_mul, raw_shiftLeft, Nat.shiftLeft_eq] using h
    · rw [hok, sel_true] at h
      have hok' : (kLoop P.lpos sp.n M (2 * (M * a0)) s0 kk td acc0).ok = true := by
        rw [← hkp.n]; exact hok
      have hdf := denseFast_eq hkp hkp.prod bM hall hok'
      rw [← hkp.n, ← hkp.oZ] at hdf
      simp only [raw_add, raw_mul, raw_shiftLeft, Nat.shiftLeft_eq] at h hdf ⊢
      rw [hdf] at h
      exact h
  clear h
  have h := h2
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

end AutocorrK2
