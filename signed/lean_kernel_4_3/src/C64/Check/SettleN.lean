import C64.Check.SettleL

/-!
# Nested node sets (Section 6, earlier numbering: Lemma X, L8-iv, Theorem 3, tubes)

A node set is a pinned set (mass `≤ τ`, crossing disc, boxes) with interval tubes: for a tube on the arc
`z([q₀, q₁])` of a tile with base transform `w₀`, a point `z = z(q)` and `m ≥ 0` with
`‖μ̂(z) - S(z) - m (S(z) - w₀(z))‖ ≤ ε`.  The node sets are not convex; separation (`nodeSet_tile_ne`) is proved for
convex combinations of two members, emptiness (`nodeSet_empty`) for members.  The witness step
(`nodeSettled_of_witness`) is Lemma X in winding-number form: if the homotopy from `G_{w_rep}` to `G_μ` along the
tile has no zero, `μ` has an odd-winding ellipse; a zero on a W1 arc is excluded by separation; a zero on a hard arc
puts `μ` exactly on the new tube, i.e. in the child's node set.
-/

open MeasureTheory Set Complex Real ComplexConjugate

namespace C64

/-- An interval tube: the tile `(c, a, b)`, the arc `[q₀, q₁]` and the transform `w₀` of its base measure. -/
structure TubeR where
  c : ℂ
  a : ℝ
  b : ℝ
  q0 : ℝ
  q1 : ℝ
  w0 : ℂ → ℂ

/-- The point of the tile at `q`. -/
noncomputable def TubeR.pt (tb : TubeR) (q : ℝ) : ℂ := ellipse tb.c tb.a tb.b q

/-- `μ` meets the tube. -/
def TubeIn (eps : ℝ) (tb : TubeR) (μ : Measure ℝ) : Prop :=
  ∃ q ∈ Icc tb.q0 tb.q1, ∃ m : ℝ, 0 ≤ m ∧
    ‖hat μ (tb.pt q) - S (tb.pt q) - (m : ℂ) * (S (tb.pt q) - tb.w0 (tb.pt q))‖ ≤ eps

/-- The node set: the pinned set with the tubes. -/
def NodeSet (τ : ℝ) (zc : ℂ) (r : ℝ) (pq : List (ℂ × Box)) (eps : ℝ) (tubes : List TubeR) (μ : Measure ℝ) : Prop :=
  PinnedL τ zc r pq μ ∧ ∀ tb ∈ tubes, TubeIn eps tb μ

/-- Every member of the node set has an odd-winding ellipse. -/
def NodeSettled (τ : ℝ) (zc : ℂ) (r : ℝ) (pq : List (ℂ × Box)) (eps : ℝ) (tubes : List TubeR) : Prop :=
  ∀ μ : Measure ℝ, NodeSet τ zc r pq eps tubes μ → OddLoop μ

lemma NodeSet.mono {τ τ' r r' eps : ℝ} {zc : ℂ} {pq : List (ℂ × Box)} {tubes : List TubeR} {μ : Measure ℝ}
    (h : NodeSet τ zc r pq eps tubes μ) (hτ : τ ≤ τ') (hr : r ≤ r') : NodeSet τ' zc r' pq eps tubes μ :=
  ⟨h.1.mono hτ hr, h.2⟩

/-! ### Sums of tube terms -/

/-- `Σ Re(conj(vt) K_t(z))`. -/
noncomputable def TL (vz : List (ℂ × ℂ)) (t : ℝ) : ℝ := (vz.map fun x => (conj x.1 * Kt t x.2).re).sum

lemma continuous_TL (vz : List (ℂ × ℂ)) : Continuous (TL vz) := by
  unfold TL
  induction vz with
  | nil => simp only [List.map_nil, List.sum_nil]; exact continuous_const
  | cons x vz ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (continuous_re_conj_mul_Kt x.1 x.2).add ih

lemma integrable_TLsum {τ : ℝ} {μ : Measure ℝ} (hμ : ClassA τ μ) (vz : List (ℂ × ℂ)) :
    Integrable (fun t => (vz.map fun x => (conj x.1 * Kt t x.2).re).sum) μ := by
  induction vz with
  | nil => have := hμ.1; simp only [List.map_nil, List.sum_nil]; exact integrable_const (0 : ℝ)
  | cons x vz ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (integrable_re_conj_mul_Kt hμ x.1 x.2).add ih

lemma integral_TLsum {τ : ℝ} {μ : Measure ℝ} (hμ : ClassA τ μ) (vz : List (ℂ × ℂ)) :
    ∫ t, (vz.map fun x => (conj x.1 * Kt t x.2).re).sum ∂μ = (vz.map fun x => (conj x.1 * hat μ x.2).re).sum := by
  induction vz with
  | nil => simp
  | cons x vz ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add (integrable_re_conj_mul_Kt hμ x.1 x.2) (integrable_TLsum hμ vz), ih, re_conj_mul_hat hμ]

lemma integrable_TL {τ : ℝ} {μ : Measure ℝ} (hμ : ClassA τ μ) (vz : List (ℂ × ℂ)) : Integrable (TL vz) μ :=
  integrable_TLsum hμ vz

lemma integral_TL {τ : ℝ} {μ : Measure ℝ} (hμ : ClassA τ μ) (vz : List (ℂ × ℂ)) :
    ∫ t, TL vz t ∂μ = (vz.map fun x => (conj x.1 * hat μ x.2).re).sum :=
  integral_TLsum hμ vz

/-- The tube points of a list of tubes with multipliers and bounds. -/
def TubePts (zs : List ℂ) (tv : List (TubeR × ℂ × ℝ)) : Prop :=
  List.Forall₂ (fun z (x : TubeR × ℂ × ℝ) => ∃ q ∈ Icc x.1.q0 x.1.q1, z = x.1.pt q) zs tv

/-- The multiplier terms `(vt, z)`. -/
def tvz (zs : List ℂ) (tv : List (TubeR × ℂ × ℝ)) : List (ℂ × ℂ) := List.zipWith (fun z x => (x.2.1, z)) zs tv

/-- Upper bounds of the tube terms of a member (separation). -/
lemma tubes_hi {eps : ℝ} {μ : Measure ℝ} : ∀ (tv : List (TubeR × ℂ × ℝ)),
    (∀ x ∈ tv, ∀ q ∈ Icc x.1.q0 x.1.q1, (conj x.2.1 * (S (x.1.pt q) - x.1.w0 (x.1.pt q))).re ≤ 0) →
    (∀ x ∈ tv, ∀ q ∈ Icc x.1.q0 x.1.q1, (conj x.2.1 * S (x.1.pt q)).re ≤ x.2.2) →
    (∀ x ∈ tv, TubeIn eps x.1 μ) →
    ∃ zs : List ℂ, TubePts zs tv ∧
      ((tvz zs tv).map fun x => (conj x.1 * hat μ x.2).re).sum ≤ (tv.map fun x => x.2.2 + ‖x.2.1‖ * eps).sum
  | [], _, _, _ => ⟨[], List.Forall₂.nil, by simp [tvz]⟩
  | x :: tv, hsg, hbd, hin => by
    obtain ⟨zs, hzs, hsum⟩ := tubes_hi tv (fun y hy => hsg y (List.mem_cons_of_mem _ hy))
      (fun y hy => hbd y (List.mem_cons_of_mem _ hy)) (fun y hy => hin y (List.mem_cons_of_mem _ hy))
    obtain ⟨q, hq, m, hm, hn⟩ := hin x List.mem_cons_self
    refine ⟨x.1.pt q :: zs, List.Forall₂.cons ⟨q, hq, rfl⟩ hzs, ?_⟩
    simp only [tvz, List.zipWith_cons_cons, List.map_cons, List.sum_cons] at hsum ⊢
    set z := x.1.pt q
    have hsplit : hat μ z = S z + (m : ℂ) * (S z - x.1.w0 z) +
        (hat μ z - S z - (m : ℂ) * (S z - x.1.w0 z)) := by ring
    have h1 : (conj x.2.1 * hat μ z).re = (conj x.2.1 * S z).re + m * (conj x.2.1 * (S z - x.1.w0 z)).re +
        (conj x.2.1 * (hat μ z - S z - (m : ℂ) * (S z - x.1.w0 z))).re := by
      conv_lhs => rw [hsplit]
      simp only [mul_add, Complex.add_re]
      rw [show conj x.2.1 * ((m : ℂ) * (S z - x.1.w0 z)) = (m : ℂ) * (conj x.2.1 * (S z - x.1.w0 z)) by ring,
        Complex.re_ofReal_mul]
    have h2 : (conj x.2.1 * (hat μ z - S z - (m : ℂ) * (S z - x.1.w0 z))).re ≤ ‖x.2.1‖ * eps := by
      refine (Complex.re_le_norm _).trans ?_
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    have h3 := hsg x List.mem_cons_self q hq
    have h4 := hbd x List.mem_cons_self q hq
    have h5 : m * (conj x.2.1 * (S z - x.1.w0 z)).re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm h3
    linarith

/-- Lower bounds of the tube terms of a member (emptiness). -/
lemma tubes_lo {eps : ℝ} {μ : Measure ℝ} : ∀ (tv : List (TubeR × ℂ × ℝ)),
    (∀ x ∈ tv, ∀ q ∈ Icc x.1.q0 x.1.q1, 0 ≤ (conj x.2.1 * (S (x.1.pt q) - x.1.w0 (x.1.pt q))).re) →
    (∀ x ∈ tv, ∀ q ∈ Icc x.1.q0 x.1.q1, x.2.2 ≤ (conj x.2.1 * S (x.1.pt q)).re) →
    (∀ x ∈ tv, TubeIn eps x.1 μ) →
    ∃ zs : List ℂ, TubePts zs tv ∧
      (tv.map fun x => x.2.2 - ‖x.2.1‖ * eps).sum ≤ ((tvz zs tv).map fun x => (conj x.1 * hat μ x.2).re).sum
  | [], _, _, _ => ⟨[], List.Forall₂.nil, by simp [tvz]⟩
  | x :: tv, hsg, hbd, hin => by
    obtain ⟨zs, hzs, hsum⟩ := tubes_lo tv (fun y hy => hsg y (List.mem_cons_of_mem _ hy))
      (fun y hy => hbd y (List.mem_cons_of_mem _ hy)) (fun y hy => hin y (List.mem_cons_of_mem _ hy))
    obtain ⟨q, hq, m, hm, hn⟩ := hin x List.mem_cons_self
    refine ⟨x.1.pt q :: zs, List.Forall₂.cons ⟨q, hq, rfl⟩ hzs, ?_⟩
    simp only [tvz, List.zipWith_cons_cons, List.map_cons, List.sum_cons] at hsum ⊢
    set z := x.1.pt q
    have hsplit : hat μ z = S z + (m : ℂ) * (S z - x.1.w0 z) +
        (hat μ z - S z - (m : ℂ) * (S z - x.1.w0 z)) := by ring
    have h1 : (conj x.2.1 * hat μ z).re = (conj x.2.1 * S z).re + m * (conj x.2.1 * (S z - x.1.w0 z)).re +
        (conj x.2.1 * (hat μ z - S z - (m : ℂ) * (S z - x.1.w0 z))).re := by
      conv_lhs => rw [hsplit]
      simp only [mul_add, Complex.add_re]
      rw [show conj x.2.1 * ((m : ℂ) * (S z - x.1.w0 z)) = (m : ℂ) * (conj x.2.1 * (S z - x.1.w0 z)) by ring,
        Complex.re_ofReal_mul]
    have h2 : -(‖x.2.1‖ * eps) ≤ (conj x.2.1 * (hat μ z - S z - (m : ℂ) * (S z - x.1.w0 z))).re := by
      have h2a : |(conj x.2.1 * (hat μ z - S z - (m : ℂ) * (S z - x.1.w0 z))).re| ≤ ‖x.2.1‖ * eps := by
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_left hn (norm_nonneg _)
      linarith [neg_abs_le (conj x.2.1 * (hat μ z - S z - (m : ℂ) * (S z - x.1.w0 z))).re]
    have h3 := hsg x List.mem_cons_self q hq
    have h4 := hbd x List.mem_cons_self q hq
    have h5 : 0 ≤ m * (conj x.2.1 * (S z - x.1.w0 z)).re := mul_nonneg hm h3
    linarith

/-! ### Separation and emptiness (L8-iv) -/

/-- Separation at `p` for convex combinations of two members of the node set. -/
theorem nodeSet_tile_ne {τ' : ℝ} (hτ : 0 ≤ τ') {zc : ℂ} {r' eps : ℝ} {ds : List PinD}
    {tv : List (TubeR × ℂ × ℝ)} {u v : ℂ} (hbox : ∀ d ∈ ds, BoxBounds d.y d.Q d.lo d.hi) {p : ℂ}
    (hX : (conj v * S zc).re ≤ 0)
    (hsg : ∀ x ∈ tv, ∀ q ∈ Icc x.1.q0 x.1.q1, (conj x.2.1 * (S (x.1.pt q) - x.1.w0 (x.1.pt q))).re ≤ 0)
    (hbd : ∀ x ∈ tv, ∀ q ∈ Icc x.1.q0 x.1.q1, (conj x.2.1 * S (x.1.pt q)).re ≤ x.2.2)
    (hW : ∀ zs : List ℂ, TubePts zs tv → ∀ t ∈ Icc (-1/2 : ℝ) (1/2),
      τ' * ((conj u * Kt t p).re - LamL v zc ds t - TL (tvz zs tv) t) <
        (conj u * S p).re - (conj v * S zc).re - ‖v‖ * r' - (ds.map fun d => d.hi).sum -
          (tv.map fun x => x.2.2 + ‖x.2.1‖ * eps).sum)
    (hWpos : 0 < (conj u * S p).re - (conj v * S zc).re - ‖v‖ * r' - (ds.map fun d => d.hi).sum -
      (tv.map fun x => x.2.2 + ‖x.2.1‖ * eps).sum)
    {μ ν : Measure ℝ} (hμ : NodeSet τ' zc r' (pqOf ds) eps (tv.map Prod.fst) μ)
    (hν : NodeSet τ' zc r' (pqOf ds) eps (tv.map Prod.fst) ν)
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) : S p - ((1 - θ) * hat μ p + θ * hat ν p) ≠ 0 := by
  set W := (conj u * S p).re - (conj v * S zc).re - ‖v‖ * r' - (ds.map fun d => d.hi).sum -
    (tv.map fun x => x.2.2 + ‖x.2.1‖ * eps).sum
  have key : ∀ ρ : Measure ℝ, NodeSet τ' zc r' (pqOf ds) eps (tv.map Prod.fst) ρ →
      (conj u * hat ρ p).re < (conj u * S p).re := by
    intro ρ ⟨⟨hA, ⟨σ, hσ1, hσr⟩, hQ⟩, hT⟩
    obtain ⟨zs, hzs, hsum⟩ := tubes_hi tv hsg hbd (fun x hx => hT x.1 (List.mem_map_of_mem hx))
    set φ : ℝ → ℝ := fun t => (conj u * Kt t p).re - LamL v zc ds t - TL (tvz zs tv) t with hφ
    have hφc : Continuous φ :=
      ((continuous_re_conj_mul_Kt u p).sub (continuous_LamL v zc ds)).sub (continuous_TL _)
    obtain ⟨t₀, ht₀, hmax⟩ := exists_max_on_Icc hφc
    set B := max 0 (φ t₀)
    have hB0 : 0 ≤ B := le_max_left _ _
    have hτB : τ' * B < W := by
      rcases le_total (φ t₀) 0 with h | h
      · rw [show B = 0 from max_eq_left h, mul_zero]; exact hWpos
      · rw [show B = φ t₀ from max_eq_right h]; exact hW zs hzs t₀ ht₀
    have hint := integral_le_of_classA hA hτ (φ := φ)
      (((integrable_re_conj_mul_Kt hA u p).sub (integrable_LamL hA v zc ds)).sub (integrable_TL hA _))
      hB0 (fun t ht => (hmax t ht).trans (le_max_right _ _))
    simp only [hφ] at hint
    have hI1 : Integrable (fun t => (conj u * Kt t p).re - LamL v zc ds t) ρ :=
      (integrable_re_conj_mul_Kt hA u p).sub (integrable_LamL hA v zc ds)
    rw [integral_sub hI1 (integrable_TL hA _),
      integral_sub (integrable_re_conj_mul_Kt hA u p) (integrable_LamL hA v zc ds), ← re_conj_mul_hat hA,
      integral_LamL hA, integral_TL hA] at hint
    have h1 := re_conj_mul_le v (S zc) (hat ρ zc) σ hσr
    have h2 : (σ : ℝ) * (conj v * S zc).re ≤ (conj v * S zc).re := by nlinarith
    have h3 := sum_le_hi hbox hQ
    linarith
  intro h0
  have hSp : S p = (1 - θ) * hat μ p + θ * hat ν p := sub_eq_zero.1 h0
  have hre : (conj u * S p).re = (1 - θ) * (conj u * hat μ p).re + θ * (conj u * hat ν p).re := by
    rw [hSp]
    simp only [mul_add, Complex.add_re]
    rw [show conj u * ((1 - (θ : ℂ)) * hat μ p) = ((1 - θ : ℝ) : ℂ) * (conj u * hat μ p) by push_cast; ring,
      show conj u * ((θ : ℂ) * hat ν p) = (θ : ℂ) * (conj u * hat ν p) by ring,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have hk1 := key μ hμ
  have hk2 := key ν hν
  have hθ0 : 0 ≤ θ := hθ.1
  have hθ1 : 0 ≤ 1 - θ := by linarith [hθ.2]
  nlinarith [mul_le_mul_of_nonneg_left hk1.le hθ1, mul_le_mul_of_nonneg_left hk2.le hθ0]

/-- Emptiness of the node set. -/
theorem nodeSet_empty {τ' : ℝ} (hτ : 0 ≤ τ') {zc : ℂ} {r' eps : ℝ} {ds : List PinD} {tv : List (TubeR × ℂ × ℝ)}
    {v : ℂ} (hbox : ∀ d ∈ ds, BoxBounds d.y d.Q d.lo d.hi) (hX : 0 ≤ (conj v * S zc).re)
    (hsg : ∀ x ∈ tv, ∀ q ∈ Icc x.1.q0 x.1.q1, 0 ≤ (conj x.2.1 * (S (x.1.pt q) - x.1.w0 (x.1.pt q))).re)
    (hbd : ∀ x ∈ tv, ∀ q ∈ Icc x.1.q0 x.1.q1, x.2.2 ≤ (conj x.2.1 * S (x.1.pt q)).re)
    (hE : ∀ zs : List ℂ, TubePts zs tv → ∀ t ∈ Icc (-1/2 : ℝ) (1/2),
      τ' * (LamL v zc ds t + TL (tvz zs tv) t) <
        (conj v * S zc).re - ‖v‖ * r' + (ds.map fun d => d.lo).sum + (tv.map fun x => x.2.2 - ‖x.2.1‖ * eps).sum)
    (hEpos : 0 < (conj v * S zc).re - ‖v‖ * r' + (ds.map fun d => d.lo).sum +
      (tv.map fun x => x.2.2 - ‖x.2.1‖ * eps).sum)
    {μ : Measure ℝ} (hμ : NodeSet τ' zc r' (pqOf ds) eps (tv.map Prod.fst) μ) : False := by
  obtain ⟨⟨hA, ⟨σ, hσ1, hσr⟩, hQ⟩, hT⟩ := hμ
  obtain ⟨zs, hzs, hsum⟩ := tubes_lo tv hsg hbd (fun x hx => hT x.1 (List.mem_map_of_mem hx))
  set E := (conj v * S zc).re - ‖v‖ * r' + (ds.map fun d => d.lo).sum + (tv.map fun x => x.2.2 - ‖x.2.1‖ * eps).sum
  set ψ : ℝ → ℝ := fun t => LamL v zc ds t + TL (tvz zs tv) t with hψ
  have hψc : Continuous ψ := (continuous_LamL v zc ds).add (continuous_TL _)
  obtain ⟨t₀, ht₀, hmax⟩ := exists_max_on_Icc hψc
  set B := max 0 (ψ t₀)
  have hB0 : 0 ≤ B := le_max_left _ _
  have hint := integral_le_of_classA hA hτ (φ := ψ) ((integrable_LamL hA v zc ds).add (integrable_TL hA _)) hB0
    (fun t ht => (hmax t ht).trans (le_max_right _ _))
  have hτB : τ' * B < E := by
    rcases le_total (ψ t₀) 0 with h | h
    · rw [show B = 0 from max_eq_left h, mul_zero]; exact hEpos
    · rw [show B = ψ t₀ from max_eq_right h]; exact hE zs hzs t₀ ht₀
  simp only [hψ] at hint
  rw [integral_add (integrable_LamL hA v zc ds) (integrable_TL hA _), integral_LamL hA, integral_TL hA] at hint
  have h1 := re_conj_mul_ge v (S zc) (hat μ zc) σ hσr
  have h2 : (σ : ℝ) * (conj v * S zc).re ≥ (conj v * S zc).re := by nlinarith
  have h3 := sum_lo_le hbox hQ
  linarith

/-! ### The witness step (Lemma X) -/

theorem nodeSettled_of_witness {τ τ' r r' eps : ℝ} (hττ' : τ ≤ τ') (hrr' : r ≤ r') (heps : 0 ≤ eps) {zc : ℂ}
    {pq : List (ℂ × Box)} {tubes : List TubeR} {cT : ℂ} {aT bT : ℝ} (haT : 0 < aT) (hbT : 0 < bT)
    {ν : Measure ℝ} (hν : NodeSet τ' zc r' pq eps tubes ν) {n : ℤ} (hn : Odd n)
    (hwind : HasWinding (fun q => G ν (ellipse cT aT bT q)) n)
    (htile : ∀ q ∈ Icc (0 : ℝ) 1,
      (∀ μ μ' : Measure ℝ, NodeSet τ' zc r' pq eps tubes μ → NodeSet τ' zc r' pq eps tubes μ' →
        ∀ θ ∈ Icc (0 : ℝ) 1, S (ellipse cT aT bT q) -
          ((1 - θ) * hat μ (ellipse cT aT bT q) + θ * hat μ' (ellipse cT aT bT q)) ≠ 0) ∨
      ∃ a b : ℝ, q ∈ Icc a b ∧ NodeSettled τ zc r pq eps (tubes ++ [⟨cT, aT, bT, a, b, hat ν⟩])) :
    NodeSettled τ zc r pq eps tubes := by
  intro μ hμ
  have hμ' := hμ.mono hττ' hrr'
  set H : ℝ → ℝ → ℂ := fun θ q => S (ellipse cT aT bT q) -
    (θ * hat μ (ellipse cT aT bT q) + (1 - θ) * hat ν (ellipse cT aT bT q)) with hH
  have hGν : ∀ q ∈ Icc (0 : ℝ) 1, G ν (ellipse cT aT bT q) ≠ 0 := by
    obtain ⟨L, _, hL, _⟩ := hwind
    intro q hq h0
    exact Complex.exp_ne_zero _ ((hL q hq).trans h0)
  by_cases hall : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1, H θ q ≠ 0
  · have hcont : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2) (Icc 0 1 ×ˢ Icc 0 1) := by
      apply Continuous.continuousOn
      have h1 : Continuous fun p : ℝ × ℝ => ellipse cT aT bT p.2 := (continuous_ellipse cT aT bT).comp continuous_snd
      have hμc := continuous_hat_of_classA hμ'.1.1
      have hνc := continuous_hat_of_classA hν.1.1
      exact (continuous_S.comp h1).sub (((Complex.continuous_ofReal.comp continuous_fst).mul (hμc.comp h1)).add
        ((continuous_const.sub (Complex.continuous_ofReal.comp continuous_fst)).mul (hνc.comp h1)))
    have hper : ∀ θ ∈ Icc (0 : ℝ) 1, H θ 0 = H θ 1 := fun θ _ => by simp only [hH, ellipse_zero_eq_one]
    have h0 : HasWinding (H 0) n := by
      have : H 0 = fun q => G ν (ellipse cT aT bT q) := by funext q; simp [hH, G]
      rw [this]; exact hwind
    have h1 := hasWinding_homotopy hcont hall hper h0
    refine ⟨cT, aT, bT, haT, hbT, fun q hq => ?_, n, hn, ?_⟩
    · have := hall 1 ⟨zero_le_one, le_rfl⟩ q hq; simpa [hH, G] using this
    · have : H 1 = fun q => G μ (ellipse cT aT bT q) := by funext q; simp [hH, G]
      rw [← this]; exact h1
  · push_neg at hall
    obtain ⟨θ, hθ, q, hq, hz⟩ := hall
    rcases htile q hq with hW1 | ⟨a, b, hqab, hchild⟩
    · exfalso
      have := hW1 μ ν hμ' hν (1 - θ) ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
      apply this
      simpa [hH, sub_sub_cancel, add_comm] using hz
    · set z := ellipse cT aT bT q
      have hθ0 : θ ≠ 0 := by
        intro h0
        rw [h0] at hz
        apply hGν q hq
        simpa [hH, G] using hz
      have hθC : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ0
      have hθpos : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθ0)
      refine hchild μ ⟨hμ.1, fun tb htb => ?_⟩
      rcases List.mem_append.1 htb with htb | htb
      · exact hμ.2 tb htb
      · simp only [List.mem_singleton] at htb
        subst htb
        refine ⟨q, hqab, (1 - θ) / θ, div_nonneg (by linarith [hθ.2]) hθpos.le, ?_⟩
        have hz' : S z - (θ * hat μ z + (1 - θ) * hat ν z) = 0 := hz
        have e0 : hat μ z - S z - (((1 - θ) / θ : ℝ) : ℂ) * (S z - hat ν z) = 0 := by
          push_cast
          field_simp
          linear_combination (-1 : ℂ) * hz'
        simp only [TubeR.pt]
        rw [e0, norm_zero]
        exact heps

/-! ### Splitting the arc of a tube (ivsplit) -/

theorem nodeSettled_ivsplit {τ r eps : ℝ} {zc : ℂ} {pq : List (ℂ × Box)} {tubes : List TubeR} {k : ℕ}
    {tb : TubeR} (hk : tubes[k]? = some tb) {qm : ℝ}
    (hlo : NodeSettled τ zc r pq eps (tubes.set k { tb with q1 := qm }))
    (hhi : NodeSettled τ zc r pq eps (tubes.set k { tb with q0 := qm })) :
    NodeSettled τ zc r pq eps tubes := by
  intro μ hμ
  have htb : tb ∈ tubes := List.mem_of_getElem? hk
  obtain ⟨q, hq, m, hm, hn⟩ := hμ.2 tb htb
  rcases le_total q qm with h | h
  · refine hlo μ ⟨hμ.1, fun x hx => ?_⟩
    rcases List.mem_or_eq_of_mem_set hx with hx | rfl
    · exact hμ.2 x hx
    · exact ⟨q, ⟨hq.1, h⟩, m, hm, hn⟩
  · refine hhi μ ⟨hμ.1, fun x hx => ?_⟩
    rcases List.mem_or_eq_of_mem_set hx with hx | rfl
    · exact hμ.2 x hx
    · exact ⟨q, ⟨h, hq.2⟩, m, hm, hn⟩

/-! ### Rooted arcs -/

theorem settled_N {τ c a b s₀ s₁ eps : ℝ} {zc : ℂ} {r : ℝ}
    (hloc : ∀ μ : Measure ℝ, ClassA τ μ → ∀ s ∈ Icc s₀ s₁, ∀ lam ∈ Ioc (0 : ℝ) 1,
      S (ellipse c a b s) = lam * hat μ (ellipse c a b s) → ∃ σ : ℝ, 1 ≤ σ ∧ ‖hat μ zc - (σ : ℂ) * S zc‖ ≤ r)
    (hcov : ∀ μ : Measure ℝ, ClassA τ μ → ∃ pq : List (ℂ × Box), (∀ x ∈ pq, x.2.mem (hat μ x.1)) ∧
      NodeSettled τ zc r pq eps []) :
    ArcSettled τ c a b s₀ s₁ := by
  intro μ hμ s hs lam hlam hcr
  obtain ⟨σ, hσ1, hσr⟩ := hloc μ hμ s hs lam hlam hcr
  obtain ⟨pq, hQ, hset⟩ := hcov μ hμ
  exact hset μ ⟨⟨hμ, ⟨σ, hσ1, hσr⟩, hQ⟩, fun tb htb => by simp at htb⟩

end C64
