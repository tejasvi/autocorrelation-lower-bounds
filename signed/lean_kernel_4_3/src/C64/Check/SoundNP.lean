import C64.Check.SoundNT
import C64.Check.SDerivN
import C64.Check.SoundWitL
import C64.Check.SoundH
import C64.Check.SettleN

/-!
# Soundness of the nested checker, part 2: pieces of tile arcs and of interval tubes

`piece3` (third-order bounds of `S` on the disc of a piece), the atom sums with derivatives (`sumK1`), the pieces of
a tube (`ivPiece`) and their sign and bound conditions (`ivOne` … `ivSum`), the pieces of a tube for the functions
of `t` (`tPiece`), and the data of a tube at a leaf (`tubeC`).
-/

namespace C64Chk

open Ival Ival.Ball C64Num Real

variable {P : ℕ}

/-! ### Global data -/

structure GlobNOK (gn : GlobN) : Prop where
  g : GlobOK gn.g
  epsd : 0 < gn.eps.d
  epsn : 0 ≤ gn.eps.n
  hS : gn.g.EQ + gn.lS + gn.dS + 1 ≤ gn.g.P
  hT : gn.g.EQ + gn.lT + gn.nL ≤ gn.g.P

theorem checkGlobN_ok {gn : GlobN} (h : checkGlobN gn = true) :
    GlobNOK gn ∧ windOdd gn.g (T1B gn.g) [] 0 = true := by
  unfold checkGlobN globParamsN at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hp, hd⟩, hn⟩, -⟩, hS⟩, hT⟩, hw⟩ := h
  have hg : checkGlob gn.g = true := by unfold checkGlob; simp [hp, hw]
  exact ⟨⟨(checkGlob_ok hg).1, hd, hn, hS, hT⟩, hw⟩

theorem eps_nonneg {gn : GlobN} (hgn : GlobNOK gn) : 0 ≤ gn.eps.val := by
  unfold Q.val; exact div_nonneg (by exact_mod_cast hgn.epsn) (by positivity)

theorem eps_le_epsHi {gn : GlobN} (hgn : GlobNOK gn) : gn.eps.val ≤ (epsHi gn : ℝ) / 2 ^ gn.g.P := by
  have hP := two_pow_pos' gn.g.P
  have hd : (0 : ℝ) < gn.eps.d := by exact_mod_cast hgn.epsd
  have hc := cdiv_spec (gn.eps.n.toNat * 2 ^ gn.g.P) gn.eps.d hgn.epsd
  have e : ((gn.eps.n.toNat : ℕ) : ℝ) = (gn.eps.n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hgn.epsn
  push_cast at hc; rw [e] at hc
  unfold epsHi Q.val
  rw [le_div_iff₀ hP]
  calc (gn.eps.n : ℝ) / gn.eps.d * 2 ^ gn.g.P = (gn.eps.n : ℝ) * 2 ^ gn.g.P / gn.eps.d := by ring
    _ ≤ _ := hc

theorem epsLo_le {gn : GlobN} (hgn : GlobNOK gn) : (epsLo gn : ℝ) / 2 ^ gn.g.P ≤ gn.eps.val := by
  have hP := two_pow_pos' gn.g.P
  have hd : (0 : ℝ) < gn.eps.d := by exact_mod_cast hgn.epsd
  have e : ((gn.eps.n.toNat : ℕ) : ℝ) = (gn.eps.n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hgn.epsn
  have h1 : ((gn.eps.n.toNat * 2 ^ gn.g.P / gn.eps.d : ℕ) : ℝ) ≤ ((gn.eps.n.toNat * 2 ^ gn.g.P : ℕ) : ℝ) / gn.eps.d :=
    Nat.cast_div_le
  push_cast at h1; rw [e] at h1
  unfold epsLo Q.val
  rw [div_le_iff₀ hP]
  calc ((gn.eps.n.toNat * 2 ^ gn.g.P / gn.eps.d : ℕ) : ℝ) ≤ (gn.eps.n : ℝ) * 2 ^ gn.g.P / gn.eps.d := h1
    _ = (gn.eps.n : ℝ) / gn.eps.d * 2 ^ gn.g.P := by ring

/-! ### Tiles and tubes -/

/-- The tile `i` as reals: centre, `a`, `b`. -/
noncomputable def tileR (g : Glob) (i : ℕ) : ℂ × ℝ × ℝ :=
  match g.tiles[i]? with
  | some t => (⟨t.1.val, t.2.1.val⟩, t.2.2.1.val, t.2.2.2.val)
  | none => (0, 1, 1)

theorem tileOf_okR {g : Glob} (hg : GlobOK g) {i : ℕ} {E : EllB} (h : tileOf g i = some E) :
    0 < (tileR g i).2.1 ∧ 0 < (tileR g i).2.2 ∧ EllOK g.P (tileR g i).1 (tileR g i).2.1 (tileR g i).2.2 E := by
  unfold tileOf at h
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
  have hmem : t ∈ g.tiles := List.mem_of_getElem? ht
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hg.tiles t hmem
  simp only [tileR, ht]
  refine ⟨?_, ?_, ⟨mem_Qball h1, mem_Qball h2, mem_Qball h3, mem_Qball h4⟩⟩
  · unfold Q.val; exact div_pos (by exact_mod_cast h5) (by exact_mod_cast h3)
  · unfold Q.val; exact div_pos (by exact_mod_cast h6) (by exact_mod_cast h4)

/-- The semantic tube of a tube of the checker. -/
noncomputable def tubeR (g : Glob) (tb : TubeD) : C64.TubeR :=
  ⟨(tileR g tb.ti).1, (tileR g tb.ti).2.1, (tileR g tb.ti).2.2, (tb.q0 : ℝ) / 2 ^ g.EQ, (tb.q1 : ℝ) / 2 ^ g.EQ,
    wsum tb.as⟩

/-! ### `S`, `S'`, `S''` at a point -/

theorem memC_cSS2 {c : Cfg} {z : ℂ} {a : CBall} {w w1 w2 : CBall} (hz : memC c.P z a)
    (h : cSS2 c a = some (w, w1, w2)) :
    z ≠ 0 ∧ memC c.P (C64.S z) w ∧ memC c.P (C64.S1 z) w1 ∧ memC c.P (C64.S2 z) w2 := by
  unfold cSS2 at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨co, si⟩, hcs, s, hs, s1, hs1, s2, hs2, rfl, rfl, rfl⟩ := h
  obtain ⟨hco, hsi⟩ := memC_ccosSinPi hz hcs
  obtain ⟨hpz, hw⟩ := cdiv_sound hsi (memC_piz hz) hs
  have hz0 : z ≠ 0 := by intro h0; apply hpz; rw [h0, mul_zero]
  refine ⟨hz0, ?_, ?_, ?_⟩
  · simp only [C64.S, hz0, ↓reduceIte]; exact hw
  · have hnum := CBall.memC_sub (CBall.memC_mul (memC_piz hz) hco) hsi
    have hden := CBall.memC_mul (memC_piz hz) hz
    obtain ⟨_, hw1⟩ := cdiv_sound hnum hden hs1
    rw [C64.S1_eq hz0]
    convert hw1 using 2
    ring
  · have h2 : memC c.P (2 : ℂ) ⟨Ball.ofInt c.P 2, ⟨0, 0⟩⟩ := by
      have := mem_ofInt c.P 2
      exact ⟨by simpa using this, by simpa using mem_zero_ball (P := c.P)⟩
    have hnum := CBall.memC_sub (CBall.memC_mul (CBall.memC_sub h2 (CBall.memC_mul (memC_piz hz) (memC_piz hz))) hsi)
      (CBall.memC_mul (CBall.memC_add (memC_piz hz) (memC_piz hz)) hco)
    have hden := CBall.memC_mul (memC_piz hz) (CBall.memC_mul hz hz)
    obtain ⟨_, hw2⟩ := cdiv_sound hnum hden hs2
    rw [C64.S2_eq hz0]
    convert hw2 using 2 <;> ring

/-! ### Pieces with third-order bounds -/

/-- `|S''(z)| ρ²/2 + (π³/3) e^{π Y} ρ³/6 ≤ d23`. -/
theorem d23_ok {s2 : CBall} {w : ℂ} (hs2 : memC P w s2) {rho eY : ℕ} {Y : ℝ}
    (heY : Real.exp (π * Y) ≤ (eY : ℝ) / 2 ^ P) :
    ‖w‖ * ((rho : ℝ) / 2 ^ P) ^ 2 / 2 + π ^ 3 / 3 * Real.exp (π * Y) * ((rho : ℝ) / 2 ^ P) ^ 3 / 6 ≤
      (d23 P s2 rho eY : ℝ) / 2 ^ P := by
  have hP := two_pow_pos' P
  have hw := norm_le_normHi hs2
  have hpi := pi_le_piHi (P := P)
  unfold d23
  push_cast
  rw [add_div]
  refine add_le_add ?_ ?_
  · have hc := cdiv_spec (normHi s2 * rho * rho) (2 * 2 ^ (2 * P)) (by positivity)
    push_cast at hc
    calc ‖w‖ * ((rho : ℝ) / 2 ^ P) ^ 2 / 2 ≤ ((normHi s2 : ℝ) / 2 ^ P) * ((rho : ℝ) / 2 ^ P) ^ 2 / 2 := by gcongr
      _ = ((normHi s2 : ℝ) * rho * rho / (2 * 2 ^ (2 * P))) / 2 ^ P := by
        rw [show (2 : ℝ) ^ (2 * P) = 2 ^ P * 2 ^ P by rw [two_mul, pow_add]]; field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hc hP.le
  · have hc := cdiv_spec (piHi P ^ 3 * eY * rho ^ 3) (18 * 2 ^ (6 * P)) (by positivity)
    push_cast at hc
    have hpi0 : 0 ≤ π := Real.pi_pos.le
    calc π ^ 3 / 3 * Real.exp (π * Y) * ((rho : ℝ) / 2 ^ P) ^ 3 / 6
        ≤ ((piHi P : ℝ) / 2 ^ P) ^ 3 / 3 * ((eY : ℝ) / 2 ^ P) * ((rho : ℝ) / 2 ^ P) ^ 3 / 6 := by gcongr
      _ = ((piHi P : ℝ) ^ 3 * eY * rho ^ 3 / (18 * 2 ^ (6 * P))) / 2 ^ P := by
        rw [show (2 : ℝ) ^ (6 * P) = (2 ^ P) ^ 6 by rw [← pow_mul, mul_comm]]; field_simp; ring
      _ ≤ _ := div_le_div_of_nonneg_right hc hP.le

/-- Semantics of a piece: the midpoint value `zm`, the arc of the piece in the disc, `S`, `S'`, `S''` at `zm`,
`|Im| ≤ Y` and `e^{π Y} ≤ eY` with `Y = (|Im z|⁺ + ρ)`, and the variation bound `dS`. -/
structure Piece3OK (P : ℕ) (zm : ℂ) (p : Piece3) : Prop where
  z : memC P zm p.z
  sz : memC P (C64.S zm) p.sz
  s1 : memC P (C64.S1 zm) p.s1
  s2 : memC P (C64.S2 zm) p.s2
  im : ∀ w, ‖w - zm‖ ≤ (p.rho : ℝ) / 2 ^ P → |w.im| ≤ ((p.z.im.absHi + p.rho : ℕ) : ℝ) / 2 ^ P
  eY : Real.exp (π * (((p.z.im.absHi + p.rho : ℕ) : ℝ) / 2 ^ P)) ≤ (p.eY : ℝ) / 2 ^ P
  dS : ∀ ζ, ‖ζ - zm‖ ≤ (p.rho : ℝ) / 2 ^ P → ‖C64.S ζ - C64.S zm‖ ≤ (p.dS : ℝ) / 2 ^ P

theorem piece3_ok {c : Cfg} {cc : ℂ} {a b : ℝ} {E : EllB} (hE : EllOK c.P cc a b E) {n0 n1 e : ℕ} {p : Piece3}
    (h01 : n0 ≤ n1) (he : e + 1 ≤ c.P) (h : piece3 c E n0 n1 e = some p) :
    Piece3OK c.P (C64.ellipse cc a b (((n0 : ℝ) + n1) / 2 ^ (e + 1))) p ∧
    ∀ q ∈ Set.Icc ((n0 : ℝ) / 2 ^ e) ((n1 : ℝ) / 2 ^ e),
      ‖C64.ellipse cc a b q - C64.ellipse cc a b (((n0 : ℝ) + n1) / 2 ^ (e + 1))‖ ≤ (p.rho : ℝ) / 2 ^ c.P := by
  unfold piece3 at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨z, hz, ρ, hρ, ⟨sz, s1, s2⟩, hss, eY, heY, rfl⟩ := h
  have hzm := memC_ellPt hE (mem_midB he) hz
  obtain ⟨-, hsz, hs1, hs2⟩ := memC_cSS2 hzm hss
  have hP := two_pow_pos' c.P
  set zm := C64.ellipse cc a b (((n0 : ℝ) + n1) / 2 ^ (e + 1))
  have him : ∀ w, ‖w - zm‖ ≤ (ρ : ℝ) / 2 ^ c.P → |w.im| ≤ ((z.im.absHi + ρ : ℕ) : ℝ) / 2 ^ c.P := fun w hw =>
    im_le_of_disc hzm ρ w (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hw)
  have heY' := exp_le_expPiHi heY (le_refl (((z.im.absHi + ρ : ℕ) : ℝ) / 2 ^ c.P))
  refine ⟨⟨hzm, hsz, hs1, hs2, him, ?_, ?_⟩, fun q hq => ellRad_sound hE h01 he hρ hq⟩
  · simpa using heY'
  · intro ζ hζ
    have hC := C64.norm_S3_le_disc (z₀ := zm) (ρ := (ρ : ℝ) / 2 ^ c.P) him
    have h3 := C64.norm_sub_S_le3 hζ hC
    have h1 : ‖C64.S1 zm‖ * ((ρ : ℝ) / 2 ^ c.P) ≤ (mulU c.P (normHi s1) ρ : ℝ) / 2 ^ c.P :=
      mulU_le (norm_nonneg _) (by positivity) (norm_le_normHi hs1) le_rfl
    have h2 := d23_ok (P := c.P) hs2 (rho := ρ) heY'
    push_cast
    rw [add_div]
    linarith

/-! ### Atom sums with derivatives -/

theorem sumK1_ok {c : Cfg} {z : ℂ} {zb : CBall} (hz : memC c.P z zb) : ∀ (as : List (Q × Q)) {w : CBall × CBall},
    (∀ a ∈ as, 0 < a.1.d ∧ 0 < a.2.d) → sumK1 c zb as = some w →
    memC c.P (wsum as z) w.1 ∧ memC c.P (wsum1 as z) w.2
  | [], w, _, h => by
    simp only [sumK1, Option.some.injEq] at h; subst h
    exact ⟨⟨by simp [wsum, mem], by simp [wsum, mem]⟩, ⟨by simp [wsum1, mem], by simp [wsum1, mem]⟩⟩
  | (t, m) :: as, w, hd, h => by
    unfold sumK1 at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, s, hs, rfl⟩ := h
    have hd0 := hd (t, m) (by simp)
    have hK := memC_ckt (mem_Qball hd0.1) hz hk
    obtain ⟨hS0, hS1⟩ := sumK1_ok hz as (fun a ha => hd a (by simp [ha])) hs
    have hmk := C64Num.CBall.memC_mulR (mem_Qball hd0.2) hK
    have htp : mem c.P (2 * (π * t.val)) (Ball.mulInt 2 (Ball.mul c.P (piB c.P) (t.ball c.P))) := by
      have := mem_mulInt 2 (mem_mul (mem_piB c.P) (mem_Qball (P := c.P) hd0.1)); simpa using this
    refine ⟨?_, ?_⟩
    · have := C64Num.CBall.memC_add hmk hS0
      simpa [wsum] using this
    · have hd1 : memC c.P ((m.val : ℂ) * ((-2 * π * Complex.I * t.val) * C64.Kt t.val z))
          ⟨Ball.mul c.P (Ball.mulInt 2 (Ball.mul c.P (piB c.P) (t.ball c.P))) (CBall.mulR c.P (m.ball c.P) k).im,
           Ball.neg (Ball.mul c.P (Ball.mulInt 2 (Ball.mul c.P (piB c.P) (t.ball c.P)))
             (CBall.mulR c.P (m.ball c.P) k).re)⟩ := by
        refine ⟨?_, ?_⟩
        · have := mem_mul htp hmk.2
          convert this using 1
          simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
            Complex.I_im]
          norm_num
          try ring
        · have := mem_neg (mem_mul htp hmk.1)
          convert this using 1
          simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
            Complex.I_im]
          norm_num
          try ring
      have := C64Num.CBall.memC_add hd1 hS1
      simpa [wsum1] using this

/-! ### Pieces of a tube -/

/-- Semantics of a piece of a tube: at every point of its arc, `S` and `G = S - w₀` at a point `zm` with the variation
bounds. -/
def IvPOK (P : ℕ) (cT : ℂ) (aT bT : ℝ) (as : List (Q × Q)) (p : IvP) : Prop :=
  ∀ q ∈ Set.Icc ((p.n0 : ℝ) / 2 ^ p.e) ((p.n1 : ℝ) / 2 ^ p.e), ∃ zm : ℂ,
    memC P (C64.S zm) p.sz ∧ memC P (C64.S zm - wsum as zm) p.gz ∧
    ‖C64.S (C64.ellipse cT aT bT q) - C64.S zm‖ ≤ (p.dS : ℝ) / 2 ^ P ∧
    ‖(C64.S (C64.ellipse cT aT bT q) - wsum as (C64.ellipse cT aT bT q)) - (C64.S zm - wsum as zm)‖ ≤
      (p.dG : ℝ) / 2 ^ P

theorem ivPiece_ok {c : Cfg} {cT : ℂ} {aT bT : ℝ} {E : EllB} (hE : EllOK c.P cT aT bT E) {as : List (Q × Q)}
    (hA : AtomsOK as) {mSum : ℕ} (hmS : msum as ≤ (mSum : ℝ) / 2 ^ c.P) {n0 n1 e : ℕ} {p : IvP}
    (h01 : n0 ≤ n1) (he : e + 1 ≤ c.P) (h : ivPiece c E as mSum n0 n1 e = some p) :
    p.n0 = n0 ∧ p.n1 = n1 ∧ p.e = e ∧ IvPOK c.P cT aT bT as p := by
  unfold ivPiece at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨p3, hp3, w, hw, rfl⟩ := h
  obtain ⟨hok, hrad⟩ := piece3_ok hE h01 he hp3
  refine ⟨rfl, rfl, rfl, fun q hq => ?_⟩
  set zm := C64.ellipse cT aT bT (((n0 : ℝ) + n1) / 2 ^ (e + 1))
  have hP := two_pow_pos' c.P
  obtain ⟨hw0, hw1⟩ := sumK1_ok hok.z as (fun a ha => ⟨(hA a ha).1, (hA a ha).2.2.1⟩) hw
  have hq' := hrad q hq
  refine ⟨zm, hok.sz, C64Num.CBall.memC_sub hok.sz hw0, hok.dS _ hq', ?_⟩
  set Y : ℝ := ((p3.z.im.absHi + p3.rho : ℕ) : ℝ) / 2 ^ c.P
  have hC := C64.norm_S3_le_disc (z₀ := zm) (ρ := (p3.rho : ℝ) / 2 ^ c.P) hok.im
  have hG := norm_sub_G_le hA hq' hC hok.im
  have h1 : ‖C64.S1 zm - wsum1 as zm‖ * ((p3.rho : ℝ) / 2 ^ c.P) ≤
      (mulU c.P (normHi (CBall.sub p3.s1 w.2)) p3.rho : ℝ) / 2 ^ c.P :=
    mulU_le (norm_nonneg _) (by positivity) (norm_le_normHi (C64Num.CBall.memC_sub hok.s1 hw1)) le_rfl
  have h2 := d23_ok (P := c.P) hok.s2 (rho := p3.rho) hok.eY
  have hm0 : 0 ≤ msum as := by
    unfold msum; exact List.sum_nonneg (fun x hx => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx; exact (hA a ha).2.2.2)
  have hpi := pi_le_piHi (P := c.P)
  have h3 : msum as * (π ^ 2 * Real.exp (π * Y)) * ((p3.rho : ℝ) / 2 ^ c.P) ^ 2 / 2 ≤
      (Ball.cdiv (mSum * piHi c.P ^ 2 * p3.eY * p3.rho * p3.rho) (2 * 2 ^ (5 * c.P)) : ℝ) / 2 ^ c.P := by
    have hc := cdiv_spec (mSum * piHi c.P ^ 2 * p3.eY * p3.rho * p3.rho) (2 * 2 ^ (5 * c.P)) (by positivity)
    push_cast at hc
    calc msum as * (π ^ 2 * Real.exp (π * Y)) * ((p3.rho : ℝ) / 2 ^ c.P) ^ 2 / 2
        ≤ ((mSum : ℝ) / 2 ^ c.P) * (((piHi c.P : ℝ) / 2 ^ c.P) ^ 2 * ((p3.eY : ℝ) / 2 ^ c.P)) *
            ((p3.rho : ℝ) / 2 ^ c.P) ^ 2 / 2 := by
          gcongr
          exact hok.eY
      _ = ((mSum : ℝ) * piHi c.P ^ 2 * p3.eY * p3.rho * p3.rho / (2 * 2 ^ (5 * c.P))) / 2 ^ c.P := by
          rw [show (2 : ℝ) ^ (5 * c.P) = (2 ^ c.P) ^ 5 by rw [← pow_mul, mul_comm]]; field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hc hP.le
  simp only
  push_cast
  rw [add_div, add_div]
  nlinarith [hG, h1, h2, h3]

/-! ### Sign and bound conditions of a tube -/

/-- The condition at the parameter `q` with the multiplier `v` and the bound `b`: `neg = true` (W1)
`Re(v̄ G) ≤ 0`, `Re(v̄ S) ≤ b`; `neg = false` (empty) `Re(v̄ G) ≥ 0`, `Re(v̄ S) ≥ b`. -/
def IvCond (neg : Bool) (cT : ℂ) (aT bT : ℝ) (as : List (Q × Q)) (v : ℂ) (b : ℝ) (q : ℝ) : Prop :=
  if neg then ((starRingEnd ℂ) v * (C64.S (C64.ellipse cT aT bT q) - wsum as (C64.ellipse cT aT bT q))).re ≤ 0 ∧
      ((starRingEnd ℂ) v * C64.S (C64.ellipse cT aT bT q)).re ≤ b
  else 0 ≤ ((starRingEnd ℂ) v * (C64.S (C64.ellipse cT aT bT q) - wsum as (C64.ellipse cT aT bT q))).re ∧
      b ≤ ((starRingEnd ℂ) v * C64.S (C64.ellipse cT aT bT q)).re

theorem IvCond.comb {neg : Bool} {cT : ℂ} {aT bT : ℝ} {as : List (Q × Q)} {v : ℂ} {q : ℝ} {b1 : ℤ}
    (h : IvCond neg cT aT bT as v ((b1 : ℝ) / 2 ^ P) q) (b2 : ℤ) :
    IvCond neg cT aT bT as v ((comb neg b1 b2 : ℝ) / 2 ^ P) q ∧ IvCond neg cT aT bT as v ((comb neg b2 b1 : ℝ) / 2 ^ P) q := by
  have hP := two_pow_pos' P
  cases neg
  · simp only [IvCond, Bool.false_eq_true, ↓reduceIte] at h ⊢
    refine ⟨⟨h.1, le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_left _ _) hP.le) h.2⟩,
      ⟨h.1, le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_right _ _) hP.le) h.2⟩⟩
  · simp only [IvCond, ↓reduceIte] at h ⊢
    refine ⟨⟨h.1, le_trans h.2 (div_le_div_of_nonneg_right (by exact_mod_cast le_max_left _ _) hP.le)⟩,
      ⟨h.1, le_trans h.2 (div_le_div_of_nonneg_right (by exact_mod_cast le_max_right _ _) hP.le)⟩⟩

theorem ivOne_ok {neg : Bool} {vt : CBall} {v : ℂ} (hv : memC P v vt) {p : IvP} {cT : ℂ} {aT bT : ℝ}
    {as : List (Q × Q)} (hp : IvPOK P cT aT bT as p) {b : ℤ} (h : ivOne P neg vt p = some b) :
    ∀ q ∈ Set.Icc ((p.n0 : ℝ) / 2 ^ p.e) ((p.n1 : ℝ) / 2 ^ p.e), IvCond neg cT aT bT as v ((b : ℝ) / 2 ^ P) q := by
  intro q hq
  obtain ⟨zm, hsz, hgz, hdS, hdG⟩ := hp q hq
  have hP := two_pow_pos' P
  set z := C64.ellipse cT aT bT q
  have hn := norm_le_normHi hv
  have hvS : ‖v‖ * ‖C64.S z - C64.S zm‖ ≤ (mulU P (normHi vt) p.dS : ℝ) / 2 ^ P :=
    mulU_le (norm_nonneg _) (norm_nonneg _) hn hdS
  have hvG : ‖v‖ * ‖(C64.S z - wsum as z) - (C64.S zm - wsum as zm)‖ ≤ (mulU P (normHi vt) p.dG : ℝ) / 2 ^ P :=
    mulU_le (norm_nonneg _) (norm_nonneg _) hn hdG
  have bnd : ∀ x y : ℂ, |((starRingEnd ℂ) v * x).re - ((starRingEnd ℂ) v * y).re| ≤ ‖v‖ * ‖x - y‖ := by
    intro x y
    rw [← Complex.sub_re, ← mul_sub]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
  have bS := abs_le.1 (bnd (C64.S z) (C64.S zm))
  have bG := abs_le.1 (bnd (C64.S z - wsum as z) (C64.S zm - wsum as zm))
  obtain ⟨gLo, gHi⟩ := reConj_bounds hv hgz
  obtain ⟨sLo, sHi⟩ := reConj_bounds hv hsz
  unfold ivOne at h
  cases neg
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    simp only [IvCond, Bool.false_eq_true, ↓reduceIte]
    have hc' : (0 : ℝ) ≤ ((reConjLo P vt p.gz - (mulU P (normHi vt) p.dG : ℕ) : ℤ) : ℝ) := by exact_mod_cast hc
    push_cast at hc' ⊢
    constructor
    · have : (0 : ℝ) ≤ (reConjLo P vt p.gz : ℝ) / 2 ^ P - (mulU P (normHi vt) p.dG : ℝ) / 2 ^ P := by
        rw [← sub_div]; exact div_nonneg hc' hP.le
      linarith
    · rw [sub_div]; linarith
  · simp only [↓reduceIte] at h
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    simp only [IvCond, ↓reduceIte]
    have hc' : ((reConjHi P vt p.gz + (mulU P (normHi vt) p.dG : ℕ) : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hc
    push_cast at hc' ⊢
    constructor
    · have : (reConjHi P vt p.gz : ℝ) / 2 ^ P + (mulU P (normHi vt) p.dG : ℝ) / 2 ^ P ≤ 0 := by
        rw [← add_div]; exact div_nonpos_of_nonpos_of_nonneg hc' hP.le
      linarith
    · rw [add_div]; linarith

/-- Bisection of a piece. -/
theorem ivRec_ok {c : Cfg} {cT : ℂ} {aT bT : ℝ} {E : EllB} (hE : EllOK c.P cT aT bT E) {as : List (Q × Q)}
    (hA : AtomsOK as) {mSum : ℕ} (hmS : msum as ≤ (mSum : ℝ) / 2 ^ c.P) {neg : Bool} {vt : CBall} {v : ℂ}
    (hv : memC c.P v vt) :
    ∀ (fuel n0 n1 e : ℕ) {b : ℤ}, n0 ≤ n1 → e + fuel + 1 ≤ c.P →
      ivRec c E as mSum neg vt fuel n0 n1 e = some b →
      ∀ q ∈ Set.Icc ((n0 : ℝ) / 2 ^ e) ((n1 : ℝ) / 2 ^ e), IvCond neg cT aT bT as v ((b : ℝ) / 2 ^ c.P) q
  | 0, n0, n1, e, b, h01, he, h => by
    unfold ivRec at h
    obtain ⟨p, hp, hb⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e1, e2, e3, hok⟩ := ivPiece_ok hE hA hmS h01 (by omega) hp
    have := ivOne_ok hv hok hb
    rw [e1, e2, e3] at this; exact this
  | fuel + 1, n0, n1, e, b, h01, he, h => by
    unfold ivRec at h
    rcases hfirst : (ivPiece c E as mSum n0 n1 e).bind (ivOne c.P neg vt) with _ | b0
    · rw [hfirst] at h
      simp only [Option.orElse_none, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b1, hb1, b2, hb2, rfl⟩ := h
      intro s hs
      have hm : ((n0 + n1 : ℕ) : ℝ) / 2 ^ (e + 1) = ((n0 : ℝ) + n1) / 2 ^ (e + 1) := by push_cast; ring
      rcases le_total s (((n0 : ℝ) + n1) / 2 ^ (e + 1)) with hsm | hsm
      · refine (IvCond.comb (ivRec_ok hE hA hmS hv fuel (2 * n0) (n0 + n1) (e + 1) (by omega) (by omega) hb1 s
          ⟨?_, ?_⟩) b2).1
        · push_cast; rw [pow_succ]
          have := hs.1; rw [show (2 * (n0 : ℝ)) / (2 ^ e * 2) = (n0 : ℝ) / 2 ^ e by field_simp]; exact this
        · rw [hm]; exact hsm
      · refine (IvCond.comb (ivRec_ok hE hA hmS hv fuel (n0 + n1) (2 * n1) (e + 1) (by omega) (by omega) hb2 s
          ⟨?_, ?_⟩) b1).2
        · rw [hm]; exact hsm
        · push_cast; rw [pow_succ]
          have := hs.2; rw [show (2 * (n1 : ℝ)) / (2 ^ e * 2) = (n1 : ℝ) / 2 ^ e by field_simp]; exact this
    · rw [hfirst] at h
      simp only [Option.orElse_some, Option.some.injEq] at h
      subst h
      obtain ⟨p, hp, hb⟩ := Option.bind_eq_some_iff.1 hfirst
      obtain ⟨e1, e2, e3, hok⟩ := ivPiece_ok hE hA hmS h01 (by omega) hp
      have := ivOne_ok hv hok hb
      rw [e1, e2, e3] at this; exact this

theorem ivTry_ok {c : Cfg} {cT : ℂ} {aT bT : ℝ} {E : EllB} (hE : EllOK c.P cT aT bT E) {as : List (Q × Q)}
    (hA : AtomsOK as) {mSum : ℕ} (hmS : msum as ≤ (mSum : ℝ) / 2 ^ c.P) {neg : Bool} {vt : CBall} {v : ℂ}
    (hv : memC c.P v vt) {dS : ℕ} {p : IvP} (hp : IvPOK c.P cT aT bT as p) (h01 : p.n0 ≤ p.n1)
    (he : p.e + dS + 1 ≤ c.P) {b : ℤ} (h : ivTry c E as mSum neg vt dS p = some b) :
    ∀ q ∈ Set.Icc ((p.n0 : ℝ) / 2 ^ p.e) ((p.n1 : ℝ) / 2 ^ p.e), IvCond neg cT aT bT as v ((b : ℝ) / 2 ^ c.P) q := by
  unfold ivTry at h
  rcases hfirst : ivOne c.P neg vt p with _ | b0
  · rw [hfirst] at h
    simp only [Option.orElse_none] at h
    cases dS with
    | zero => simp at h
    | succ d =>
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b1, hb1, b2, hb2, rfl⟩ := h
      intro s hs
      have hm : ((p.n0 + p.n1 : ℕ) : ℝ) / 2 ^ (p.e + 1) = ((p.n0 : ℝ) + p.n1) / 2 ^ (p.e + 1) := by push_cast; ring
      rcases le_total s (((p.n0 : ℝ) + p.n1) / 2 ^ (p.e + 1)) with hsm | hsm
      · refine (IvCond.comb (ivRec_ok hE hA hmS hv d (2 * p.n0) (p.n0 + p.n1) (p.e + 1) (by omega) (by omega)
          hb1 s ⟨?_, ?_⟩) b2).1
        · push_cast; rw [pow_succ]
          have := hs.1; rw [show (2 * (p.n0 : ℝ)) / (2 ^ p.e * 2) = (p.n0 : ℝ) / 2 ^ p.e by field_simp]; exact this
        · rw [hm]; exact hsm
      · refine (IvCond.comb (ivRec_ok hE hA hmS hv d (p.n0 + p.n1) (2 * p.n1) (p.e + 1) (by omega) (by omega)
          hb2 s ⟨?_, ?_⟩) b1).2
        · rw [hm]; exact hsm
        · push_cast; rw [pow_succ]
          have := hs.2; rw [show (2 * (p.n1 : ℝ)) / (2 ^ p.e * 2) = (p.n1 : ℝ) / 2 ^ p.e by field_simp]; exact this
  · rw [hfirst] at h
    simp only [Option.orElse_some, Option.some.injEq] at h
    subst h
    exact ivOne_ok hv hp hfirst

theorem ivAll_ok {c : Cfg} {cT : ℂ} {aT bT : ℝ} {E : EllB} (hE : EllOK c.P cT aT bT E) {as : List (Q × Q)}
    (hA : AtomsOK as) {mSum : ℕ} (hmS : msum as ≤ (mSum : ℝ) / 2 ^ c.P) {neg : Bool} {vt : CBall} {v : ℂ}
    (hv : memC c.P v vt) {dS : ℕ} :
    ∀ (ps : List IvP) {b : ℤ}, (∀ p ∈ ps, IvPOK c.P cT aT bT as p ∧ p.n0 ≤ p.n1 ∧ p.e + dS + 1 ≤ c.P) →
      ivAll c E as mSum neg vt dS ps = some b →
      ∀ p ∈ ps, ∀ q ∈ Set.Icc ((p.n0 : ℝ) / 2 ^ p.e) ((p.n1 : ℝ) / 2 ^ p.e),
        IvCond neg cT aT bT as v ((b : ℝ) / 2 ^ c.P) q
  | [], _, _, h => by simp [ivAll] at h
  | [p], b, hok, h => by
    unfold ivAll at h
    intro p' hp'
    simp only [List.mem_singleton] at hp'
    subst hp'
    obtain ⟨h1, h2, h3⟩ := hok p' (by simp)
    exact ivTry_ok hE hA hmS hv h1 h2 h3 h
  | p :: p2 :: ps, b, hok, h => by
    unfold ivAll at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨b0, hb0, b1, hb1, rfl⟩ := h
    intro p' hp' q hq
    simp only [List.mem_cons] at hp'
    rcases hp' with rfl | hp'
    · obtain ⟨h1, h2, h3⟩ := hok p' (by simp)
      exact (IvCond.comb (ivTry_ok hE hA hmS hv h1 h2 h3 hb0 q hq) b1).1
    · have := ivAll_ok hE hA hmS hv (p2 :: ps) (fun x hx => hok x (List.mem_cons_of_mem _ hx)) hb1 p'
        (by simpa using hp') q hq
      exact (IvCond.comb this b0).2

/-! ### Covering an arc by equal pieces -/

theorem forall2_range_getD {β : Type} {R : ℕ → β → Prop} {d : β} {n : ℕ} {ts : List β}
    (h : List.Forall₂ R (List.range n) ts) {l : ℕ} (hl : l < n) : R l (ts.getD l d) := by
  rw [List.forall₂_iff_get] at h
  obtain ⟨hlen, hR⟩ := h
  have hl' : l < ts.length := by rw [← hlen, List.length_range]; exact hl
  have := hR l (by rw [List.length_range]; exact hl) hl'
  simp only [List.get_eq_getElem, List.getElem_range] at this
  rw [List.getD_eq_getElem _ _ hl']
  exact this

theorem forall2_left_mem {α β : Type} {R : α → β → Prop} : ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 →
    ∀ a ∈ l1, ∃ b ∈ l2, R a b
  | _, _, .nil => by simp
  | _, _, .cons h hs => by
    intro a ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨b, hb, hr⟩ := forall2_left_mem hs a ha; exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

theorem forall2_right_mem {α β : Type} {R : α → β → Prop} : ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 →
    ∀ b ∈ l2, ∃ a ∈ l1, R a b
  | _, _, .nil => by simp
  | _, _, .cons h hs => by
    intro b hb
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨a, ha, hr⟩ := forall2_right_mem hs b hb; exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

theorem subPc_cover {q0 q1 E l : ℕ} {q : ℝ}
    (hq : q ∈ Set.Icc ((q0 : ℝ) / 2 ^ E) ((q1 : ℝ) / 2 ^ E)) :
    ∃ i < 2 ^ l, q ∈ Set.Icc (((subPc q0 q1 l i).1 : ℝ) / 2 ^ (E + l)) (((subPc q0 q1 l i).2 : ℝ) / 2 ^ (E + l)) := by
  have hE := two_pow_pos' E
  have h01 : q0 ≤ q1 := by
    have h1 : (q0 : ℝ) / 2 ^ E ≤ (q1 : ℝ) / 2 ^ E := le_trans hq.1 hq.2
    have : (q0 : ℝ) ≤ q1 := by rwa [div_le_div_iff_of_pos_right hE] at h1
    exact_mod_cast this
  have hL : (0 : ℝ) < 2 ^ l := by positivity
  set δ : ℝ := ((q1 : ℝ) - q0) / 2 ^ (E + l) with hδ
  have hsub : ((q1 - q0 : ℕ) : ℝ) = (q1 : ℝ) - q0 := by push_cast [Nat.cast_sub h01]; ring
  have hpt : ∀ i : ℕ, ((subPc q0 q1 l i).1 : ℝ) / 2 ^ (E + l) = (q0 : ℝ) / 2 ^ E + i * δ ∧
      ((subPc q0 q1 l i).2 : ℝ) / 2 ^ (E + l) = (q0 : ℝ) / 2 ^ E + (i + 1) * δ := by
    intro i
    simp only [subPc]
    push_cast
    rw [hsub, hδ, pow_add]
    constructor <;> field_simp <;> ring
  rcases eq_or_lt_of_le h01 with heq | hlt
  · refine ⟨0, by positivity, ?_⟩
    rw [(hpt 0).1, (hpt 0).2]
    have : δ = 0 := by rw [hδ, heq, sub_self, zero_div]
    rw [this]; simp only [mul_zero, add_zero]
    have := hq.1; have := hq.2; rw [heq] at *; constructor <;> linarith
  · have hδ0 : 0 < δ := by
      rw [hδ]; apply div_pos _ (by positivity); have : (q0 : ℝ) < q1 := by exact_mod_cast hlt
      linarith
    set x := (q - (q0 : ℝ) / 2 ^ E) / δ with hx
    have hx0 : 0 ≤ x := div_nonneg (by linarith [hq.1]) hδ0.le
    have hxL : x ≤ 2 ^ l := by
      rw [hx, div_le_iff₀ hδ0, hδ]
      have : q ≤ (q1 : ℝ) / 2 ^ E := hq.2
      rw [pow_add]
      have e : (2 : ℝ) ^ l * (((q1 : ℝ) - q0) / (2 ^ E * 2 ^ l)) = (q1 : ℝ) / 2 ^ E - (q0 : ℝ) / 2 ^ E := by
        field_simp
      linarith
    set i := min (⌊x⌋₊) (2 ^ l - 1) with hi
    have hpow : 1 ≤ 2 ^ l := Nat.one_le_two_pow
    have hiL : i < 2 ^ l := by omega
    have hix : (i : ℝ) ≤ x := by
      have : (i : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast min_le_left _ _
      exact this.trans (Nat.floor_le hx0)
    have hxi : x ≤ (i : ℝ) + 1 := by
      rcases le_total ⌊x⌋₊ (2 ^ l - 1) with h | h
      · have : i = ⌊x⌋₊ := min_eq_left h
        rw [this]; exact (Nat.lt_floor_add_one x).le
      · have : i = 2 ^ l - 1 := min_eq_right h
        rw [this]
        have : ((2 ^ l - 1 : ℕ) : ℝ) + 1 = 2 ^ l := by
          rw [Nat.cast_sub hpow]; push_cast; ring
        linarith
    refine ⟨i, hiL, ?_, ?_⟩
    · rw [(hpt i).1]
      have : (i : ℝ) * δ ≤ x * δ := mul_le_mul_of_nonneg_right hix hδ0.le
      have e : x * δ = q - (q0 : ℝ) / 2 ^ E := by rw [hx]; field_simp
      linarith
    · rw [(hpt i).2]
      have : x * δ ≤ ((i : ℝ) + 1) * δ := mul_le_mul_of_nonneg_right hxi hδ0.le
      have e : x * δ = q - (q0 : ℝ) / 2 ^ E := by rw [hx]; field_simp
      linarith

/-! ### Pieces of a tube for the functions of `t` -/

/-- The centre and the radius of a `t`-piece of a tube on the tile `(cT, aT, bT)`. -/
noncomputable def tpZ (cT : ℂ) (aT bT : ℝ) (x : TPc) : ℂ :=
  C64.ellipse cT aT bT (((x.n0 : ℝ) + x.n1) / 2 ^ (x.e + 1))

/-- Semantics of a `t`-piece. -/
structure TPOK (g : Glob) (cT : ℂ) (aT bT : ℝ) (x : TPc) : Prop where
  pt : PtOK g.P g.D (tpZ cT aT bT x) x.T
  dz : 2 * π * ((x.rho : ℝ) / 2 ^ g.P) * Real.exp (π * ((x.rho : ℝ) / 2 ^ g.P)) ≤ (x.dz : ℝ) / 2 ^ g.P
  yz : 2 * π * |(tpZ cT aT bT x).im| * Real.exp (π * |(tpZ cT aT bT x).im| / 16) ≤ (x.yz : ℝ) / 2 ^ g.P
  arc : ∀ q ∈ Set.Icc ((x.n0 : ℝ) / 2 ^ x.e) ((x.n1 : ℝ) / 2 ^ x.e),
    ‖C64.ellipse cT aT bT q - tpZ cT aT bT x‖ ≤ (x.rho : ℝ) / 2 ^ g.P

theorem tPiece_ok {g : Glob} (hg : GlobOK g) {cT : ℂ} {aT bT : ℝ} {E : EllB} (hE : EllOK g.P cT aT bT E)
    {n0 n1 e : ℕ} {x : TPc} (h01 : n0 ≤ n1) (he : e + 1 ≤ g.P) (h : tPiece g E n0 n1 e = some x) :
    x.n0 = n0 ∧ x.n1 = n1 ∧ x.e = e ∧ TPOK g cT aT bT x := by
  unfold tPiece at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨z, hz, rho, hrho, T, hT, ⟨dz, yz⟩, hd, rfl⟩ := h
  have hzm := memC_ellPt hE (mem_midB he) hz
  refine ⟨rfl, rfl, rfl, ⟨ptT_ok hzm hg.D1 hg.hD hT, ?_, ?_, fun q hq => ellRad_sound hE h01 he hrho hq⟩⟩
  all_goals
    unfold dzOf at hd
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at hd
    obtain ⟨ex, hex, ey, hey, rfl, rfl⟩ := hd
  · have hP := two_pow_pos' g.P
    have h1 : π * ((rho : ℝ) / 2 ^ g.P) ≤ (mulU g.P (piHi g.P) rho : ℝ) / 2 ^ g.P :=
      mulU_le Real.pi_pos.le (by positivity) pi_le_piHi le_rfl
    have h2 := exp_le_expPiHi hex (le_refl ((rho : ℝ) / 2 ^ g.P))
    have h3 := mulU_le (P := g.P) (x := 2 * (π * ((rho : ℝ) / 2 ^ g.P))) (y := Real.exp (π * ((rho : ℝ) / 2 ^ g.P)))
      (X := 2 * mulU g.P (piHi g.P) rho) (Y := ex) (by positivity) (by positivity)
      (by push_cast; rw [mul_div_assoc]; linarith) h2
    calc 2 * π * ((rho : ℝ) / 2 ^ g.P) * Real.exp (π * ((rho : ℝ) / 2 ^ g.P))
        = 2 * (π * ((rho : ℝ) / 2 ^ g.P)) * Real.exp (π * ((rho : ℝ) / 2 ^ g.P)) := by ring
      _ ≤ _ := h3
  · have hP := two_pow_pos' g.P
    have him := abs_le_absHi hzm.2
    simp only [tpZ]
    set Y := |(C64.ellipse cT aT bT (((n0 : ℝ) + n1) / 2 ^ (e + 1))).im|
    have h1 : π * Y ≤ (mulU g.P (piHi g.P) z.im.absHi : ℝ) / 2 ^ g.P :=
      mulU_le Real.pi_pos.le (abs_nonneg _) pi_le_piHi him
    have h2 : Real.exp (π * Y / 16) ≤ (ey : ℝ) / 2 ^ g.P := by
      have := exp_le_expPiHi hey (y := Y / 16) (cdiv_le (by norm_num) him)
      rw [show π * Y / 16 = π * (Y / 16) by ring]; exact this
    have h3 := mulU_le (P := g.P) (x := 2 * (π * Y)) (y := Real.exp (π * Y / 16))
      (X := 2 * mulU g.P (piHi g.P) z.im.absHi) (Y := ey) (by positivity) (by positivity)
      (by push_cast; rw [mul_div_assoc]; linarith) h2
    calc 2 * π * Y * Real.exp (π * Y / 16) = 2 * (π * Y) * Real.exp (π * Y / 16) := by ring
      _ ≤ _ := h3

/-! ### The data of a tube at a leaf -/

structure TubeCOK (gn : GlobN) (tb : TubeD) (tc : TubeC) : Prop where
  E : EllOK gn.g.P (tileR gn.g tb.ti).1 (tileR gn.g tb.ti).2.1 (tileR gn.g tb.ti).2.2 tc.E
  as : tc.as = tb.as
  hA : AtomsOK tb.as
  mS : msum tb.as ≤ (tc.mSum : ℝ) / 2 ^ gn.g.P
  ps : ∀ p ∈ tc.ps, IvPOK gn.g.P (tileR gn.g tb.ti).1 (tileR gn.g tb.ti).2.1 (tileR gn.g tb.ti).2.2 tb.as p ∧
    p.n0 ≤ p.n1 ∧ p.e + gn.dS + 1 ≤ gn.g.P
  cover : ∀ q ∈ Set.Icc ((tb.q0 : ℝ) / 2 ^ gn.g.EQ) ((tb.q1 : ℝ) / 2 ^ gn.g.EQ), ∃ p ∈ tc.ps,
    q ∈ Set.Icc ((p.n0 : ℝ) / 2 ^ p.e) ((p.n1 : ℝ) / 2 ^ p.e)
  ts : ∀ l < gn.nL, (∀ x ∈ tc.ts.getD l [], TPOK gn.g (tileR gn.g tb.ti).1 (tileR gn.g tb.ti).2.1
      (tileR gn.g tb.ti).2.2 x) ∧
    ∀ q ∈ Set.Icc ((tb.q0 : ℝ) / 2 ^ gn.g.EQ) ((tb.q1 : ℝ) / 2 ^ gn.g.EQ), ∃ x ∈ tc.ts.getD l [],
      q ∈ Set.Icc ((x.n0 : ℝ) / 2 ^ x.e) ((x.n1 : ℝ) / 2 ^ x.e)

theorem tubeC_ok {gn : GlobN} (hgn : GlobNOK gn) {tb : TubeD} {tc : TubeC}
    (h : tubeC gn tb = some tc) : TubeCOK gn tb tc := by
  unfold tubeC at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨E, hE, ⟨mn, md⟩, hmm, ps, hps, ts, hts, rfl⟩ := h
  obtain ⟨-, -, hEok⟩ := tileOf_okR hgn.g hE
  obtain ⟨hAt, hmd, hms⟩ := atomsOK_ok tb.as hmm
  have hg := hgn.g
  have hP := two_pow_pos' gn.g.P
  have hmS : msum tb.as ≤ (Ball.cdiv (mn.toNat * 2 ^ gn.g.P) md : ℝ) / 2 ^ gn.g.P := by
    have hmd' : (0 : ℝ) < md := by exact_mod_cast hmd
    have hmn : 0 ≤ mn := by
      have : (0 : ℝ) ≤ (mn : ℝ) / md := by
        rw [← hms]; exact List.sum_nonneg (fun x hx => by
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx; exact (hAt y hy).2.2.2)
      rcases div_nonneg_iff.1 this with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact_mod_cast h1
      · linarith
    have hc := cdiv_spec (mn.toNat * 2 ^ gn.g.P) md hmd
    push_cast at hc
    have e : ((mn.toNat : ℕ) : ℝ) = (mn : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hmn
    rw [e] at hc
    rw [hms, le_div_iff₀ hP]
    calc (mn : ℝ) / md * 2 ^ gn.g.P = (mn : ℝ) * 2 ^ gn.g.P / md := by ring
      _ ≤ _ := hc
  have hsub : ∀ l i, (subPc tb.q0 tb.q1 l i).1 ≤ (subPc tb.q0 tb.q1 l i).2 := by
    intro l i; simp only [subPc]; nlinarith
  have hps' := mapM_some hps
  have hts' := mapM_some hts
  refine ⟨hEok, rfl, hAt, hmS, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨i, -, hi⟩ := forall2_right_mem hps' p hp
    obtain ⟨e1, e2, e3, hok⟩ := ivPiece_ok hEok hAt hmS (hsub _ _) (by have := hgn.hS; (try simp only [Glob.cfg]); omega) hi
    refine ⟨hok, by rw [e1, e2]; exact hsub _ _, by rw [e3]; have := hgn.hS; (try simp only [Glob.cfg]); omega⟩
  · intro q hq
    obtain ⟨i, hi, hqi⟩ := subPc_cover (l := gn.lS) hq
    obtain ⟨p, hp, hpi⟩ := forall2_left_mem hps' i (List.mem_range.2 hi)
    obtain ⟨e1, e2, e3, -⟩ := ivPiece_ok hEok hAt hmS (hsub _ _) (by have := hgn.hS; (try simp only [Glob.cfg]); omega) hpi
    exact ⟨p, hp, by rw [e1, e2, e3]; exact hqi⟩
  · intro l hl
    have hL := mapM_some (forall2_range_getD (d := []) hts' hl)
    refine ⟨fun x hx => ?_, fun q hq => ?_⟩
    · obtain ⟨i, -, hi⟩ := forall2_right_mem hL x hx
      exact (tPiece_ok hg hEok (hsub _ _) (by have := hgn.hT; (try simp only [Glob.cfg]); omega) hi).2.2.2
    · obtain ⟨i, hi, hqi⟩ := subPc_cover (l := gn.lT + l) hq
      obtain ⟨x, hx, hxi⟩ := forall2_left_mem hL i (List.mem_range.2 hi)
      obtain ⟨e1, e2, e3, -⟩ := tPiece_ok hg hEok (hsub _ _) (by have := hgn.hT; (try simp only [Glob.cfg]); omega) hxi
      refine ⟨x, hx, ?_⟩
      rw [e1, e2, e3, show gn.g.EQ + gn.lT + l = gn.g.EQ + (gn.lT + l) by ring]; exact hqi

end C64Chk
