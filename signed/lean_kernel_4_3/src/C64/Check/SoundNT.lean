import C64.Check.SoundT
import C64Core.Nest

/-!
# Soundness of the nested checker, part 1: bounds in `t` with disc terms and groups (`cellsD`, `tboundD`)

A disc term `Re(c K_t(z))` with `‖z - ζ‖ ≤ ρ` is bounded on a cell `[t_c - h, t_c + h]` (`h = 2^{-e} ≤ 1/32`) by the
Taylor bound of `Re(c K_t(ζ))` plus the correction `corrD ≥ |c| |K_t(z) - K_t(ζ)|`.  A group (the pieces of an
interval tube) enters with the largest value plus correction, the hull of the derivatives and the largest `M₂`; for
every choice of one piece per group and of a point in its disc the bound holds.
-/

namespace C64Chk

open Ival Ival.Ball C64Num Real

variable {P : ℕ}

/-! ### Multiplication with shifts -/

theorem Ball.mulS_eq (P : ℕ) (a b : Ball) : Ball.mulS P a b = Ival.Ball.mul P a b := by
  simp only [Ball.mulS, Ival.Ball.mul, rnd2, Ival.Ball.cdiv, Nat.shiftLeft_eq, one_mul, Nat.shiftRight_eq_div_pow,
    Int.shiftRight_eq_div_pow, pow_one]

theorem CBall.mulS_eq (P : ℕ) (a b : CBall) : CBall.mulS P a b = C64Num.CBall.mul P a b := by
  simp only [CBall.mulS, C64Num.CBall.mul, Ball.mulS_eq]

theorem reMulS_eq (P : ℕ) (a b : CBall) : reMulS P a b = reMul P a b := by
  simp only [reMulS, reMul, Ball.mulS_eq]

/-! ### Disc terms -/

/-- The term state of a disc term. -/
def TermD.toS (T : TermD) : TermS := ⟨T.W, T.w, T.st, T.m2⟩

/-- Semantics of a disc term `Re(c K_t(z))`, `‖z - ζ‖ ≤ ρ`, at the cell `(t_c, e)`. -/
structure TermOKD (P : ℕ) (tc : ℝ) (e : ℕ) (c ζ : ℂ) (ρ : ℝ) (T : TermD) : Prop where
  base : TermOK P tc e c ζ T.toS
  hρ : 0 ≤ ρ
  dz : 2 * π * ρ * Real.exp (π * ρ) ≤ (T.dz : ℝ) / 2 ^ P
  yz : 0 < ρ → 2 * π * |ζ.im| * Real.exp (π * |ζ.im| / 16) ≤ (T.yz : ℝ) / 2 ^ P

theorem stepD_toS (P : ℕ) (down : Bool) (T : TermD) : (stepD P down T).toS = stepT P down T.toS := by
  obtain ⟨W, w, st, m2, dz, yz⟩ := T
  cases st with
  | nil => rfl
  | cons x rest => obtain ⟨kp, km⟩ := x; simp [stepD, stepT, TermD.toS, CBall.mulS_eq]

theorem stepD_dz (P : ℕ) (down : Bool) (T : TermD) : (stepD P down T).dz = T.dz ∧ (stepD P down T).yz = T.yz := by
  obtain ⟨W, w, st, m2, dz, yz⟩ := T
  cases st with
  | nil => exact ⟨rfl, rfl⟩
  | cons x rest => obtain ⟨kp, km⟩ := x; exact ⟨rfl, rfl⟩

theorem stepD_ok {tc : ℝ} {e : ℕ} {c ζ : ℂ} {ρ : ℝ} {T : TermD} (hT : TermOKD P tc e c ζ ρ T) (hne : T.st ≠ [])
    (down : Bool) :
    TermOKD P (if down then tc - 1 / 2 ^ (e + 1) else tc + 1 / 2 ^ (e + 1)) (e + 1) c ζ ρ (stepD P down T) := by
  have hne' : T.toS.st ≠ [] := hne
  obtain ⟨h1, h2⟩ := stepD_dz P down T
  refine ⟨?_, hT.hρ, ?_, ?_⟩
  · rw [stepD_toS]; exact stepT_ok hT.base hne' down
  · rw [h1]; exact hT.dz
  · rw [h2]; exact hT.yz

theorem stepD_len {T : TermD} (hne : T.st ≠ []) (down : Bool) : (stepD P down T).st.length + 1 = T.st.length := by
  have := stepT_len (P := P) (T := T.toS) hne down
  rw [← stepD_toS] at this
  exact this

theorem termD_ok {D : ℕ} {c ζ : ℂ} {ρ : ℝ} {cf : CBall} {T : PtT} {dy : ℕ × ℕ} (hT : PtOK P D ζ T)
    (hc : memC P c cf) (hρ : 0 ≤ ρ) (hdz : 2 * π * ρ * Real.exp (π * ρ) ≤ (dy.1 : ℝ) / 2 ^ P)
    (hyz : 0 < ρ → 2 * π * |ζ.im| * Real.exp (π * |ζ.im| / 16) ≤ (dy.2 : ℝ) / 2 ^ P) :
    TermOKD P 0 1 c ζ ρ (termD cf T dy) :=
  ⟨termOf_ok hT hc, hρ, hdz, hyz⟩

theorem toD_ok {tc : ℝ} {e : ℕ} {c ζ : ℂ} {T : TermS} (hT : TermOK P tc e c ζ T) : TermOKD P tc e c ζ 0 (toD T) :=
  ⟨hT, le_rfl, by simp [toD], fun h => absurd h (lt_irrefl 0)⟩

/-! ### Norm bounds -/

theorem absW_ok {w : ℂ} {W : CBall} (hw : memC P w W) : ‖w‖ ≤ (absW W : ℝ) / 2 ^ P := by
  have hP := two_pow_pos' P
  have h1 := abs_le_absHi hw.1
  have h2 := abs_le_absHi hw.2
  set a : ℝ := (W.re.absHi : ℝ)
  set b : ℝ := (W.im.absHi : ℝ)
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have key : ‖w‖ ≤ (max a b + min a b / 2) / 2 ^ P := by
    have hX : 0 ≤ (max a b + min a b / 2) / 2 ^ P := by positivity
    have hsq : ‖w‖ ^ 2 ≤ ((max a b + min a b / 2) / 2 ^ P) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      have hre : w.re * w.re ≤ (a / 2 ^ P) ^ 2 := by
        have := sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2; nlinarith
      have him : w.im * w.im ≤ (b / 2 ^ P) ^ 2 := by
        have := sq_le_sq' (abs_le.1 h2).1 (abs_le.1 h2).2; nlinarith
      have hab : (a / 2 ^ P) ^ 2 + (b / 2 ^ P) ^ 2 ≤ ((max a b + min a b / 2) / 2 ^ P) ^ 2 := by
        rw [div_pow, div_pow, div_pow, ← add_div]
        apply div_le_div_of_nonneg_right _ (by positivity)
        rcases le_total a b with h | h
        · rw [max_eq_right h, min_eq_left h]; nlinarith
        · rw [max_eq_left h, min_eq_right h]; nlinarith
      linarith
    nlinarith [norm_nonneg w]
  refine key.trans (div_le_div_of_nonneg_right ?_ hP.le)
  have hm : (W.re.absHi ⊓ W.im.absHi : ℕ) ≤ 2 * ((W.re.absHi ⊓ W.im.absHi + 1) / 2) := by omega
  have hm' : ((W.re.absHi ⊓ W.im.absHi : ℕ) : ℝ) ≤ 2 * (((W.re.absHi ⊓ W.im.absHi + 1) / 2 : ℕ) : ℝ) := by
    exact_mod_cast hm
  unfold absW
  push_cast
  simp only [a, b] at *
  rw [Nat.cast_min] at hm'
  linarith

theorem Kt_add_z (t : ℝ) (ζ δ : ℂ) : C64.Kt t (ζ + δ) = C64.Kt t ζ * C64.Kt t δ := by
  simp only [C64.Kt, ← Complex.exp_add]; congr 1; ring

theorem norm_Kt_sub_le {t : ℝ} {ζ z : ℂ} {ρ : ℝ} (hz : ‖z - ζ‖ ≤ ρ) :
    ‖C64.Kt t z - C64.Kt t ζ‖ ≤ 2 * π * |t| * ‖C64.Kt t ζ‖ * Real.exp (2 * π * |t| * ρ) * ρ := by
  have hρ : 0 ≤ ρ := le_trans (norm_nonneg _) hz
  have h := (convex_closedBall ζ ρ).norm_image_sub_le_of_norm_hasDerivWithin_le (f := C64.Kt t)
    (C := 2 * π * |t| * ‖C64.Kt t ζ‖ * Real.exp (2 * π * |t| * ρ))
    (fun w _ => (C64.hasDerivAt_Kt t w).hasDerivWithinAt) (fun w hw => by
      rw [Metric.mem_closedBall, dist_eq_norm] at hw
      rw [norm_mul]
      have h1 : ‖(-2 * π * Complex.I * t : ℂ)‖ = 2 * π * |t| := by simp [Real.pi_pos.le]
      rw [h1, C64.norm_Kt, C64.norm_Kt]
      have h3 : |w.im - ζ.im| ≤ ρ := by rw [← Complex.sub_im]; exact (Complex.abs_im_le_norm _).trans hw
      have h4 : t * (w.im - ζ.im) ≤ |t| * ρ :=
        (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left h3 (abs_nonneg t))
      have h2 : 2 * π * t * w.im ≤ 2 * π * t * ζ.im + 2 * π * |t| * ρ := by nlinarith [Real.pi_pos]
      calc 2 * π * |t| * Real.exp (2 * π * t * w.im) ≤
            2 * π * |t| * Real.exp (2 * π * t * ζ.im + 2 * π * |t| * ρ) := by gcongr
        _ = 2 * π * |t| * Real.exp (2 * π * t * ζ.im) * Real.exp (2 * π * |t| * ρ) := by
          rw [Real.exp_add]; ring)
    (Metric.mem_closedBall_self hρ) (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hz)
  exact h.trans (mul_le_mul_of_nonneg_left hz (by positivity))

/-- The disc correction. -/
theorem corrD_ok {tc : ℝ} {e : ℕ} {c ζ : ℂ} {ρ : ℝ} {T : TermD} (hT : TermOKD P tc e c ζ ρ T) (he : 5 ≤ e)
    {tn : ℤ} (htc : tc = (tn : ℝ) / 2 ^ e) {t : ℝ} (ht : t ∈ Set.Icc (tc - 1 / 2 ^ e) (tc + 1 / 2 ^ e))
    (ht2 : |t| ≤ 1 / 2) {z : ℂ} (hz : ‖z - ζ‖ ≤ ρ) :
    ‖c * C64.Kt t z - c * C64.Kt t ζ‖ ≤ (corrD P e tn T : ℝ) / 2 ^ P := by
  have hP := two_pow_pos' P
  have hE := two_pow_pos' e
  have hcorr0 : (0 : ℝ) ≤ (corrD P e tn T : ℝ) / 2 ^ P := by positivity
  rcases eq_or_lt_of_le hT.hρ with h0 | hpos
  · have : z = ζ := by rw [← h0] at hz; exact sub_eq_zero.1 (norm_le_zero_iff.1 hz)
    rw [this, sub_self, norm_zero]; exact hcorr0
  have hh : (1 : ℝ) / 2 ^ e ≤ 1 / 32 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (32 : ℝ) ≤ 2 ^ e := by
      calc (32 : ℝ) = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ e := pow_le_pow_right₀ (by norm_num) he
    linarith
  have hd : |t - tc| ≤ 1 / 2 ^ e := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  set H : ℝ := 1 / 2 ^ e with hH
  have hH0 : 0 ≤ H := by positivity
  set Yr : ℝ := (T.yz : ℝ) / 2 ^ P
  have hKt : ‖C64.Kt t ζ‖ ≤ ‖C64.Kt tc ζ‖ * (1 + H * Yr) := by
    have hs : C64.Kt t ζ = C64.Kt tc ζ * C64.Kt (t - tc) ζ := by rw [← C64.Kt_add]; congr 1; ring
    rw [hs, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hb := norm_Kt_le_abs (t - tc) ζ
    set x := 2 * π * H * |ζ.im| with hx
    have hx0 : 0 ≤ x := by positivity
    have hx1 : Real.exp x ≤ 1 + x * Real.exp x := by
      have h1 := Real.add_one_le_exp (-x)
      have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos x]
    have hx2 : x * Real.exp x ≤ H * Yr := by
      have hY := hT.yz hpos
      have h3 : Real.exp x ≤ Real.exp (π * |ζ.im| / 16) := Real.exp_le_exp.2 (by
        have h4 : H * |ζ.im| ≤ 1 / 32 * |ζ.im| := mul_le_mul_of_nonneg_right hh (abs_nonneg _)
        rw [hx]; nlinarith [Real.pi_pos])
      calc x * Real.exp x ≤ x * Real.exp (π * |ζ.im| / 16) := mul_le_mul_of_nonneg_left h3 hx0
        _ = H * (2 * π * |ζ.im| * Real.exp (π * |ζ.im| / 16)) := by rw [hx]; ring
        _ ≤ H * Yr := mul_le_mul_of_nonneg_left hY hH0
    calc ‖C64.Kt (t - tc) ζ‖ ≤ Real.exp (2 * π * |t - tc| * |ζ.im|) := hb
      _ ≤ Real.exp x := Real.exp_le_exp.2 (by
          rw [hx]; have := abs_nonneg ζ.im; have := Real.pi_pos
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by positivity)) (abs_nonneg _))
      _ ≤ 1 + x * Real.exp x := hx1
      _ ≤ 1 + H * Yr := by linarith
  have htabs : |t| ≤ ((tn.natAbs : ℝ) + 1) * H := by
    have hna : ((tn.natAbs : ℕ) : ℝ) = |(tn : ℝ)| := by simp [Nat.cast_natAbs, Int.cast_abs]
    have hc : |tc| = (tn.natAbs : ℝ) * H := by
      rw [htc, abs_div, abs_of_pos hE, hH, hna]; ring
    calc |t| ≤ |tc| + |t - tc| := by linarith [abs_sub_abs_le_abs_sub t tc]
      _ ≤ (tn.natAbs : ℝ) * H + H := by rw [hc]; linarith
      _ = _ := by ring
  have hexp : Real.exp (2 * π * |t| * ρ) ≤ Real.exp (π * ρ) := Real.exp_le_exp.2 (by
    have := mul_le_mul_of_nonneg_right ht2 hT.hρ; nlinarith [Real.pi_pos])
  have hW := absW_ok hT.base.W
  have hK := norm_Kt_sub_le (t := t) hz
  set Wr : ℝ := (absW T.W : ℝ) / 2 ^ P
  set Dr : ℝ := (T.dz : ℝ) / 2 ^ P
  set N : ℝ := (tn.natAbs : ℝ) + 1
  have hN0 : 0 ≤ N := by positivity
  have hY0 : 0 ≤ Yr := by positivity
  have hDr : 2 * π * ρ * Real.exp (π * ρ) ≤ Dr := hT.dz
  have hcK : ‖c‖ * ‖C64.Kt tc ζ‖ ≤ Wr := by rw [← norm_mul]; exact hW
  have hmain : ‖c * C64.Kt t z - c * C64.Kt t ζ‖ ≤ Wr * Dr * N * H * (1 + H * Yr) := by
    rw [← mul_sub, norm_mul]
    calc ‖c‖ * ‖C64.Kt t z - C64.Kt t ζ‖
        ≤ ‖c‖ * (2 * π * |t| * ‖C64.Kt t ζ‖ * Real.exp (2 * π * |t| * ρ) * ρ) :=
          mul_le_mul_of_nonneg_left hK (norm_nonneg _)
      _ ≤ ‖c‖ * (2 * π * (N * H) * (‖C64.Kt tc ζ‖ * (1 + H * Yr)) * Real.exp (π * ρ) * ρ) := by
          gcongr
      _ = (‖c‖ * ‖C64.Kt tc ζ‖) * (2 * π * ρ * Real.exp (π * ρ)) * N * H * (1 + H * Yr) := by ring
      _ ≤ Wr * Dr * N * H * (1 + H * Yr) := by gcongr
  refine hmain.trans ?_
  -- the integer bound
  set A := mulU P (absW T.W) T.dz
  have hA : Wr * Dr ≤ (A : ℝ) / 2 ^ P := mulU_le (by positivity) (by positivity) le_rfl le_rfl
  have hAY : (A : ℝ) / 2 ^ P * Yr ≤ (mulU P A T.yz : ℝ) / 2 ^ P := mulU_le (by positivity) hY0 le_rfl le_rfl
  have hc1 := cdiv_le (P := P) (x := (A : ℝ) / 2 ^ P * N) (X := A * (tn.natAbs + 1)) (d := 2 ^ e) (by positivity)
    (by push_cast; rw [mul_div_right_comm])
  have hc2 := cdiv_le (P := P) (x := (mulU P A T.yz : ℝ) / 2 ^ P * N) (X := mulU P A T.yz * (tn.natAbs + 1))
    (d := 2 ^ (2 * e)) (by positivity) (by push_cast; rw [mul_div_right_comm])
  unfold corrD
  push_cast at hc1 hc2 ⊢
  rw [add_div]
  have e1 : Wr * Dr * N * H * (1 + H * Yr) = (Wr * Dr) * N * H + (Wr * Dr) * Yr * N * (H * H) := by ring
  rw [e1]
  have hHH : H * H = 1 / (2 : ℝ) ^ (2 * e) := by rw [hH, pow_mul', sq]; field_simp
  refine add_le_add ?_ ?_
  · calc Wr * Dr * N * H ≤ (A : ℝ) / 2 ^ P * N * H := by gcongr
      _ = (A : ℝ) / 2 ^ P * N / 2 ^ e := by rw [hH]; ring
      _ ≤ _ := hc1
  · calc Wr * Dr * Yr * N * (H * H) ≤ (A : ℝ) / 2 ^ P * Yr * N * (H * H) := by gcongr
      _ ≤ (mulU P A T.yz : ℝ) / 2 ^ P * N * (H * H) := by gcongr
      _ = (mulU P A T.yz : ℝ) / 2 ^ P * N / 2 ^ (2 * e) := by rw [hHH]; ring
      _ ≤ _ := hc2

/-! ### Main terms of a cell -/

/-- A semantic disc term (coefficient, centre, radius) with its state. -/
abbrev DTerm := (ℂ × ℂ × ℝ) × TermD

def DOK (P : ℕ) (tc : ℝ) (e : ℕ) (p : DTerm) : Prop := TermOKD P tc e p.1.1 p.1.2.1 p.1.2.2 p.2

/-- The centres `(c, ζ)` of a list of disc terms. -/
def cens (l : List DTerm) : List (ℂ × ℂ) := l.map fun p => (p.1.1, p.1.2.1)

theorem fsum_cons (a : ℂ × ℂ) (l : List (ℂ × ℂ)) (t : ℝ) : fsum (a :: l) t = (a.1 * C64.Kt t a.2).re + fsum l t := by
  simp [fsum]

theorem f1sum_cons (a : ℂ × ℂ) (l : List (ℂ × ℂ)) (t : ℝ) :
    f1sum (a :: l) t = (a.1 * wOf a.2 * C64.Kt t a.2).re + f1sum l t := by
  simp [f1sum]

theorem fsum_append (l1 l2 : List (ℂ × ℂ)) (t : ℝ) : fsum (l1 ++ l2) t = fsum l1 t + fsum l2 t := by
  simp [fsum, List.map_append, List.sum_append]

theorem f1sum_append (l1 l2 : List (ℂ × ℂ)) (t : ℝ) : f1sum (l1 ++ l2) t = f1sum l1 t + f1sum l2 t := by
  simp [f1sum, List.map_append, List.sum_append]

/-- `M₂` of a list of centres at `t_c`. -/
noncomputable def mOf (tc : ℝ) (l : List (ℂ × ℂ)) : ℝ :=
  (l.map fun p => ‖p.1 * C64.Kt tc p.2‖ * (‖wOf p.2‖ ^ 2 * Real.exp (2 * π * |p.2.im| / 32))).sum

theorem mOf_append (tc : ℝ) (l1 l2 : List (ℂ × ℂ)) : mOf tc (l1 ++ l2) = mOf tc l1 + mOf tc l2 := by
  simp [mOf, List.map_append, List.sum_append]

theorem mOf_cons (tc : ℝ) (a : ℂ × ℂ) (l : List (ℂ × ℂ)) :
    mOf tc (a :: l) = ‖a.1 * C64.Kt tc a.2‖ * (‖wOf a.2‖ ^ 2 * Real.exp (2 * π * |a.2.im| / 32)) + mOf tc l := by
  simp [mOf]

/-- One term: `‖c K_tc ζ‖ (‖w‖² e^{..}) ≤ mulU (absW W) m₂`. -/
theorem m2_term {tc : ℝ} {e : ℕ} {c ζ : ℂ} {T : TermS} (hT : TermOK P tc e c ζ T) :
    ‖c * C64.Kt tc ζ‖ * (‖wOf ζ‖ ^ 2 * Real.exp (2 * π * |ζ.im| / 32)) ≤
      (mulU P (absW T.W) T.m2 : ℝ) / 2 ^ P :=
  mulU_le (norm_nonneg _) (by positivity) (absW_ok hT.W) hT.m2

theorem sumTermsD_cons (P e : ℕ) (tn : ℤ) (T : TermD) (ts : List TermD) :
    sumTermsD P e tn (T :: ts) = (Ball.add T.W.re (sumTermsD P e tn ts).1,
      Ball.add (reMulS P T.W T.w) (sumTermsD P e tn ts).2.1, mulU P (absW T.W) T.m2 + (sumTermsD P e tn ts).2.2.1,
      corrD P e tn T + (sumTermsD P e tn ts).2.2.2) := rfl

attribute [local irreducible] corrD mulU absW reMulS Ival.Ball.cdiv Ival.Ball.add Ival.Ball.mul fsum f1sum mOf

theorem sumTermsD_ok {tc : ℝ} {e : ℕ} {tn : ℤ} (he : 5 ≤ e) (htc : tc = (tn : ℝ) / 2 ^ e) (mp : List DTerm) :
    ∀ (zm : List ℂ), (∀ p ∈ mp, DOK P tc e p) →
      List.Forall₂ (fun z (p : DTerm) => ‖z - p.1.2.1‖ ≤ p.1.2.2) zm mp →
      mem P (fsum (cens mp) tc) (sumTermsD P e tn (mp.map Prod.snd)).1 ∧
      mem P (f1sum (cens mp) tc) (sumTermsD P e tn (mp.map Prod.snd)).2.1 ∧
      mOf tc (cens mp) ≤ ((sumTermsD P e tn (mp.map Prod.snd)).2.2.1 : ℝ) / 2 ^ P ∧
      ∀ t ∈ Set.Icc (tc - 1 / 2 ^ e) (tc + 1 / 2 ^ e), |t| ≤ 1 / 2 →
        fsum (List.zipWith (fun z (p : DTerm) => (p.1.1, z)) zm mp) t ≤
          fsum (cens mp) t + ((sumTermsD P e tn (mp.map Prod.snd)).2.2.2 : ℝ) / 2 ^ P := by
  induction mp with
  | nil =>
    intro zm _ hz
    cases hz
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [sumTermsD, cens, fsum, f1sum, mOf, mem]
  | cons p mp ih =>
    intro zm hok hz
    cases hz with
    | cons hz1 hzr =>
    rename_i z zm
    have hp : DOK P tc e p := hok p List.mem_cons_self
    obtain ⟨i1, i2, i3, i4⟩ := ih zm (fun q hq => hok q (List.mem_cons_of_mem _ hq)) hzr
    have hP := two_pow_pos' P
    rw [List.map_cons, sumTermsD_cons]
    simp only [cens, List.map_cons] at i1 i2 i3 i4 ⊢
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [fsum_cons]; exact mem_add hp.base.W.1 i1
    · rw [f1sum_cons, reMulS_eq]
      have := (C64Num.CBall.memC_mul hp.base.W hp.base.w).1
      rw [show p.1.1 * wOf p.1.2.1 * C64.Kt tc p.1.2.1 = p.1.1 * C64.Kt tc p.1.2.1 * wOf p.1.2.1 by ring]
      exact mem_add this i2
    · rw [mOf_cons]; push_cast; rw [add_div]; exact add_le_add (m2_term hp.base) i3
    · intro t ht ht2
      simp only [List.zipWith_cons_cons, fsum_cons]
      have hc := corrD_ok hp he htc ht ht2 hz1
      have hre : (p.1.1 * C64.Kt t z).re ≤ (p.1.1 * C64.Kt t p.1.2.1).re + (corrD P e tn p.2 : ℝ) / 2 ^ P := by
        have := (Complex.re_le_norm (p.1.1 * C64.Kt t z - p.1.1 * C64.Kt t p.1.2.1)).trans hc
        rw [Complex.sub_re] at this; linarith
      have := i4 t ht ht2
      push_cast; rw [add_div]; linarith

/-! ### Groups -/

theorem groupB_ok {e : ℕ} {tn : ℤ} : ∀ (G : List TermD) {b : ℤ × Ball × ℕ}, groupB P e tn G = some b →
    ∀ T ∈ G, T.W.re.hi + (corrD P e tn T : ℤ) ≤ b.1 ∧ (∀ x, mem P x (reMulS P T.W T.w) → mem P x b.2.1) ∧
      mulU P (absW T.W) T.m2 ≤ b.2.2
  | [], _, h => by simp [groupB] at h
  | [T], b, h => by
    simp only [groupB, Option.some.injEq] at h
    subst h
    intro T' hT'
    simp only [List.mem_singleton] at hT'
    subst hT'
    exact ⟨le_rfl, fun x hx => hx, le_rfl⟩
  | T :: T2 :: ts, b, h => by
    unfold groupB at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨b', hb', rfl⟩ := h
    have ih := groupB_ok (T2 :: ts) hb'
    intro T' hT'
    simp only [List.mem_cons] at hT'
    rcases hT' with rfl | hT'
    · refine ⟨le_max_left _ _, fun x hx => ?_, le_max_left _ _⟩
      have := mem_iff_lo_hi.1 hx
      refine mem_hullB (le_trans ?_ this.1) (le_trans this.2 ?_)
      · push_cast; exact div_le_div_of_nonneg_right (by exact_mod_cast min_le_left _ _) (two_pow_pos' P).le
      · push_cast; exact div_le_div_of_nonneg_right (by exact_mod_cast le_max_left _ _) (two_pow_pos' P).le
    · obtain ⟨j1, j2, j3⟩ := ih T' (by simpa using hT')
      refine ⟨j1.trans (le_max_right _ _), fun x hx => ?_, j3.trans (le_max_right _ _)⟩
      have := mem_iff_lo_hi.1 (j2 x hx)
      refine mem_hullB (le_trans ?_ this.1) (le_trans this.2 ?_)
      · push_cast; exact div_le_div_of_nonneg_right (by exact_mod_cast min_le_right _ _) (two_pow_pos' P).le
      · push_cast; exact div_le_div_of_nonneg_right (by exact_mod_cast le_max_right _ _) (two_pow_pos' P).le

/-- The groups: for every choice of one piece per group and of a point in its disc. -/
theorem groupsB_ok {tc : ℝ} {e : ℕ} {tn : ℤ} (he : 5 ≤ e) (htc : tc = (tn : ℝ) / 2 ^ e) (gp : List (List DTerm)) :
    ∀ {b : ℤ × Ball × ℕ}, groupsB P e tn (gp.map (·.map Prod.snd)) = some b →
      (∀ G ∈ gp, ∀ p ∈ G, DOK P tc e p) → ∀ (sel : List (ℂ × ℂ)),
      List.Forall₂ (fun (cz : ℂ × ℂ) (G : List DTerm) => ∃ p ∈ G, cz.1 = p.1.1 ∧ ‖cz.2 - p.1.2.1‖ ≤ p.1.2.2) sel gp →
      ∃ (cen : List (ℂ × ℂ)) (Kc : ℝ),
        (∀ t ∈ Set.Icc (tc - 1 / 2 ^ e) (tc + 1 / 2 ^ e), |t| ≤ 1 / 2 → fsum sel t ≤ fsum cen t + Kc) ∧
        fsum cen tc + Kc ≤ (b.1 : ℝ) / 2 ^ P ∧ mem P (f1sum cen tc) b.2.1 ∧ mOf tc cen ≤ (b.2.2 : ℝ) / 2 ^ P := by
  induction gp with
  | nil =>
    intro b h _ sel hsel
    cases hsel
    simp only [List.map_nil, groupsB, Option.some.injEq] at h
    subst h
    exact ⟨[], 0, fun t _ _ => by simp [fsum], by simp [fsum], by simp [f1sum, mem], by simp [mOf]⟩
  | cons G gp ih =>
    intro b h hok sel hsel
    cases hsel with
    | cons hcz hrest =>
    rename_i cz sel
    obtain ⟨p, hpG, hc, hz⟩ := hcz
    simp only [List.map_cons, groupsB, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨bg, hbg, bs, hbs, rfl⟩ := h
    obtain ⟨cen, Kc, k1, k2, k3, k4⟩ := ih hbs (fun G' hG' q hq => hok G' (List.mem_cons_of_mem _ hG') q hq)
      sel hrest
    have hp : DOK P tc e p := hok G List.mem_cons_self p hpG
    obtain ⟨j1, j2, j3⟩ := groupB_ok (G.map Prod.snd) hbg p.2 (List.mem_map_of_mem hpG)
    have hP := two_pow_pos' P
    set cr : ℝ := (corrD P e tn p.2 : ℝ) / 2 ^ P
    refine ⟨(p.1.1, p.1.2.1) :: cen, cr + Kc, ?_, ?_, ?_, ?_⟩
    · intro t ht ht2
      rw [fsum_cons, fsum_cons]
      have hcd := corrD_ok hp he htc ht ht2 hz
      have hre : (cz.1 * C64.Kt t cz.2).re ≤ (p.1.1 * C64.Kt t p.1.2.1).re + cr := by
        rw [hc]
        have := (Complex.re_le_norm (p.1.1 * C64.Kt t cz.2 - p.1.1 * C64.Kt t p.1.2.1)).trans hcd
        rw [Complex.sub_re] at this; linarith
      have := k1 t ht ht2
      linarith
    · rw [fsum_cons]
      have hv := (mem_iff_lo_hi.1 hp.base.W.1).2
      have hj1 : ((p.2.W.re.hi + (corrD P e tn p.2 : ℤ) : ℤ) : ℝ) ≤ (bg.1 : ℝ) := by exact_mod_cast j1
      push_cast at hj1 ⊢
      have : (p.2.W.re.hi : ℝ) / 2 ^ P + cr ≤ (bg.1 : ℝ) / 2 ^ P := by
        rw [← add_div]; exact div_le_div_of_nonneg_right hj1 hP.le
      simp only [TermD.toS] at hv
      rw [add_div]; linarith
    · rw [f1sum_cons]
      have := (C64Num.CBall.memC_mul hp.base.W hp.base.w).1
      rw [show p.1.1 * wOf p.1.2.1 * C64.Kt tc p.1.2.1 = p.1.1 * C64.Kt tc p.1.2.1 * wOf p.1.2.1 by ring]
      have h2 := j2 _ (by rw [reMulS_eq]; exact this)
      exact mem_add h2 k3
    · rw [mOf_cons]
      have hm := m2_term hp.base
      have hj3 : (mulU P (absW p.2.W) p.2.m2 : ℝ) ≤ (bg.2.2 : ℝ) := by exact_mod_cast j3
      push_cast
      rw [add_div]
      exact add_le_add (hm.trans (div_le_div_of_nonneg_right hj3 hP.le)) k4

/-! ### The cell bound -/

theorem f2sum_cell {tc : ℝ} {e : ℕ} (he : 5 ≤ e) (czs : List (ℂ × ℂ)) :
    ∀ x ∈ Set.Icc (tc - 1 / 2 ^ e) (tc + 1 / 2 ^ e), |f2sum czs x| ≤ mOf tc czs := by
  have hδ : (1 : ℝ) / 2 ^ e ≤ 1 / 32 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (32 : ℝ) ≤ 2 ^ e := by
      calc (32 : ℝ) = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ e := pow_le_pow_right₀ (by norm_num) he
    linarith
  intro x hx
  have hxd : |x - tc| ≤ 1 / 32 := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  unfold f2sum mOf
  induction czs with
  | nil => simp
  | cons p czs ih =>
    simp only [List.map_cons, List.sum_cons]
    refine (abs_add_le _ _).trans (add_le_add ?_ ih)
    refine (Complex.abs_re_le_norm _).trans ?_
    have hk : C64.Kt x p.2 = C64.Kt tc p.2 * C64.Kt (x - tc) p.2 := by
      rw [← C64.Kt_add]; congr 1; ring
    have hb : ‖C64.Kt (x - tc) p.2‖ ≤ Real.exp (2 * π * |p.2.im| / 32) := by
      refine (norm_Kt_le_abs _ _).trans (Real.exp_le_exp.2 ?_)
      have := mul_le_mul_of_nonneg_right hxd (abs_nonneg p.2.im)
      nlinarith [Real.pi_pos, abs_nonneg p.2.im]
    rw [hk, show p.1 * wOf p.2 ^ 2 * (C64.Kt tc p.2 * C64.Kt (x - tc) p.2) =
      (p.1 * C64.Kt tc p.2) * C64.Kt (x - tc) p.2 * wOf p.2 ^ 2 by ring, norm_mul, norm_mul, norm_pow]
    calc ‖p.1 * C64.Kt tc p.2‖ * ‖C64.Kt (x - tc) p.2‖ * ‖wOf p.2‖ ^ 2
        ≤ ‖p.1 * C64.Kt tc p.2‖ * Real.exp (2 * π * |p.2.im| / 32) * ‖wOf p.2‖ ^ 2 := by gcongr
      _ = ‖p.1 * C64.Kt tc p.2‖ * (‖wOf p.2‖ ^ 2 * Real.exp (2 * π * |p.2.im| / 32)) := by ring

/-- The semantic content of a cell or tree check: for every choice of points in the discs of the main terms and of
one piece per group with a point in its disc, the bound holds on the cell. -/
def CellBound (P : ℕ) (target : ℤ) (tc : ℝ) (e : ℕ) (mp : List DTerm) (gp : List (List DTerm)) : Prop :=
  ∀ (zm : List ℂ), List.Forall₂ (fun z (p : DTerm) => ‖z - p.1.2.1‖ ≤ p.1.2.2) zm mp →
  ∀ (sel : List (ℂ × ℂ)),
    List.Forall₂ (fun (cz : ℂ × ℂ) (G : List DTerm) => ∃ p ∈ G, cz.1 = p.1.1 ∧ ‖cz.2 - p.1.2.1‖ ≤ p.1.2.2) sel gp →
  ∀ t ∈ Set.Icc (tc - 1 / 2 ^ e) (tc + 1 / 2 ^ e), |t| ≤ 1 / 2 →
    fsum (List.zipWith (fun z (p : DTerm) => (p.1.1, z)) zm mp) t + fsum sel t < (target : ℝ) / 2 ^ P

theorem cellOKD_ok {target : ℤ} {tc : ℝ} {e : ℕ} {tn : ℤ} (htc : tc = (tn : ℝ) / 2 ^ e)
    {mp : List DTerm} {gp : List (List DTerm)}
    (h : cellOKD P (mp.map Prod.snd) (gp.map (·.map Prod.snd)) e tn target = true)
    (hmp : ∀ p ∈ mp, DOK P tc e p) (hgp : ∀ G ∈ gp, ∀ p ∈ G, DOK P tc e p) :
    CellBound P target tc e mp gp := by
  unfold cellOKD at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Option.any_eq_true] at h
  obtain ⟨he5, b, hb, hlt⟩ := h
  intro zm hzm sel hsel t ht ht2
  obtain ⟨i1, i2, i3, i4⟩ := sumTermsD_ok (P := P) he5 htc mp zm hmp hzm
  obtain ⟨cen, Kc, k1, k2, k3, k4⟩ := groupsB_ok (P := P) he5 htc gp hb hgp sel hsel
  set f := (sumTermsD P e tn (mp.map Prod.snd)).1
  set f1 := (sumTermsD P e tn (mp.map Prod.snd)).2.1
  set m := (sumTermsD P e tn (mp.map Prod.snd)).2.2.1
  set d := (sumTermsD P e tn (mp.map Prod.snd)).2.2.2
  have hP := two_pow_pos' P
  set C := cens mp ++ cen
  have hM : ∀ x ∈ Set.Icc (tc - 1 / 2 ^ e) (tc + 1 / 2 ^ e), |f2sum C x| ≤ (m + b.2.2 : ℝ) / 2 ^ P := by
    intro x hx
    refine (f2sum_cell he5 C x hx).trans ?_
    rw [mOf_append, add_div]; exact add_le_add i3 k4
  have hT := C64.taylor2_upper (hasDerivAt_fsum C) (hasDerivAt_f1sum C) (by positivity) hM t ht
  have hf := (mem_iff_lo_hi.1 i1).2
  have hF1 : mem P (f1sum C tc) (Ball.add f1 b.2.1) := by rw [f1sum_append]; exact mem_add i2 k3
  have hf1 := abs_le_absHi hF1
  have h1 : |f1sum C tc| * (1 / 2 ^ e) ≤ (Ball.cdiv (Ball.add f1 b.2.1).absHi (2 ^ e) : ℝ) / 2 ^ P := by
    have := cdiv_le (P := P) (d := 2 ^ e) (by positivity) hf1
    push_cast at this
    calc |f1sum C tc| * (1 / 2 ^ e) = |f1sum C tc| / 2 ^ e := by ring
      _ ≤ _ := this
  have h2 : (m + b.2.2 : ℝ) / 2 ^ P * (1 / 2 ^ e) ^ 2 / 2 ≤ (Ball.cdiv (m + b.2.2) (2 ^ (2 * e + 1)) : ℝ) / 2 ^ P := by
    have := cdiv_le (P := P) (x := (m + b.2.2 : ℝ) / 2 ^ P) (X := m + b.2.2) (d := 2 ^ (2 * e + 1)) (by positivity)
      (by push_cast; exact le_rfl)
    push_cast at this
    calc (m + b.2.2 : ℝ) / 2 ^ P * (1 / 2 ^ e) ^ 2 / 2 = (m + b.2.2 : ℝ) / 2 ^ P / 2 ^ (2 * e + 1) := by
          rw [show (2 : ℝ) ^ (2 * e + 1) = 2 ^ e * 2 ^ e * 2 by rw [pow_succ, two_mul, pow_add]]; field_simp
      _ ≤ _ := this
  have hlt' : ((f.hi + b.1 + (Ball.cdiv (Ball.add f1 b.2.1).absHi (2 ^ e) : ℕ) +
      (Ball.cdiv (m + b.2.2) (2 ^ (2 * e + 1)) : ℕ) + (d : ℤ) : ℤ) : ℝ) < target := by exact_mod_cast hlt
  push_cast at hlt'
  have hsum : (f.hi : ℝ) / 2 ^ P + (b.1 : ℝ) / 2 ^ P + (Ball.cdiv (Ball.add f1 b.2.1).absHi (2 ^ e) : ℝ) / 2 ^ P +
      (Ball.cdiv (m + b.2.2) (2 ^ (2 * e + 1)) : ℝ) / 2 ^ P + (d : ℝ) / 2 ^ P < (target : ℝ) / 2 ^ P := by
    rw [← add_div, ← add_div, ← add_div, ← add_div]; exact div_lt_div_of_pos_right hlt' hP
  have hC : fsum C t = fsum (cens mp) t + fsum cen t := fsum_append _ _ _
  have hCtc : fsum C tc = fsum (cens mp) tc + fsum cen tc := fsum_append _ _ _
  have ha := i4 t ht ht2
  have hb' := k1 t ht ht2
  push_cast at h2
  nlinarith [hT, hf, h1, h2, k2]

/-! ### The cell tree -/

theorem cellsD_ok (target : ℤ) : ∀ (fuel skip e : ℕ) (tn : ℤ) (mp : List DTerm) (gp : List (List DTerm)) (tc : ℝ),
    tc = (tn : ℝ) / 2 ^ e →
    cellsD P target fuel skip e tn (mp.map Prod.snd) (gp.map (·.map Prod.snd)) = true →
    (∀ p ∈ mp, DOK P tc e p) → (∀ G ∈ gp, ∀ p ∈ G, DOK P tc e p) →
    (∀ p ∈ mp, fuel ≤ p.2.st.length + 1) → (∀ G ∈ gp, ∀ p ∈ G, fuel ≤ p.2.st.length + 1) →
    CellBound P target tc e mp gp
  | 0, _, _, _, _, _, _, _, h, _, _, _, _ => by simp [cellsD] at h
  | fuel + 1, skip, e, tn, mp, gp, tc, htc, h, hmp, hgp, hlen, hglen => by
    unfold cellsD at h
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨_, hc⟩ | ⟨hd, hu⟩
    · exact cellOKD_ok htc hc hmp hgp
    · cases fuel with
      | zero => simp [cellsD] at hd
      | succ f =>
        have hne : ∀ p ∈ mp, p.2.st ≠ [] := by
          intro p hp h0; have := hlen p hp; rw [h0] at this; simp at this
        have hgne : ∀ G ∈ gp, ∀ p ∈ G, p.2.st ≠ [] := by
          intro G hG p hp h0; have := hglen G hG p hp; rw [h0] at this; simp at this
        set stp : Bool → DTerm → DTerm := fun down p => (p.1, stepD P down p.2)
        have hmap : ∀ down : Bool, (mp.map Prod.snd).map (stepD P down) = (mp.map (stp down)).map Prod.snd := by
          intro down; simp [stp, List.map_map, Function.comp_def]
        have hgmap : ∀ down : Bool, (gp.map (·.map Prod.snd)).map (·.map (stepD P down)) =
            (gp.map (·.map (stp down))).map (·.map Prod.snd) := by
          intro down; simp [stp, List.map_map, Function.comp_def]
        have hok : ∀ down : Bool, ∀ p, DOK P tc e p → p.2.st ≠ [] →
            DOK P (if down then tc - 1 / 2 ^ (e + 1) else tc + 1 / 2 ^ (e + 1)) (e + 1) (stp down p) :=
          fun down p hp hp' => stepD_ok hp hp' down
        have hlenS : ∀ down : Bool, ∀ p, f + 1 + 1 ≤ p.2.st.length + 1 → p.2.st ≠ [] →
            f + 1 ≤ (stp down p).2.st.length + 1 := by
          intro down p h1 h2; have := stepD_len (P := P) h2 down; simp only [stp]; omega
        have hch : ∀ down : Bool, CellBound P target (if down then tc - 1 / 2 ^ (e + 1) else tc + 1 / 2 ^ (e + 1))
            (e + 1) (mp.map (stp down)) (gp.map (·.map (stp down))) := by
          intro down
          refine cellsD_ok target (f + 1) (skip - 1) (e + 1) (if down then 2 * tn - 1 else 2 * tn + 1) _ _ _ ?_ ?_
            ?_ ?_ ?_ ?_
          · rw [htc]; cases down <;> simp <;> push_cast <;> rw [pow_succ] <;> field_simp <;> ring
          · rw [← hmap, ← hgmap]; cases down
            · simpa using hu
            · simpa using hd
          · intro q hq; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq; exact hok down p (hmp p hp) (hne p hp)
          · intro G' hG' q hq
            obtain ⟨G, hG, rfl⟩ := List.mem_map.1 hG'
            obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
            exact hok down p (hgp G hG p hp) (hgne G hG p hp)
          · intro q hq; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq; exact hlenS down p (hlen p hp) (hne p hp)
          · intro G' hG' q hq
            obtain ⟨G, hG, rfl⟩ := List.mem_map.1 hG'
            obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
            exact hlenS down p (hglen G hG p hp) (hgne G hG p hp)
        -- the semantic lists are unchanged by the steps
        have hz : ∀ down : Bool, ∀ zm : List ℂ,
            List.Forall₂ (fun z (p : DTerm) => ‖z - p.1.2.1‖ ≤ p.1.2.2) zm mp →
            List.Forall₂ (fun z (p : DTerm) => ‖z - p.1.2.1‖ ≤ p.1.2.2) zm (mp.map (stp down)) := by
          intro down zm hzm
          rw [List.forall₂_map_right_iff]; exact hzm
        have hs : ∀ down : Bool, ∀ sel : List (ℂ × ℂ),
            List.Forall₂ (fun (cz : ℂ × ℂ) (G : List DTerm) => ∃ p ∈ G, cz.1 = p.1.1 ∧ ‖cz.2 - p.1.2.1‖ ≤ p.1.2.2)
              sel gp →
            List.Forall₂ (fun (cz : ℂ × ℂ) (G : List DTerm) => ∃ p ∈ G, cz.1 = p.1.1 ∧ ‖cz.2 - p.1.2.1‖ ≤ p.1.2.2)
              sel (gp.map (·.map (stp down))) := by
          intro down sel hsel
          rw [List.forall₂_map_right_iff]
          refine hsel.imp (fun cz G ⟨p, hp, h1, h2⟩ => ⟨stp down p, List.mem_map_of_mem hp, h1, h2⟩)
        have hzip : ∀ down : Bool, ∀ zm : List ℂ,
            List.zipWith (fun z (p : DTerm) => (p.1.1, z)) zm (mp.map (stp down)) =
              List.zipWith (fun z (p : DTerm) => (p.1.1, z)) zm mp := by
          intro down zm; rw [List.zipWith_map_right]
        intro zm hzm sel hsel t ht ht2
        rcases le_total t tc with htc' | htc'
        · have := hch true zm (hz true zm hzm) sel (hs true sel hsel) t ⟨?_, ?_⟩ ht2
          · rwa [hzip] at this
          · simp only [if_true]; rw [pow_succ]; linarith [ht.1, show (1 : ℝ) / 2 ^ e = 1 / (2 ^ e * 2) * 2 by
              field_simp]
          · simp only [if_true]; rw [pow_succ]; linarith [show (1 : ℝ) / 2 ^ e = 1 / (2 ^ e * 2) * 2 by field_simp]
        · have := hch false zm (hz false zm hzm) sel (hs false sel hsel) t ⟨?_, ?_⟩ ht2
          · rwa [hzip] at this
          · simp only [Bool.false_eq_true, if_false]; rw [pow_succ]
            linarith [show (1 : ℝ) / 2 ^ e = 1 / (2 ^ e * 2) * 2 by field_simp]
          · simp only [Bool.false_eq_true, if_false]; rw [pow_succ]
            linarith [ht.2, show (1 : ℝ) / 2 ^ e = 1 / (2 ^ e * 2) * 2 by field_simp]

theorem tboundD_ok {D : ℕ} {target : ℤ} {mp : List DTerm} {gp : List (List DTerm)}
    (h : tboundD P D (mp.map Prod.snd) (gp.map (·.map Prod.snd)) target = true)
    (hmp : ∀ p ∈ mp, DOK P 0 1 p) (hgp : ∀ G ∈ gp, ∀ p ∈ G, DOK P 0 1 p)
    (hlen : ∀ p ∈ mp, p.2.st.length = D) (hglen : ∀ G ∈ gp, ∀ p ∈ G, p.2.st.length = D) :
    ∀ (zm : List ℂ), List.Forall₂ (fun z (p : DTerm) => ‖z - p.1.2.1‖ ≤ p.1.2.2) zm mp →
    ∀ (sel : List (ℂ × ℂ)),
      List.Forall₂ (fun (cz : ℂ × ℂ) (G : List DTerm) => ∃ p ∈ G, cz.1 = p.1.1 ∧ ‖cz.2 - p.1.2.1‖ ≤ p.1.2.2) sel gp →
    ∀ t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2),
      fsum (List.zipWith (fun z (p : DTerm) => (p.1.1, z)) zm mp) t + fsum sel t < (target : ℝ) / 2 ^ P := by
  intro zm hzm sel hsel t ht
  refine cellsD_ok target (D + 1) 4 1 0 mp gp 0 (by simp) h hmp hgp (fun p hp => by rw [hlen p hp])
    (fun G hG p hp => by rw [hglen G hG p hp]) zm hzm sel hsel t ?_ ?_
  · norm_num at ht ⊢; exact ht
  · rw [abs_le]; constructor <;> linarith [ht.1, ht.2]

end C64Chk
