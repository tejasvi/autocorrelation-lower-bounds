import Mathlib
import C64K.KNest
import C64K.KPieceGood

/-!
# Every t-piece of a tile is `some` (for the lazy tube data of the 4/3 kernel port)

`tPiece_isSome`: for the glob constants (`P = 80`, `n = 18`, `k = 3`, `D = 23`), every tile ellipse within the size bounds
`tileB` (one `decide` per tile) and every piece `n0 < n1 ≤ 2^e`, `e + 1 ≤ P`, the kernel port's `tPiece` is `some`.

Method: interval bounds on the balls ("abstract interpretation"). `In a B` says that the ball `a` has magnitude `≤ B.M` and
radius `≤ B.R`; every kernel ball operation maps bounded inputs to outputs bounded by an explicit `Bd` function of the input
bounds (monotone). The guards on `tPiece`'s path (`expSmall`, `cosSinSmall` via `expB` and `cosSinTurn`) then follow from
closed numeric inequalities on these bounds, checked by `decide`.
-/

namespace C64KPiece

open KIval KIval.KBall KNum C64KChk

/-! ## Raw `Nat` functions as operators -/

theorem raw_add (a b : Nat) : Nat.add a b = a + b := rfl
theorem raw_sub (a b : Nat) : Nat.sub a b = a - b := rfl
theorem raw_mul (a b : Nat) : Nat.mul a b = a * b := rfl
theorem raw_div (a b : Nat) : Nat.div a b = a / b := rfl
theorem raw_pow (a b : Nat) : Nat.pow a b = a ^ b := rfl

/-! ## Bounds -/

/-- Upper bounds on the magnitude (`M`) and the radius (`R`) of a ball. -/
structure Bd where
  M : Nat
  R : Nat
deriving Repr, DecidableEq

/-- The ball `a` satisfies the bounds `B`. -/
def In (a : KBall) (B : Bd) : Prop := a.m ≤ B.M ∧ a.r ≤ B.R

theorem div_add_le (m a d : Nat) (ha : a ≤ d) : (m + a) / d ≤ m / d + 1 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · calc (m + a) / d ≤ (m + d) / d := Nat.div_le_div_right (by omega)
      _ = m / d + 1 := Nat.add_div_right m hd

theorem cdiv_mono {n n' : Nat} (d : Nat) (h : n ≤ n') : KBall.cdiv n d ≤ KBall.cdiv n' d := by
  unfold KBall.cdiv
  simp only [raw_add, raw_sub, raw_div]
  exact Nat.div_le_div_right (by omega)

theorem cdiv_le (n d : Nat) : KBall.cdiv n d ≤ n / d + 1 := by
  unfold KBall.cdiv
  simp only [raw_add, raw_sub, raw_div]
  calc (n + d - 1) / d ≤ (n + d) / d := Nat.div_le_div_right (by omega)
    _ ≤ n / d + 1 := div_add_le n d d (Nat.le_refl _)

/-! ## Elementary operations -/

theorem rndD_m (s : Bool) (m d r : Nat) : (rndD s m d r).m ≤ m / d + 1 := by
  have h1 : (m + d / 2) / d ≤ m / d + 1 := div_add_le m (d / 2) d (Nat.div_le_self d 2)
  have h2 : (m + d - (d / 2 + 1)) / d ≤ m / d + 1 :=
    Nat.le_trans (Nat.div_le_div_right (Nat.sub_le _ _)) (div_add_le m d d (Nat.le_refl _))
  unfold rndD
  cases s
  · simpa only [Bool.cond_false, raw_add, raw_div] using h1
  · simp only [Bool.cond_true]
    cases Nat.ble m (Nat.div d 2)
    · simpa only [Bool.cond_false, raw_add, raw_sub, raw_div] using h2
    · simp

theorem rndD_r (s : Bool) (m d r : Nat) : (rndD s m d r).r = r := by
  unfold rndD
  cases s
  · rfl
  · simp only [Bool.cond_true]
    cases Nat.ble m (Nat.div d 2) <;> rfl

theorem sadd_m (s₁ : Bool) (a : Nat) (s₂ : Bool) (b r : Nat) : (sadd s₁ a s₂ b r).m ≤ a + b := by
  unfold sadd
  cases bx s₁ s₂
  · simp only [Bool.cond_false, raw_add]; exact (Nat.le_refl _)
  · simp only [Bool.cond_true]
    cases Nat.ble b a
    · simp only [Bool.cond_false, raw_sub]; omega
    · simp only [Bool.cond_true, raw_sub]; omega

theorem sadd_r (s₁ : Bool) (a : Nat) (s₂ : Bool) (b r : Nat) : (sadd s₁ a s₂ b r).r = r := by
  unfold sadd
  cases bx s₁ s₂
  · rfl
  · simp only [Bool.cond_true]
    cases Nat.ble b a <;> rfl

def Bd.add (A B : Bd) : Bd := ⟨A.M + B.M, A.R + B.R⟩

theorem add_in {a b : KBall} {A B : Bd} (ha : In a A) (hb : In b B) : In (KBall.add a b) (Bd.add A B) := by
  unfold KBall.add Bd.add In
  constructor
  · exact Nat.le_trans (sadd_m _ _ _ _ _) (Nat.add_le_add ha.1 hb.1)
  · rw [sadd_r]; simp only [raw_add]; exact Nat.add_le_add ha.2 hb.2

theorem sub_in {a b : KBall} {A B : Bd} (ha : In a A) (hb : In b B) : In (KBall.sub a b) (Bd.add A B) := by
  unfold KBall.sub Bd.add In
  constructor
  · exact Nat.le_trans (sadd_m _ _ _ _ _) (Nat.add_le_add ha.1 hb.1)
  · rw [sadd_r]; simp only [raw_add]; exact Nat.add_le_add ha.2 hb.2

theorem neg_in {a : KBall} {A : Bd} (ha : In a A) : In (KBall.neg a) A := ha

/-- Bounds of a product at precision `P`. -/
def Bd.mul (P : Nat) (A B : Bd) : Bd :=
  ⟨A.M * B.M / 2 ^ P + 1, KBall.cdiv (A.M * B.R + B.M * A.R + A.R * B.R) (2 ^ P) + 1⟩

theorem mul_in (P : Nat) {a b : KBall} {A B : Bd} (ha : In a A) (hb : In b B) :
    In (KBall.mul P a b) (Bd.mul P A B) := by
  unfold KBall.mul Bd.mul In
  simp only []
  constructor
  · refine Nat.le_trans (rndD_m _ _ _ _) ?_
    simp only [raw_mul, raw_pow]
    exact Nat.add_le_add_right (Nat.div_le_div_right (Nat.mul_le_mul ha.1 hb.1)) 1
  · rw [rndD_r]
    simp only [raw_add, raw_mul, raw_pow]
    refine Nat.add_le_add_right (cdiv_mono _ ?_) 1
    exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul ha.1 hb.2) (Nat.mul_le_mul hb.1 ha.2))
      (Nat.mul_le_mul ha.2 hb.2)

def Bd.mulInt (n : Nat) (A : Bd) : Bd := ⟨n * A.M, n * A.R⟩

theorem mulInt_in (s : Bool) (n : Nat) {a : KBall} {A : Bd} (ha : In a A) :
    In (KBall.mulInt s n a) (Bd.mulInt n A) := by
  unfold KBall.mulInt Bd.mulInt In
  simp only [raw_mul]
  exact ⟨Nat.mul_le_mul_left n ha.1, Nat.mul_le_mul_left n ha.2⟩

def Bd.shr (k : Nat) (A : Bd) : Bd := ⟨A.M / 2 ^ k + 1, KBall.cdiv A.R (2 ^ k) + 1⟩

theorem shr_in (k : Nat) {a : KBall} {A : Bd} (ha : In a A) : In (KBall.shr k a) (Bd.shr k A) := by
  unfold KBall.shr Bd.shr In
  simp only []
  constructor
  · refine Nat.le_trans (rndD_m _ _ _ _) ?_
    simp only [raw_pow]
    exact Nat.add_le_add_right (Nat.div_le_div_right ha.1) 1
  · rw [rndD_r]
    simp only [raw_add, raw_pow]
    exact Nat.add_le_add_right (cdiv_mono _ ha.2) 1

def Bd.divNat (d : Nat) (A : Bd) : Bd := ⟨A.M / d + 1, KBall.cdiv A.R d + 1⟩

theorem divNat_in (d : Nat) {a : KBall} {A : Bd} (ha : In a A) : In (KBall.divNat d a) (Bd.divNat d A) := by
  unfold KBall.divNat Bd.divNat In
  constructor
  · exact Nat.le_trans (rndD_m _ _ _ _) (Nat.add_le_add_right (Nat.div_le_div_right ha.1) 1)
  · rw [rndD_r]
    simp only [raw_add]
    exact Nat.add_le_add_right (cdiv_mono _ ha.2) 1

theorem absHi_le {a : KBall} {A : Bd} (ha : In a A) : absHi a ≤ A.M + A.R := by
  unfold absHi
  simp only [raw_add]
  exact Nat.add_le_add ha.1 ha.2

/-! ## Taylor sums, `cosSinSmall`, doublings -/

theorem addsub_in (c : Bool) {a b : KBall} {A B : Bd} (ha : In a A) (hb : In b B) :
    In (cond c (KBall.sub a b) (KBall.add a b)) (Bd.add A B) := by
  cases c
  · exact add_in ha hb
  · exact sub_in ha hb

/-- Bounds of `taylorAux` (same recursion). -/
def TBd (P : Nat) (X : Bd) : Nat → Nat → Bd → Bd → Bd → Bd × Bd
  | 0, _, _, EV, OD => (EV, OD)
  | fuel + 1, j, T, EV, OD =>
    TBd P X fuel (j + 1) (Bd.divNat (j + 1) (Bd.mul P T X))
      (if j % 2 = 0 then Bd.add EV T else EV) (if j % 2 = 1 then Bd.add OD T else OD)

theorem taylorAux_in (P : Nat) (alt : Bool) {x : KBall} {X : Bd} (hx : In x X) :
    ∀ fuel j t ev od T EV OD, In t T → In ev EV → In od OD →
      In (taylorAux P alt x fuel j t ev od).1 (TBd P X fuel j T EV OD).1 ∧
      In (taylorAux P alt x fuel j t ev od).2 (TBd P X fuel j T EV OD).2 := by
  intro fuel
  induction fuel with
  | zero => intro j t ev od T EV OD _ hev hod; exact ⟨hev, hod⟩
  | succ fuel ih =>
    intro j t ev od T EV OD ht hev hod
    have ht' : In (divNat (Nat.add j 1) (KBall.mul P t x)) (Bd.divNat (j + 1) (Bd.mul P T X)) :=
      divNat_in (j + 1) (mul_in P ht hx)
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · have hev' := addsub_in (cond alt (Nat.beq (Nat.mod j 4) 2) false) hev ht
      have := ih (Nat.add j 1) _ _ od _ _ OD ht' hev' hod
      simp only [taylorAux, TBd, show Nat.mod j 2 = j % 2 from rfl, h, show Nat.beq 0 0 = true from rfl,
        show Nat.beq 0 1 = false from rfl, Bool.cond_true, Bool.cond_false, ite_true,
        show ((0 : Nat) = 1) = False from by simp, ite_false] at this ⊢
      exact this
    · have hod' := addsub_in (cond alt (Nat.beq (Nat.mod j 4) 3) false) hod ht
      have := ih (Nat.add j 1) _ ev _ _ EV _ ht' hev hod'
      simp only [taylorAux, TBd, show Nat.mod j 2 = j % 2 from rfl, h, show Nat.beq 1 0 = false from rfl,
        show Nat.beq 1 1 = true from rfl, Bool.cond_true, Bool.cond_false, ite_true,
        show ((1 : Nat) = 0) = False from by simp, ite_false] at this ⊢
      exact this

theorem remBound_mono (P n : Nat) {h h' : Nat} (hh : h ≤ h') : remBound P n h ≤ remBound P n h' := by
  unfold remBound
  simp only [raw_mul, raw_pow, raw_add]
  exact cdiv_mono _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hh n))

/-- Bounds of the two outputs of `cosSinSmall` for `θ` within `Θ`. -/
def csSmallBd (P n : Nat) (Θ : Bd) : Bd × Bd :=
  let eo := TBd P Θ n 0 ⟨2 ^ P, 0⟩ ⟨0, 0⟩ ⟨0, 0⟩
  (⟨eo.1.M, eo.1.R + remBound P n (Θ.M + Θ.R)⟩, ⟨eo.2.M, eo.2.R + remBound P n (Θ.M + Θ.R)⟩)

theorem cosSinSmall_spec {P n : Nat} {θ : KBall} {Θ : Bd} (hθ : In θ Θ) (hn : 0 < n) (hg : Θ.M + Θ.R ≤ 2 ^ P) :
    ∃ cs, cosSinSmall P n θ = some cs ∧ In cs.1 (csSmallBd P n Θ).1 ∧ In cs.2 (csSmallBd P n Θ).2 := by
  have hab := absHi_le hθ
  have g1 : Nat.ble (absHi θ) (Nat.pow 2 P) = true := by
    simp only [Nat.ble_eq, raw_pow]; omega
  have g2 : blt 0 n = true := by
    simp only [blt, Nat.ble_eq, raw_add]; omega
  have h1 : In (ofInt P false 1) ⟨2 ^ P, 0⟩ := by
    simp only [In, ofInt, raw_mul, raw_pow]; omega
  have h0 : In ⟨false, 0, 0⟩ ⟨0, 0⟩ := ⟨Nat.le_refl _, Nat.le_refl _⟩
  have ht := taylorAux_in P true hθ n 0 _ _ _ _ _ _ h1 h0 h0
  have hr := remBound_mono P n hab
  refine ⟨_, by simp only [cosSinSmall, g1, g2, Bool.cond_true]; rfl, ?_, ?_⟩
  · exact ⟨ht.1.1, by simp only [raw_add]; exact Nat.add_le_add ht.1.2 hr⟩
  · exact ⟨ht.2.1, by simp only [raw_add]; exact Nat.add_le_add ht.2.2 hr⟩

/-- Bounds of `dblIter` (same recursion). -/
def DBd (P : Nat) : Nat → Bd × Bd → Bd × Bd
  | 0, CS => CS
  | k + 1, CS => DBd P k (Bd.add (Bd.mul P CS.1 CS.1) (Bd.mul P CS.2 CS.2), Bd.mulInt 2 (Bd.mul P CS.1 CS.2))

theorem dblIter_in (P : Nat) : ∀ k (cs : KBall × KBall) (CS : Bd × Bd), In cs.1 CS.1 → In cs.2 CS.2 →
    In (dblIter P k cs).1 (DBd P k CS).1 ∧ In (dblIter P k cs).2 (DBd P k CS).2 := by
  intro k
  induction k with
  | zero => intro cs CS h1 h2; exact ⟨h1, h2⟩
  | succ k ih =>
    intro cs CS h1 h2
    exact ih _ _ (sub_in (mul_in P h1 h1) (mul_in P h2 h2)) (mulInt_in false 2 (mul_in P h1 h2))

/-! ## Angles in turns -/

theorem fracTurn_in (P : Nat) {u : KBall} {R : Nat} (hr : u.r ≤ R) : In (fracTurn P u) ⟨2 ^ P / 2, R⟩ := by
  have hd : 0 < 2 ^ P := Nat.two_pow_pos P
  unfold fracTurn In
  simp only [raw_pow, raw_mul]
  refine ⟨?_, by rw [sadd_r]; exact hr⟩
  generalize 2 ^ P = d at hd ⊢
  cases hs : u.s
  · -- centre `≥ 0`: nearest integer `Q = (m + d/2) / d`
    simp only [rndD, Bool.cond_false, raw_add, raw_div]
    have h1 := Nat.div_mul_le_self (u.m + d / 2) d
    have h2 := Nat.lt_div_mul_add (a := u.m + d / 2) hd
    generalize (u.m + d / 2) / d = Q at h1 h2
    simp only [sadd, bx, Bool.cond_false, Bool.cond_true, raw_sub, raw_add]
    generalize hX : Q * d = X at h1 h2
    cases hb : Nat.ble X u.m
    · simp only [Bool.cond_false]; rw [← Bool.not_eq_true, Nat.ble_eq] at hb; omega
    · simp only [Bool.cond_true]; simp only [Nat.ble_eq] at hb; omega
  · simp only [rndD, Bool.cond_true, raw_add, raw_sub, raw_div]
    cases hb : Nat.ble u.m (d / 2)
    · simp only [Bool.cond_false]
      rw [← Bool.not_eq_true, Nat.ble_eq] at hb
      have h1 := Nat.div_mul_le_self (u.m + d - (d / 2 + 1)) d
      have h2 := Nat.lt_div_mul_add (a := u.m + d - (d / 2 + 1)) hd
      generalize (u.m + d - (d / 2 + 1)) / d = Q at h1 h2
      simp only [sadd, bx, Bool.cond_false, Bool.cond_true, raw_sub, raw_add]
      generalize hX : Q * d = X at h1 h2
      cases hb2 : Nat.ble X u.m
      · simp only [Bool.cond_false]; rw [← Bool.not_eq_true, Nat.ble_eq] at hb2; omega
      · simp only [Bool.cond_true]; simp only [Nat.ble_eq] at hb2; omega
    · simp only [Bool.cond_true]
      simp only [Nat.ble_eq] at hb
      simp only [sadd, bx, Bool.cond_false, Bool.cond_true, raw_add]
      omega

/-- Bounds of `turnArg P k u` for `u.r ≤ R`, given bounds `PIB` of `piB P`. -/
def taBd (P k : Nat) (PIB : Bd) (R : Nat) : Bd := Bd.shr k (Bd.mul P (Bd.mulInt 2 PIB) ⟨2 ^ P / 2, R⟩)

theorem turnArg_in {P k : Nat} {u : KBall} {R : Nat} {PIB : Bd} (hpi : In (piB P) PIB) (hr : u.r ≤ R) :
    In (turnArg P k u) (taBd P k PIB R) :=
  shr_in k (mul_in P (mulInt_in false 2 hpi) (fracTurn_in P hr))

/-- Bounds of the outputs of `cosSinTurn P n k u` for `u.r ≤ R`. -/
def ctBd (P n k : Nat) (PIB : Bd) (R : Nat) : Bd × Bd := DBd P k (csSmallBd P n (taBd P k PIB R))

theorem cosSinTurn_spec {P n k : Nat} {u : KBall} {R : Nat} {PIB : Bd} (hpi : In (piB P) PIB) (hr : u.r ≤ R)
    (hn : 0 < n) (hg : (taBd P k PIB R).M + (taBd P k PIB R).R ≤ 2 ^ P) :
    ∃ cs, cosSinTurn P n k u = some cs ∧ In cs.1 (ctBd P n k PIB R).1 ∧ In cs.2 (ctBd P n k PIB R).2 := by
  obtain ⟨cs0, h0, h1, h2⟩ := cosSinSmall_spec (turnArg_in (k := k) hpi hr) hn hg
  refine ⟨dblIter P k cs0, by simp only [cosSinTurn, h0, Option.map_some], ?_⟩
  exact dblIter_in P k cs0 _ h1 h2

/-- `cosSinTurnC` adds `w = ⌈6.2832 u.r⌉` to both radii of `cosSinTurn` at the centre. -/
def widen (W : Nat) (CS : Bd × Bd) : Bd × Bd := (⟨CS.1.M, CS.1.R + W⟩, ⟨CS.2.M, CS.2.R + W⟩)

theorem cosSinTurnC_spec {P n k : Nat} {u : KBall} {PIB : Bd} {RU : Nat} (hpi : In (piB P) PIB) (hru : u.r ≤ RU)
    (hn : 0 < n) (hg : (taBd P k PIB 0).M + (taBd P k PIB 0).R ≤ 2 ^ P) :
    ∃ cs, cosSinTurnC P n k u = some cs ∧
      In cs.1 (widen (KBall.cdiv (RU * 62832) 10000) (ctBd P n k PIB 0)).1 ∧
      In cs.2 (widen (KBall.cdiv (RU * 62832) 10000) (ctBd P n k PIB 0)).2 := by
  obtain ⟨cs, h0, h1, h2⟩ := cosSinTurn_spec (u := ⟨u.s, u.m, 0⟩) hpi (Nat.le_refl 0) hn hg
  have hw : KBall.cdiv (Nat.mul u.r 62832) 10000 ≤ KBall.cdiv (RU * 62832) 10000 :=
    cdiv_mono _ (by simp only [raw_mul]; exact Nat.mul_le_mul_right _ hru)
  refine ⟨_, by simp only [cosSinTurnC, h0, Option.map_some]; rfl, ?_, ?_⟩
  · exact ⟨h1.1, by simp only [widen, raw_add]; exact Nat.add_le_add h1.2 hw⟩
  · exact ⟨h2.1, by simp only [widen, raw_add]; exact Nat.add_le_add h2.2 hw⟩

/-! ## `exp`: the guard of `expSmall` after `findShift` -/

theorem findShift_spec (P h : Nat) :
    ∀ fuel k, 2 * h ≤ 2 ^ (P + k + fuel) → 2 * h ≤ 2 ^ (P + findShift P h fuel k) := by
  intro fuel
  induction fuel with
  | zero => intro k hk; simpa [findShift] using hk
  | succ fuel ih =>
    intro k hk
    unfold findShift
    cases hb : Nat.ble (Nat.mul 2 h) (Nat.pow 2 (Nat.add P k))
    · simp only [Bool.cond_false]
      exact ih (Nat.add k 1) (by simp only [raw_add]; rw [show P + (k + 1) + fuel = P + k + (fuel + 1) by omega]; exact hk)
    · simp only [Bool.cond_true]
      simpa only [Nat.ble_eq, raw_mul, raw_pow, raw_add] using hb

theorem shr_absHi {P k : Nat} {x : KBall} (hP : 3 ≤ P) (hx : 2 * absHi x ≤ 2 ^ (P + k)) :
    absHi (KBall.shr k x) ≤ 2 ^ P := by
  have h2 := absHi_le (shr_in k (A := ⟨x.m, x.r⟩) ⟨Nat.le_refl _, Nat.le_refl _⟩)
  simp only [Bd.shr] at h2
  have h3 := cdiv_le x.r (2 ^ k)
  have h4 : x.m / 2 ^ k + x.r / 2 ^ k ≤ (x.m + x.r) / 2 ^ k := Nat.div_add_div_le_add_div
  have habs : absHi x = x.m + x.r := rfl
  obtain ⟨Q, rfl⟩ : ∃ Q, P = Q + 3 := ⟨P - 3, by omega⟩
  have hpow : 2 ^ (Q + 3 + k) = 2 ^ k * (8 * 2 ^ Q) := by rw [pow_add, pow_add]; ring
  have h5 : (x.m + x.r) / 2 ^ k ≤ 4 * 2 ^ Q := by
    apply Nat.div_le_of_le_mul
    rw [hpow] at hx
    nlinarith
  have h6 : 2 ^ (Q + 3) = 8 * 2 ^ Q := by rw [pow_add]; ring
  have h7 : 1 ≤ 2 ^ Q := Nat.one_le_two_pow
  omega

theorem expSmall_isSome {P n : Nat} {x : KBall} (hn : 0 < n) (hx : absHi x ≤ 2 ^ P) : (expSmall P n x).isSome := by
  have g1 : Nat.ble (absHi x) (Nat.pow 2 P) = true := by simp only [Nat.ble_eq, raw_pow]; exact hx
  have g2 : blt 0 n = true := by simp only [blt, Nat.ble_eq, raw_add]; omega
  simp only [expSmall, g1, g2, Bool.cond_true, Option.isSome_some]

theorem expB_isSome {P n : Nat} {x : KBall} (hP : 3 ≤ P) (hn : 0 < n) (hx : absHi x ≤ 2 ^ (P + 62)) :
    (expB P n x).isSome := by
  have hf := findShift_spec P (absHi x) 64 0 (by
    have : 2 ^ (P + 0 + 64) = 4 * 2 ^ (P + 62) := by rw [show P + 0 + 64 = (P + 62) + 2 by omega, pow_add]; ring
    omega)
  unfold expB
  simp only [Option.isSome_map]
  exact expSmall_isSome hn (shr_absHi hP hf)

theorem expPiHi_isSome {P n k Y YB : Nat} {PIB : Bd} (hpi : In (piB P) PIB) (hP : 3 ≤ P) (hn : 0 < n)
    (hY : Y ≤ YB) (hg : (Bd.mul P PIB ⟨YB, 0⟩).M + (Bd.mul P PIB ⟨YB, 0⟩).R ≤ 2 ^ (P + 62)) :
    (expPiHi ⟨P, n, k⟩ Y).isSome := by
  have h := absHi_le (mul_in P hpi (b := ⟨false, Y, 0⟩) (B := ⟨YB, 0⟩) ⟨hY, Nat.le_refl 0⟩)
  unfold expPiHi
  simp only [Option.isSome_map]
  exact expB_isSome hP hn (Nat.le_trans h hg)

/-! ## The functions on `tPiece`'s path -/

theorem ckt_isSome {P n k : Nat} {t : KBall} {z : KCBall} {T ZRE ZIM PIB : Bd} (hpi : In (piB P) PIB)
    (ht : In t T) (hre : In z.re ZRE) (him : In z.im ZIM) (hP : 3 ≤ P) (hn : 0 < n)
    (hex : (Bd.mul P (Bd.mulInt 2 (Bd.mul P PIB T)) ZIM).M +
      (Bd.mul P (Bd.mulInt 2 (Bd.mul P PIB T)) ZIM).R ≤ 2 ^ (P + 62))
    (hg : (taBd P k PIB (Bd.mul P T ZRE).R).M + (taBd P k PIB (Bd.mul P T ZRE).R).R ≤ 2 ^ P) :
    (ckt ⟨P, n, k⟩ t z).isSome := by
  have hx := absHi_le (mul_in P (mulInt_in false 2 (mul_in P hpi ht)) him)
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp (expB_isSome (n := n) hP hn (Nat.le_trans hx hex))
  obtain ⟨cs, hcs, -, -⟩ := cosSinTurn_spec (n := n) (k := k) hpi (mul_in P ht hre).2 hn hg
  unfold ckt
  simp only [he, hcs, Option.bind_some, Option.map_some, Option.isSome_some]

theorem ellPt_spec {P n k : Nat} {E : EllB} {U : KBall} {R : Nat} {CR CI A B PIB : Bd} (hpi : In (piB P) PIB)
    (hcr : In E.cr CR) (hci : In E.ci CI) (ha : In E.a A) (hb : In E.b B) (hr : U.r ≤ R) (hn : 0 < n)
    (hg : (taBd P k PIB R).M + (taBd P k PIB R).R ≤ 2 ^ P) :
    ∃ z, ellPt ⟨P, n, k⟩ E U = some z ∧ In z.re (Bd.add CR (Bd.mul P A (ctBd P n k PIB R).1)) ∧
      In z.im (Bd.add CI (Bd.mul P B (ctBd P n k PIB R).2)) := by
  obtain ⟨cs, hcs, h1, h2⟩ := cosSinTurn_spec (n := n) (k := k) hpi hr hn hg
  refine ⟨_, by simp only [ellPt, hcs, Option.map_some]; rfl, add_in hcr (mul_in P ha h1), add_in hci (mul_in P hb h2)⟩

/-- The bound of `ellSp` (with the cosines widened for a piece of radius `≤ RU`). -/
def spBd (P n k : Nat) (A B PIB : Bd) (RU : Nat) : Nat :=
  sqrtHi (((A.M + A.R) * ((widen (KBall.cdiv (RU * 62832) 10000) (ctBd P n k PIB 0)).2.M +
      (widen (KBall.cdiv (RU * 62832) 10000) (ctBd P n k PIB 0)).2.R)) ^ 2 +
    ((B.M + B.R) * ((widen (KBall.cdiv (RU * 62832) 10000) (ctBd P n k PIB 0)).1.M +
      (widen (KBall.cdiv (RU * 62832) 10000) (ctBd P n k PIB 0)).1.R)) ^ 2)

theorem ellSp_spec {P n k : Nat} {E : EllB} {U : KBall} {RU : Nat} {A B PIB : Bd} (hpi : In (piB P) PIB)
    (ha : In E.a A) (hb : In E.b B) (hru : U.r ≤ RU) (hn : 0 < n)
    (hg : (taBd P k PIB 0).M + (taBd P k PIB 0).R ≤ 2 ^ P) :
    ∃ sp, ellSp ⟨P, n, k⟩ E U = some sp ∧ sp ≤ spBd P n k A B PIB RU := by
  obtain ⟨cs, hcs, h1, h2⟩ := cosSinTurnC_spec (n := n) (k := k) hpi hru hn hg
  refine ⟨_, by simp only [ellSp, hcs, Option.map_some]; rfl, ?_⟩
  unfold sqrtHi spBd sqrtHi
  simp only [raw_add, raw_pow, raw_mul]
  apply Nat.add_le_add_right
  apply Nat.sqrt_le_sqrt
  exact Nat.add_le_add (Nat.pow_le_pow_left (Nat.mul_le_mul (absHi_le ha) (absHi_le h2)) 2)
    (Nat.pow_le_pow_left (Nat.mul_le_mul (absHi_le hb) (absHi_le h1)) 2)

theorem ellRad_spec {P n k : Nat} {E : EllB} {n0 n1 e SPB : Nat} (hq1 : n1 ≤ 2 ^ e)
    (hsp : ∃ sp, ellSp ⟨P, n, k⟩ E (pieceB P n0 n1 e) = some sp ∧ sp ≤ SPB) :
    ∃ rho, ellRad ⟨P, n, k⟩ E n0 n1 e = some rho ∧ rho ≤ piHi P * SPB / 2 ^ (2 * P) + 1 := by
  obtain ⟨sp, hsp, hle⟩ := hsp
  refine ⟨_, by simp only [ellRad, hsp, Option.map_some]; rfl, ?_⟩
  simp only [raw_mul, raw_sub, raw_pow, raw_add]
  refine Nat.le_trans (cdiv_le _ _) (Nat.add_le_add_right ?_ 1)
  have he : 0 < 2 ^ e := Nat.two_pow_pos e
  calc piHi P * sp * (n1 - n0) / 2 ^ (2 * P + e)
      ≤ piHi P * SPB * 2 ^ e / 2 ^ (2 * P + e) := by
        apply Nat.div_le_div_right
        exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hle) (Nat.le_trans (Nat.sub_le _ _) hq1)
    _ = piHi P * SPB / 2 ^ (2 * P) := by rw [pow_add, Nat.mul_div_mul_right _ _ he]

theorem pieceB_r (P n0 n1 e : Nat) (he : e + 1 ≤ P) (hq1 : n1 ≤ 2 ^ e) : (pieceB P n0 n1 e).r ≤ 2 ^ (P - 1) := by
  simp only [pieceB, raw_mul, raw_sub, raw_pow, raw_add]
  calc (n1 - n0) * 2 ^ (P - (e + 1)) ≤ 2 ^ e * 2 ^ (P - (e + 1)) :=
        Nat.mul_le_mul_right _ (Nat.le_trans (Nat.sub_le _ _) hq1)
    _ = 2 ^ (P - 1) := by rw [← pow_add]; congr 1; omega

theorem ptT_isSome {P n k D : Nat} {z : KCBall}
    (h1 : (ckt ⟨P, n, k⟩ (dyB P 1 (Nat.add D 1)) z).isSome)
    (h2 : (ckt ⟨P, n, k⟩ (KBall.neg (dyB P 1 (Nat.add D 1))) z).isSome)
    (h3 : (expPiHi ⟨P, n, k⟩ (KBall.cdiv (absHi z.im) 16)).isSome) : (ptT ⟨P, n, k⟩ D z).isSome := by
  obtain ⟨kp, hkp⟩ := Option.isSome_iff_exists.mp h1
  obtain ⟨km, hkm⟩ := Option.isSome_iff_exists.mp h2
  obtain ⟨f0, hf0⟩ := Option.isSome_iff_exists.mp h3
  unfold ptT
  simp only [hkp, hkm, hf0, Option.bind_some, Option.map_some, Option.isSome_some]

theorem dzOf_isSome {P n k : Nat} {z : KCBall} {rho : Nat} (h1 : (expPiHi ⟨P, n, k⟩ rho).isSome)
    (h2 : (expPiHi ⟨P, n, k⟩ (KBall.cdiv (absHi z.im) 16)).isSome) : (dzOf ⟨P, n, k⟩ z rho).isSome := by
  obtain ⟨ex, hex⟩ := Option.isSome_iff_exists.mp h1
  obtain ⟨ey, hey⟩ := Option.isSome_iff_exists.mp h2
  unfold dzOf
  simp only [hex, hey, Option.bind_some, Option.map_some, Option.isSome_some]

/-! ## The glob constants and the closed numeric checks -/

/-- Bounds of `piB 80`. -/
abbrev PIB80 : Bd := ⟨3797952473636338580790843, 6046⟩

theorem piB80_in : In (piB 80) PIB80 := by unfold In; decide +kernel

/-- Tile bounds: `|cr| ≤ 16`, `|ci|, |a|, |b| ≤ 8` (units `2^-80`). -/
abbrev CRB : Bd := ⟨2 ^ 84, 2 ^ 84⟩
abbrev SB : Bd := ⟨2 ^ 83, 2 ^ 83⟩

-- `tileB` (the tile-size condition) is defined in C64K/KPieceGood.lean, so that the guard can evaluate it.

abbrev H80 : Bd := ⟨2 ^ 56, 0⟩

theorem tileB_in {E : EllB} (hE : tileB E = true) : In E.cr CRB ∧ In E.ci SB ∧ In E.a SB ∧ In E.b SB := by
  simp only [tileB, Bool.and_eq_true, Nat.ble_eq] at hE
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hE
  have e : ∀ a : KBall, absHi a = a.m + a.r := fun _ => rfl
  rw [e] at h1 h2 h3 h4
  simp only [In]
  omega

/-! ## Every t-piece is `some` -/

/-- **Every t-piece of a tile is `some`**, for the glob constants and any tile within `tileB`.
Every guard reduces to a closed inequality between the bound functions, decided by the kernel. -/
theorem tPiece_isSome (g : C64Chk.Glob) (E : EllB) (n0 n1 e : Nat) (hP : g.P = 80) (hn : g.n = 18) (hk : g.k = 3)
    (hD : g.D = 23) (hE : tileB E = true) (he : e + 1 ≤ g.P) (hq1 : n1 ≤ 2 ^ e) : (tPiece g E n0 n1 e).isSome := by
  obtain ⟨hcr, hci, ha, hb⟩ := tileB_in hE
  cases g
  simp only at hP hn hk hD he ⊢
  subst hP hn hk hD
  have hpi := piB80_in
  have hn0 : 0 < 18 := by decide
  have hP3 : 3 ≤ 80 := by decide
  obtain ⟨z, hz, hzre, hzim⟩ := ellPt_spec (P := 80) (n := 18) (k := 3) (U := midB 80 n0 n1 e) (R := 0) hpi hcr hci
    ha hb (Nat.le_refl 0) hn0 (by decide +kernel)
  have hsp := ellSp_spec (P := 80) (n := 18) (k := 3) (E := E) hpi ha hb (pieceB_r 80 n0 n1 e he hq1) hn0
    (by decide +kernel)
  obtain ⟨rho, hrho, hrhole⟩ := ellRad_spec (P := 80) (n := 18) (k := 3) hq1 hsp
  have hh : In (dyB 80 1 (Nat.add 23 1)) H80 := by unfold In; decide +kernel
  have hzim' := cdiv_mono 16 (absHi_le hzim)
  have hk1 := ckt_isSome (P := 80) (n := 18) (k := 3) hpi hh hzre hzim hP3 hn0 (by decide +kernel) (by decide +kernel)
  have hk2 := ckt_isSome (P := 80) (n := 18) (k := 3) hpi (neg_in hh) hzre hzim hP3 hn0 (by decide +kernel)
    (by decide +kernel)
  have hy := expPiHi_isSome (P := 80) (n := 18) (k := 3) hpi hP3 hn0 hzim' (by decide +kernel)
  have hr := expPiHi_isSome (P := 80) (n := 18) (k := 3) hpi hP3 hn0 hrhole (by decide +kernel)
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp (ptT_isSome (P := 80) (n := 18) (k := 3) (D := 23) hk1 hk2 hy)
  obtain ⟨dz, hdz⟩ := Option.isSome_iff_exists.mp (dzOf_isSome (P := 80) (n := 18) (k := 3) hr hy)
  unfold tPiece
  simp only [hz, hrho, hT, hdz, Option.bind_some, Option.map_some, Option.isSome_some]

/-! ## Helpers for the lazy tube data -/

/-- The pieces `subPc q0 q1 L i`, `i < 2^L`, of `[q0, q1] ⊆ [0, 2^EQ]` satisfy the hypothesis `n1 ≤ 2^e` of
`tPiece_isSome` with `e = EQ + L`. -/
theorem subPc_snd_le {q0 q1 L i EQ : Nat} (h01 : q0 ≤ q1) (hq1 : q1 ≤ 2 ^ EQ) (hi : i < 2 ^ L) :
    (subPc q0 q1 L i).2 ≤ 2 ^ (EQ + L) := by
  simp only [subPc, raw_add, raw_mul, raw_pow, raw_sub]
  have h1 : (i + 1) * (q1 - q0) ≤ 2 ^ L * (q1 - q0) := Nat.mul_le_mul_right _ hi
  have h2 : q0 * 2 ^ L + 2 ^ L * (q1 - q0) = q1 * 2 ^ L := by
    rw [Nat.mul_comm (2 ^ L), ← Nat.add_mul, Nat.add_sub_cancel' h01]
  have h3 : q1 * 2 ^ L ≤ 2 ^ EQ * 2 ^ L := Nat.mul_le_mul_right _ hq1
  rw [pow_add]
  omega

/-- `mapM` of a function that is `some` on every element is `some` of the mapped values. -/
theorem mapM_eq_some_map_get {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (h : ∀ a ∈ l, (f a).isSome),
      l.mapM f = some (l.attach.map fun x => (f x.1).get (h x.1 x.2)) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h a (List.mem_cons_self ..))
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.mapM_cons, hb, ih', Option.bind_eq_bind, Option.pure_def,
      List.attach_cons, List.map_cons, List.map_map]
    simp

end C64KPiece
