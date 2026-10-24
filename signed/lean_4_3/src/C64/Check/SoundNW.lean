import C64.Check.SoundNL

/-!
# Soundness of the nested checker, part 4: W1 records, tile arcs, W leaves and empty leaves

`checkTAPieceN_ok … taOKN_ok`: a W1 record gives the separation condition (`TileCondN`) at every point of its tile
arc; `walkTA_ok`: the W1 arcs and the hard arcs cover `[0, 1]`; `witLocalN_ok`: the W-leaf step (Lemma 6.9) given the
children of the hard arcs; `emptyN_ok`: an empty leaf.
-/

namespace C64Chk

open Ival Ival.Ball C64Num Real MeasureTheory

variable {P : ℕ}

/-- The separation condition at the parameter `q` of a tile for node sets with tubes. -/
def TileCondN (τ' : ℝ) (zc : ℂ) (r' : ℝ) (pq : List (ℂ × C64.Box)) (eps : ℝ) (tubes : List C64.TubeR)
    (cT : ℂ) (aT bT : ℝ) (q : ℝ) : Prop :=
  ∀ μ ν : Measure ℝ, C64.NodeSet τ' zc r' pq eps tubes μ → C64.NodeSet τ' zc r' pq eps tubes ν →
    ∀ θ ∈ Set.Icc (0 : ℝ) 1, C64.S (C64.ellipse cT aT bT q) -
      ((1 - θ) * C64.hat μ (C64.ellipse cT aT bT q) + θ * C64.hat ν (C64.ellipse cT aT bT q)) ≠ 0

theorem gpOf_nil (g : Glob) (neg : Bool) (l : ℕ) (tcs : List TubeC) (vts : List (ℤ × ℤ)) :
    gpOf g neg l [] tcs vts = [] := by
  cases tcs <;> cases vts <;> rfl

theorem checkTAPieceN_ok {gn : GlobN} (hgn : GlobNOK gn) {A : ACtx} {zc : ℂ} {ps : List ℂ}
    (hA : ACtxOK gn.g A zc ps) {bx : List (ℕ × ℕ × ℕ)} (hbx : bx.length = ps.length) {E : EllB} {cT : ℂ}
    {aT bT : ℝ} (hE : EllOK gn.g.P cT aT bT E) {r' tn td : ℕ} (htn : 0 < tn) (htd : 0 < td) {u v : ℤ × ℤ}
    {ys : List (ℤ × ℤ)} (hys : ys.length = ps.length) (hX : ((starRingEnd ℂ) (cOf v) * C64.S zc).re ≤ 0)
    {tbs : List TubeD} {tcs : List TubeC} {vts : List (ℤ × ℤ)} (htc : List.Forall₂ (TubeCOK gn) tbs tcs)
    {ivB : ℤ} (hiv : ivSum gn true tcs vts = some ivB) {l : ℕ} (hl : tbs = [] ∨ l < gn.nL)
    {n0 n1 e : ℕ} (h01 : n0 ≤ n1) (he : e + 1 ≤ gn.g.P)
    (h : checkTAPieceN gn.g A E r' tn td (intC gn.g.P u) (intC gn.g.P v) (yTerms gn.g.P true A.pins ys)
      (sumBox true (pinBoxes gn.g.P A.pins bx) ys) ivB (ivGroups gn.g.P true l tcs vts) n0 n1 e = true) :
    ∀ q ∈ Set.Icc ((n0 : ℝ) / 2 ^ e) ((n1 : ℝ) / 2 ^ e),
      TileCondN ((tn : ℝ) / td) zc ((r' : ℝ) / 2 ^ gn.g.P) (pqL ps A.pins bx) gn.eps.val (tbs.map (tubeR gn.g))
        cT aT bT q := by
  unfold checkTAPieceN at h
  simp only [Option.any_eq_true] at h
  obtain ⟨pd, hpd, T, hT, dz, hdz, h⟩ := h
  unfold taPieceOKN at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨ha, htb⟩ := h
  have hP := two_pow_pos' gn.g.P
  obtain ⟨hpdok, hrad⟩ := piece3_ok (c := gn.g.cfg) hE h01 he hpd
  set zm := C64.ellipse cT aT bT (((n0 : ℝ) + n1) / 2 ^ (e + 1)) with hzm
  have hTok := ptT_ok hpdok.z hgn.g.D1 hgn.g.hD hT
  obtain ⟨hdz1, hdz2⟩ := dzOf_ok hpdok.z hdz
  obtain ⟨tv, h1, h2, h3, h4, h5⟩ := ivSum_hi hgn tbs tcs vts htc hiv
  have hlen : A.pins.length = ps.length := (List.Forall₂.length_eq hA.hpins).symm
  set ds := dsOf gn.g.P ps A.pins bx ys
  have hpq : C64.pqOf ds = pqL ps A.pins bx := pqOf_dsOf ps A.pins bx ys hlen hbx hys
  have hbox := dsOf_bounds (P := gn.g.P) (ps := ps) (pins_d hA.hpins) bx ys
  obtain ⟨-, hhi⟩ := sum_lo_dsOf (P := gn.g.P) ps A.pins bx ys hlen hbx
  obtain ⟨hF, hL⟩ := yTerms_ok hA.hpins true ys
  obtain ⟨p1, p2, p3, p4⟩ := pinDT_ok hF
  have hu := memC_intC (P := gn.g.P) u
  have hv := memC_intC (P := gn.g.P) v
  set mp : List DTerm := (((starRingEnd ℂ) (cOf u), zm, (pd.rho : ℝ) / 2 ^ gn.g.P),
      termD (CBall.conj (intC gn.g.P u)) T dz) ::
    ((-(starRingEnd ℂ) (cOf v), zc, (0 : ℝ)), toD (termOf (CBall.neg (CBall.conj (intC gn.g.P v))) A.zT)) ::
    pinDT (yczs true ps ys) (yTerms gn.g.P true A.pins ys) with hmp_def
  set gp := gpOf gn.g true l tbs tcs vts
  have hmp : mp.map Prod.snd = termD (CBall.conj (intC gn.g.P u)) T dz ::
      toD (termOf (CBall.neg (CBall.conj (intC gn.g.P v))) A.zT) :: (yTerms gn.g.P true A.pins ys).map toD := by
    simp only [hmp_def, List.map_cons, p2]
  have hgp : gp.map (·.map Prod.snd) = ivGroups gn.g.P true l tcs vts :=
    gpOf_snd gn.g true l tbs tcs vts (List.Forall₂.length_eq htc)
  have htb' : tboundD gn.g.P gn.g.D (mp.map Prod.snd) (gp.map (·.map Prod.snd))
      ((((aTA3 gn.g A r' (intC gn.g.P u) (intC gn.g.P v) (sumBox true (pinBoxes gn.g.P A.pins bx) ys) pd - ivB).toNat
        * td / tn : ℕ) : ℤ)) = true := by
    rw [hmp, hgp]; exact htb
  have hmpok : ∀ p ∈ mp, DOK gn.g.P 0 1 p := by
    intro p hp
    simp only [hmp_def, List.mem_cons] at hp
    rcases hp with rfl | rfl | hp
    · exact termD_ok hTok (C64Num.CBall.memC_conj hu) (by positivity) hdz1 (fun _ => hdz2)
    · exact toD_ok (termOf_ok hA.hzT (C64Num.CBall.memC_neg (C64Num.CBall.memC_conj hv)))
    · exact p1 p hp
  have hmplen : ∀ p ∈ mp, p.2.st.length = gn.g.D := by
    intro p hp
    simp only [hmp_def, List.mem_cons] at hp
    rcases hp with rfl | rfl | hp
    · exact hTok.len
    · exact hA.hzT.len
    · have hp2 : p.2 ∈ (yTerms gn.g.P true A.pins ys).map toD := by rw [← p2]; exact List.mem_map_of_mem hp
      obtain ⟨T', hT', heq⟩ := List.mem_map.1 hp2
      rw [← heq]; exact hL T' hT'
  have hgpok : ∀ G ∈ gp, ∀ p ∈ G, DOK gn.g.P 0 1 p ∧ p.2.st.length = gn.g.D := by
    rcases hl with hnil | hl'
    · subst hnil; intro G hG; simp [gp, gpOf_nil] at hG
    · exact gpOf_ok hl' tbs tcs vts htc
  intro q hq μ ν hμ hν θ hθ
  rw [← h1, ← hpq] at hμ hν
  have hτ : (0 : ℝ) ≤ (tn : ℝ) / td := by positivity
  set a := aTA3 gn.g A r' (intC gn.g.P u) (intC gn.g.P v) (sumBox true (pinBoxes gn.g.P A.pins bx) ys) pd - ivB
  have hdq := hrad q hq
  -- the right-hand side
  have hS := hpdok.dS _ hdq
  obtain ⟨sLo, -⟩ := reConj_bounds (C64Num.CBall.memC_conj hu |> fun _ => hu) hpdok.sz
  have hRHS : (a : ℝ) / 2 ^ gn.g.P ≤ ((starRingEnd ℂ) (cOf u) * C64.S (C64.ellipse cT aT bT q)).re -
      ((starRingEnd ℂ) (cOf v) * C64.S zc).re - ‖cOf v‖ * ((r' : ℝ) / 2 ^ gn.g.P) -
      (ds.map fun d => d.hi).sum - (tv.map fun x => x.2.2 + ‖x.2.1‖ * gn.eps.val).sum := by
    have hX1 := (reConj_bounds hv hA.hSc).2
    have hrv : ‖cOf v‖ * ((r' : ℝ) / 2 ^ gn.g.P) ≤ (mulU gn.g.P (normHi (intC gn.g.P v)) r' : ℝ) / 2 ^ gn.g.P :=
      mulU_le (norm_nonneg _) (by positivity) (norm_le_normHi hv) le_rfl
    have huS : ‖cOf u‖ * ‖C64.S (C64.ellipse cT aT bT q) - C64.S zm‖ ≤
        (mulU gn.g.P (normHi (intC gn.g.P u)) pd.dS : ℝ) / 2 ^ gn.g.P :=
      mulU_le (norm_nonneg _) (norm_nonneg _) (norm_le_normHi hu) hS
    have hdiff : |((starRingEnd ℂ) (cOf u) * C64.S (C64.ellipse cT aT bT q)).re -
        ((starRingEnd ℂ) (cOf u) * C64.S zm).re| ≤ ‖cOf u‖ * ‖C64.S (C64.ellipse cT aT bT q) - C64.S zm‖ := by
      rw [← Complex.sub_re, ← mul_sub]
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, Complex.norm_conj]
    have hab := abs_le.1 hdiff
    rw [hhi]
    unfold a aTA3 aLow3
    push_cast
    rw [sub_div, sub_div, sub_div, sub_div, sub_div]
    linarith
  have hapos : (0 : ℝ) < (a : ℝ) / 2 ^ gn.g.P := div_pos (by exact_mod_cast ha) hP
  refine C64.nodeSet_tile_ne hτ hbox hX h3 h4 (fun zs hzs t ht => ?_) (lt_of_lt_of_le hapos hRHS) hμ hν hθ
  obtain ⟨sel, hsel, hfs⟩ := groups_sel (neg := true) tbs tcs vts tv zs hl htc h1 h2 hzs
  have hzl : List.Forall₂ (fun z (p : DTerm) => ‖z - p.1.2.1‖ ≤ p.1.2.2)
      (C64.ellipse cT aT bT q :: zc :: (yczs true ps ys).map Prod.snd) mp := by
    simp only [hmp_def]
    exact List.Forall₂.cons hdq (List.Forall₂.cons (by simp) p3)
  have hbound := tboundD_ok htb' hmpok (fun G hG p hp => (hgpok G hG p hp).1) hmplen
    (fun G hG p hp => (hgpok G hG p hp).2) _ hzl sel hsel t ht
  have hzip : List.zipWith (fun z (p : DTerm) => (p.1.1, z)) (C64.ellipse cT aT bT q :: zc ::
      (yczs true ps ys).map Prod.snd) mp = ((starRingEnd ℂ) (cOf u), C64.ellipse cT aT bT q) ::
      (-(starRingEnd ℂ) (cOf v), zc) :: yczs true ps ys := by
    simp only [hmp_def, List.zipWith_cons_cons, p4]
  rw [hzip, fsum_cons, fsum_cons, (fsum_yczs (P := gn.g.P) ps A.pins bx ys hlen hbx t).2, hfs t] at hbound
  have hφ : ((starRingEnd ℂ) (cOf u) * C64.Kt t (C64.ellipse cT aT bT q)).re - C64.LamL (cOf v) zc ds t -
      C64.TL (C64.tvz zs tv) t < ((((a.toNat * td / tn : ℕ) : ℤ)) : ℝ) / 2 ^ gn.g.P := by
    unfold C64.LamL
    simp only [neg_mul, Complex.neg_re, ↓reduceIte] at hbound
    linarith
  have hfl := floor_target_le ha htn htd
  have htn' : (0 : ℝ) < (tn : ℝ) / td := by
    have : (0 : ℝ) < tn := by exact_mod_cast htn
    have : (0 : ℝ) < td := by exact_mod_cast htd
    positivity
  calc ((tn : ℝ) / td) * (((starRingEnd ℂ) (cOf u) * C64.Kt t (C64.ellipse cT aT bT q)).re -
        C64.LamL (cOf v) zc ds t - C64.TL (C64.tvz zs tv) t)
      < ((tn : ℝ) / td) * (((((a.toNat * td / tn : ℕ) : ℤ)) : ℝ) / 2 ^ gn.g.P) :=
        mul_lt_mul_of_pos_left hφ htn'
    _ = (((tn : ℝ) / td) * ((a.toNat * td / tn : ℕ) : ℝ)) / 2 ^ gn.g.P := by rw [Int.cast_natCast]; ring
    _ ≤ (a : ℝ) / 2 ^ gn.g.P := div_le_div_of_nonneg_right hfl hP.le
    _ ≤ _ := hRHS

theorem checkTAN_ok {gn : GlobN} (hgn : GlobNOK gn) {A : ACtx} {zc : ℂ} {ps : List ℂ}
    (hA : ACtxOK gn.g A zc ps) {bx : List (ℕ × ℕ × ℕ)} (hbx : bx.length = ps.length) {E : EllB} {cT : ℂ}
    {aT bT : ℝ} (hE : EllOK gn.g.P cT aT bT E) {r' tn td : ℕ} (htn : 0 < tn) (htd : 0 < td) {u v : ℤ × ℤ}
    {ys : List (ℤ × ℤ)} (hys : ys.length = ps.length) (hX : ((starRingEnd ℂ) (cOf v) * C64.S zc).re ≤ 0)
    {tbs : List TubeD} {tcs : List TubeC} {vts : List (ℤ × ℤ)} (htc : List.Forall₂ (TubeCOK gn) tbs tcs)
    {ivB : ℤ} (hiv : ivSum gn true tcs vts = some ivB) {l : ℕ} (hl : tbs = [] ∨ l < gn.nL) :
    ∀ (fuel n0 n1 e : ℕ), n0 ≤ n1 → e + fuel + 1 ≤ gn.g.P →
    checkTAN gn.g A E r' tn td (intC gn.g.P u) (intC gn.g.P v) (yTerms gn.g.P true A.pins ys)
      (sumBox true (pinBoxes gn.g.P A.pins bx) ys) ivB (ivGroups gn.g.P true l tcs vts) fuel n0 n1 e = true →
    ∀ q ∈ Set.Icc ((n0 : ℝ) / 2 ^ e) ((n1 : ℝ) / 2 ^ e),
      TileCondN ((tn : ℝ) / td) zc ((r' : ℝ) / 2 ^ gn.g.P) (pqL ps A.pins bx) gn.eps.val (tbs.map (tubeR gn.g))
        cT aT bT q
  | 0, n0, n1, e, h01, he, h => checkTAPieceN_ok hgn hA hbx hE htn htd hys hX htc hiv hl h01 (by omega) h
  | fuel + 1, n0, n1, e, h01, he, h => by
    unfold checkTAN at h
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact checkTAPieceN_ok hgn hA hbx hE htn htd hys hX htc hiv hl h01 (by omega) h
    · intro s hs
      have hm : ((n0 + n1 : ℕ) : ℝ) / 2 ^ (e + 1) = ((n0 : ℝ) + n1) / 2 ^ (e + 1) := by push_cast; ring
      rcases le_total s (((n0 : ℝ) + n1) / 2 ^ (e + 1)) with hsm | hsm
      · refine checkTAN_ok hgn hA hbx hE htn htd hys hX htc hiv hl fuel (2 * n0) (n0 + n1) (e + 1) (by omega)
          (by omega) h1 s ⟨?_, ?_⟩
        · push_cast; rw [pow_succ]
          have := hs.1; rw [show (2 * (n0 : ℝ)) / (2 ^ e * 2) = (n0 : ℝ) / 2 ^ e by field_simp]; exact this
        · rw [hm]; exact hsm
      · refine checkTAN_ok hgn hA hbx hE htn htd hys hX htc hiv hl fuel (n0 + n1) (2 * n1) (e + 1) (by omega)
          (by omega) h2 s ⟨?_, ?_⟩
        · rw [hm]; exact hsm
        · push_cast; rw [pow_succ]
          have := hs.2; rw [show (2 * (n1 : ℝ)) / (2 ^ e * 2) = (n1 : ℝ) / 2 ^ e by field_simp]; exact this

theorem levels_ok {gn : GlobN} {tbs : List TubeD} {tcs : List TubeC} (htc : List.Forall₂ (TubeCOK gn) tbs tcs)
    {l : ℕ} (hl : l ∈ levels gn tcs) : tbs = [] ∨ l < gn.nL := by
  unfold levels at hl
  by_cases h : tcs.isEmpty
  · left
    rw [List.isEmpty_iff] at h; subst h
    cases htc; rfl
  · right
    rw [if_neg h] at hl
    exact List.mem_range.1 hl

theorem taOKN_ok {gn : GlobN} (hgn : GlobNOK gn) {A : ACtx} {zc : ℂ} {ps : List ℂ}
    (hA : ACtxOK gn.g A zc ps) {bx : List (ℕ × ℕ × ℕ)} (hbx : bx.length = ps.length) {E : EllB} {cT : ℂ}
    {aT bT : ℝ} (hE : EllOK gn.g.P cT aT bT E) {r' tn td : ℕ} (htn : 0 < tn) (htd : 0 < td)
    {tbs : List TubeD} {tcs : List TubeC} (htc : List.Forall₂ (TubeCOK gn) tbs tcs) {q0 q1 : ℕ} {u v : ℤ × ℤ}
    {ys vts : List (ℤ × ℤ)} (hys : ys.length = ps.length)
    (h : taOKN gn A E r' tn td (pinBoxes gn.g.P A.pins bx) tcs q0 q1 u v ys vts = true) :
    q0 < q1 ∧ q1 ≤ 2 ^ gn.g.EQ ∧ ∀ q ∈ Set.Icc ((q0 : ℝ) / 2 ^ gn.g.EQ) ((q1 : ℝ) / 2 ^ gn.g.EQ),
      TileCondN ((tn : ℝ) / td) zc ((r' : ℝ) / 2 ^ gn.g.P) (pqL ps A.pins bx) gn.eps.val (tbs.map (tubeR gn.g))
        cT aT bT q := by
  unfold taOKN at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, Option.any_eq_true,
    List.any_eq_true] at h
  obtain ⟨⟨⟨h01, h1Q⟩, hXv⟩, ivB, hiv, l, hl, hck⟩ := h
  have hP := two_pow_pos' gn.g.P
  have hX : ((starRingEnd ℂ) (cOf v) * C64.S zc).re ≤ 0 := by
    rcases hXv with hXv | hXv
    · exact le_trans (reConj_bounds (memC_intC (P := gn.g.P) v) hA.hSc).2
        (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hXv) hP.le)
    · have : cOf v = 0 := by rw [hXv]; apply Complex.ext <;> simp [cOf]
      rw [this]; simp
  refine ⟨h01, h1Q, checkTAN_ok hgn hA hbx hE htn htd hys hX htc hiv (levels_ok htc hl) gn.g.dT q0 q1 gn.g.EQ
    h01.le (by have := hgn.g.hT; omega) hck⟩

theorem walkTA_ok {gn : GlobN} (hgn : GlobNOK gn) {A : ACtx} {zc : ℂ} {ps : List ℂ}
    (hA : ACtxOK gn.g A zc ps) {bx : List (ℕ × ℕ × ℕ)} (hbx : bx.length = ps.length) {E : EllB} {cT : ℂ}
    {aT bT : ℝ} (hE : EllOK gn.g.P cT aT bT E) {r' tn td : ℕ} (htn : 0 < tn) (htd : 0 < td)
    {tbs : List TubeD} {tcs : List TubeC} (htc : List.Forall₂ (TubeCOK gn) tbs tcs) :
    ∀ (fuel N q s : ℕ) (hs : List (ℕ × ℕ)),
    walkTA gn A E r' tn td (pinBoxes gn.g.P A.pins bx) tcs fuel N q s hs = true →
    q < 2 ^ gn.g.EQ → ∀ x ∈ Set.Icc ((q : ℝ) / 2 ^ gn.g.EQ) 1,
      TileCondN ((tn : ℝ) / td) zc ((r' : ℝ) / 2 ^ gn.g.P) (pqL ps A.pins bx) gn.eps.val (tbs.map (tubeR gn.g))
        cT aT bT x ∨ ∃ ab ∈ hs, x ∈ Set.Icc ((ab.1 : ℝ) / 2 ^ gn.g.EQ) ((ab.2 : ℝ) / 2 ^ gn.g.EQ)
  | 0, _, _, _, _, h, _ => by simp [walkTA] at h
  | fuel + 1, N, q, s, hs, h, hq => by
    have hEQ := two_pow_pos' gn.g.EQ
    have hlen : A.pins.length = ps.length := (List.Forall₂.length_eq hA.hpins).symm
    -- the W1 step
    have hw1 : walkTA.walkW1 gn A E r' tn td (pinBoxes gn.g.P A.pins bx) tcs fuel N q s hs = true →
        ∀ x ∈ Set.Icc ((q : ℝ) / 2 ^ gn.g.EQ) 1,
          TileCondN ((tn : ℝ) / td) zc ((r' : ℝ) / 2 ^ gn.g.P) (pqL ps A.pins bx) gn.eps.val (tbs.map (tubeR gn.g))
            cT aT bT x ∨ ∃ ab ∈ hs, x ∈ Set.Icc ((ab.1 : ℝ) / 2 ^ gn.g.EQ) ((ab.2 : ℝ) / 2 ^ gn.g.EQ) := by
      intro hW x hx
      unfold walkTA.walkW1 at hW
      cases N with
      | zero => simp at hW
      | succ N' =>
        simp only [Bool.and_eq_true] at hW
        obtain ⟨hta, hrest⟩ := hW
        set r := rdTAN A.pins.length tcs.length s
        have hys : r.2.2.2.1.length = ps.length := by simp only [r, rdTAN]; rw [rdPairs_length, hlen]
        obtain ⟨h01, h1Q, hcond⟩ := taOKN_ok hgn hA hbx hE htn htd htc hys hta
        rcases le_total x ((r.1 : ℝ) / 2 ^ gn.g.EQ) with hx1 | hx1
        · exact Or.inl (hcond x ⟨hx.1, hx1⟩)
        · rcases eq_or_lt_of_le h1Q with heq | hlt
          · left
            have h1 : (r.1 : ℝ) / 2 ^ gn.g.EQ = 1 := by rw [heq]; push_cast; exact div_self hEQ.ne'
            exact hcond x ⟨hx.1, by rw [h1]; exact hx.2⟩
          · exact walkTA_ok hgn hA hbx hE htn htd htc fuel N' r.1 r.2.2.2.2.2 hs hrest hlt x ⟨hx1, hx.2⟩
    unfold walkTA at h
    rw [if_neg (Nat.ne_of_lt hq)] at h
    cases hs with
    | nil => exact hw1 h
    | cons ab hs' =>
      obtain ⟨a, b⟩ := ab
      dsimp only at h
      by_cases hab : a = q
      · rw [if_pos hab] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨hqb, hb⟩, hrest⟩ := h
        intro x hx
        rcases le_total x ((b : ℝ) / 2 ^ gn.g.EQ) with hx1 | hx1
        · exact Or.inr ⟨(a, b), List.mem_cons_self, by rw [hab]; exact hx.1, hx1⟩
        · rcases eq_or_lt_of_le hb with heq | hlt
          · right
            have h1 : (b : ℝ) / 2 ^ gn.g.EQ = 1 := by rw [heq]; push_cast; exact div_self hEQ.ne'
            exact ⟨(a, b), List.mem_cons_self, by rw [hab]; exact hx.1, by rw [h1]; exact hx.2⟩
          · rcases walkTA_ok hgn hA hbx hE htn htd htc fuel N b s hs' hrest hlt x ⟨hx1, hx.2⟩ with h' | ⟨ab', hab', hx'⟩
            · exact Or.inl h'
            · exact Or.inr ⟨ab', List.mem_cons_of_mem _ hab', hx'⟩
      · rw [if_neg hab] at h
        exact hw1 h

/-! ### Representatives on the tubes -/

theorem exists_mem_zip {α β : Type} : ∀ {l1 : List α} {l2 : List β}, l1.length = l2.length →
    ∀ a ∈ l1, ∃ b, (a, b) ∈ l1.zip l2
  | [], _, _, a, ha => by simp at ha
  | _ :: _, [], h, _, _ => by simp at h
  | x :: l1, y :: l2, h, a, ha => by
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact ⟨y, by simp⟩
    · obtain ⟨b, hb⟩ := exists_mem_zip (by simpa using h) a ha
      exact ⟨b, by simp [hb]⟩

theorem tubeRepOK_ok {gn : GlobN} (hgn : GlobNOK gn) {as : List (Q × Q)} (hA : AtomsOK as) {tb : TubeD}
    (htb : AtomsOK tb.as) {qm : Q × Q} (h : tubeRepOK gn as tb qm = true) :
    C64.TubeIn gn.eps.val (tubeR gn.g tb) (atomicL as) := by
  unfold tubeRepOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Option.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hd1, hd2⟩, hmu⟩, hq0⟩, hq1⟩, Et, hEt, z, hz, sz, hsz, w, hw, w0, hw0, hn⟩ := h
  obtain ⟨-, -, hEok⟩ := tileOf_okR hgn.g hEt
  have hP := two_pow_pos' gn.g.P
  have hEQ := two_pow_pos' gn.g.EQ
  have hqd : (0 : ℝ) < qm.1.d := by exact_mod_cast hd1
  set q := qm.1.val
  have hqmem : q ∈ Set.Icc ((tb.q0 : ℝ) / 2 ^ gn.g.EQ) ((tb.q1 : ℝ) / 2 ^ gn.g.EQ) := by
    have e0 : ((tb.q0 : ℤ) * qm.1.d : ℝ) ≤ (qm.1.n * 2 ^ gn.g.EQ : ℝ) := by exact_mod_cast hq0
    have e1 : (qm.1.n * 2 ^ gn.g.EQ : ℝ) ≤ ((tb.q1 : ℤ) * qm.1.d : ℝ) := by exact_mod_cast hq1
    push_cast at e0 e1
    simp only [q, Q.val]
    constructor
    · rw [div_le_div_iff₀ hEQ hqd]; linarith
    · rw [div_le_div_iff₀ hqd hEQ]; linarith
  have hzm := memC_ellPt hEok (mem_Qball hd1) hz
  obtain ⟨-, hS⟩ := memC_cS hzm hsz
  have hW := sumK_ok hzm as (fun a ha => ⟨(hA a ha).1, (hA a ha).2.2.1⟩) hw
  have hW0 := sumK_ok hzm tb.as (fun a ha => ⟨(htb a ha).1, (htb a ha).2.2.1⟩) hw0
  have hm := C64Num.CBall.memC_sub (C64Num.CBall.memC_sub hW hS)
    (C64Num.CBall.memC_mulR (mem_Qball (P := gn.g.P) hd2) (C64Num.CBall.memC_sub hS hW0))
  refine ⟨q, hqmem, qm.2.val, ?_, ?_⟩
  · unfold Q.val; exact div_nonneg (by exact_mod_cast hmu) (by positivity)
  · simp only [tubeR, C64.TubeR.pt]
    rw [hat_atomicL hA]
    refine (norm_le_normHi hm).trans ?_
    exact (div_le_div_of_nonneg_right (by exact_mod_cast hn) hP.le).trans (epsLo_le hgn)

/-! ### W leaves and empty leaves -/

theorem tubes_ok {gn : GlobN} (hgn : GlobNOK gn) {tubes : List TubeD} {tcs : List TubeC}
    (h : tubes.mapM (tubeC gn) = some tcs) : List.Forall₂ (TubeCOK gn) tubes tcs :=
  (mapM_some h).imp (fun _ _ h' => tubeC_ok hgn h')

/-- The mass parameter of a leaf: `τ ≤ τ_N = tn / td`. -/
theorem tau_le_tw {g : Glob} (hg : GlobOK g) {tw : Q} (htw : 0 < tw.n) (htwd : 0 < tw.d)
    (hττ : g.tau.n * tw.d ≤ tw.n * g.tau.d) : g.tau.val ≤ (tw.n.toNat : ℝ) / tw.d := by
  have htn' : ((tw.n.toNat : ℕ) : ℝ) = (tw.n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg htw.le
  have htd' : (0 : ℝ) < tw.d := by exact_mod_cast htwd
  rw [htn']; unfold Q.val
  have h1 : (0 : ℝ) < g.tau.d := by have := lt_trans hg.tn hg.tlt; exact_mod_cast this
  rw [div_le_div_iff₀ h1 htd']; exact_mod_cast hττ

theorem witLocalN_ok {gn : GlobN} (hgn : GlobNOK gn) {A : ACtx} {zc : ℂ} {ps : List ℂ} (hA : ACtxOK gn.g A zc ps)
    {bx : List (ℕ × ℕ × ℕ)} (hbx : bx.length = ps.length) {tubes : List TubeD} {h : WHdr} {n dat : ℕ}
    {hards : List (ℕ × ℕ)} (hc : witLocalN gn A tubes bx h n dat hards = true)
    (hkids : ∀ ab ∈ hards, C64.NodeSettled gn.g.tau.val zc ((A.r : ℝ) / 2 ^ gn.g.P) (pqL ps A.pins bx) gn.eps.val
      ((tubes ++ [(⟨h.ti, ab.1, ab.2, h.as⟩ : TubeD)]).map (tubeR gn.g))) :
    C64.NodeSettled gn.g.tau.val zc ((A.r : ℝ) / 2 ^ gn.g.P) (pqL ps A.pins bx) gn.eps.val
      (tubes.map (tubeR gn.g)) := by
  unfold witLocalN at hc
  simp only [Option.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨E, hE, ⟨mn, md⟩, hmm, hc⟩ := hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨htw, htwd⟩, hττ⟩, hmτ⟩, hsgd⟩, hsg⟩, hmlen⟩, hreps⟩, r', hr', wz, hwz, hc⟩ := hc
  obtain ⟨⟨⟨⟨hrr, hcross⟩, hpins⟩, hwo⟩, tcs, htcs, hwalk⟩ := hc
  have hg := hgn.g
  obtain ⟨haT, hbT, hEok⟩ := tileOf_okR hg hE
  obtain ⟨hAt, hmd, hms⟩ := atomsOK_ok h.as hmm
  have hP := two_pow_pos' gn.g.P
  set tn := h.tw.n.toNat
  set td := h.tw.d
  have htn : 0 < tn := by simp only [tn]; omega
  have htd' : (0 : ℝ) < td := by exact_mod_cast htwd
  have hmd' : (0 : ℝ) < md := by exact_mod_cast hmd
  have htn' : ((tn : ℕ) : ℝ) = (h.tw.n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg htw.le
  have hττ' : gn.g.tau.val ≤ (tn : ℝ) / td := tau_le_tw hg htw htwd hττ
  have hmsτ : msum h.as ≤ (tn : ℝ) / td := by
    rw [hms, htn', div_le_div_iff₀ hmd' htd']; exact_mod_cast hmτ
  set ν := atomicL h.as
  have hνA : C64.ClassA ((tn : ℝ) / td) ν := classA_atomicL hAt hmsτ
  have hwzν := sumK_ok hA.hzc h.as (fun a ha => ⟨(hAt a ha).1, (hAt a ha).2.2.1⟩) hwz
  have hσ1 : 1 ≤ h.sg.val := by
    unfold Q.val
    have : (0 : ℝ) < h.sg.d := by exact_mod_cast hsgd
    rw [le_div_iff₀ this, one_mul]; exact_mod_cast hsg
  have hTC := tubes_ok hgn htcs
  have hν : C64.NodeSet ((tn : ℝ) / td) zc ((r' : ℝ) / 2 ^ gn.g.P) (pqL ps A.pins bx) gn.eps.val
      (tubes.map (tubeR gn.g)) ν := by
    refine ⟨⟨hνA, ⟨h.sg.val, hσ1, ?_⟩, ?_⟩, ?_⟩
    · rw [hat_atomicL hAt]
      have hm := C64Num.CBall.memC_sub hwzν (C64Num.CBall.memC_mulR (mem_Qball (P := gn.g.P) hsgd) hA.hSc)
      refine (norm_le_normHi hm).trans ?_
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcross) hP.le
    · intro x hx
      rw [hat_atomicL hAt]
      exact pinsIn_ok hAt ps A.pins bx hA.hpins hpins x hx
    · intro tb' htb'
      obtain ⟨tb, htb, rfl⟩ := List.mem_map.1 htb'
      obtain ⟨m, hm⟩ := exists_mem_zip hmlen.symm tb htb
      obtain ⟨tc, -, htcok⟩ := forall2_left_mem hTC tb htb
      exact tubeRepOK_ok hgn hAt htcok.hA (hreps _ hm)
  have hmS : msum h.as ≤ (Ball.cdiv (mn.toNat * 2 ^ gn.g.P) md : ℝ) / 2 ^ gn.g.P := by
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
  obtain ⟨-, nw, hn, hwind⟩ := windOdd_ok hg hEok hAt hmS hwo
  have hwν : C64.hat ν = wsum h.as := funext (hat_atomicL hAt)
  have hwind' : C64.HasWinding (fun q => C64.G ν (C64.ellipse (tileR gn.g h.ti).1 (tileR gn.g h.ti).2.1
      (tileR gn.g h.ti).2.2 q)) nw := by
    have : (fun q => C64.G ν (C64.ellipse (tileR gn.g h.ti).1 (tileR gn.g h.ti).2.1 (tileR gn.g h.ti).2.2 q)) =
        fun q => C64.S (C64.ellipse (tileR gn.g h.ti).1 (tileR gn.g h.ti).2.1 (tileR gn.g h.ti).2.2 q) -
          wsum h.as (C64.ellipse (tileR gn.g h.ti).1 (tileR gn.g h.ti).2.1 (tileR gn.g h.ti).2.2 q) := by
      funext q; unfold C64.G; rw [hwν]
    rw [this]; exact hwind
  have hEQ := two_pow_pos' gn.g.EQ
  refine C64.nodeSettled_of_witness hττ' (div_le_div_of_nonneg_right (by exact_mod_cast hrr) hP.le)
    (eps_nonneg hgn) haT hbT hν hn hwind' (fun q hq => ?_)
  rcases walkTA_ok hgn hA hbx hEok htn htwd hTC _ n 0 dat hards hwalk (by positivity) q
      ⟨by simpa using hq.1, hq.2⟩ with hW | ⟨ab, hab, hqab⟩
  · exact Or.inl hW
  · refine Or.inr ⟨(ab.1 : ℝ) / 2 ^ gn.g.EQ, (ab.2 : ℝ) / 2 ^ gn.g.EQ, hqab, ?_⟩
    have := hkids ab hab
    rw [List.map_append, List.map_singleton] at this
    rw [hwν]; exact this

theorem emptyN_ok {gn : GlobN} (hgn : GlobNOK gn) {A : ACtx} {zc : ℂ} {ps : List ℂ} (hA : ACtxOK gn.g A zc ps)
    {bx : List (ℕ × ℕ × ℕ)} (hbx : bx.length = ps.length) {tubes : List TubeD} {tw : Q} {rX dat : ℕ}
    (hc : emptyN gn A tubes bx tw rX dat = true) :
    C64.NodeSettled gn.g.tau.val zc ((A.r : ℝ) / 2 ^ gn.g.P) (pqL ps A.pins bx) gn.eps.val
      (tubes.map (tubeR gn.g)) := by
  unfold emptyN at hc
  simp only [Option.any_eq_true, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.any_eq_true] at hc
  obtain ⟨⟨⟨⟨htw, htwd⟩, hττ⟩, hXv⟩, r', hr', hrr, tcs, htcs, ivB, hiv, hLpos, l, hl, htb⟩ := hc
  have hg := hgn.g
  have hP := two_pow_pos' gn.g.P
  set vv := (rdPair dat).1
  set ys := (rdPairs A.pins.length (rdPair dat).2).1
  set vts := (rdPairs tubes.length (rdPairs A.pins.length (rdPair dat).2).2).1
  have hlen : A.pins.length = ps.length := (List.Forall₂.length_eq hA.hpins).symm
  have hys : ys.length = ps.length := by rw [rdPairs_length, hlen]
  have hTC := tubes_ok hgn htcs
  obtain ⟨tv, h1, h2, h3, h4, h5⟩ := ivSum_lo hgn tubes tcs vts hTC hiv
  set ds := dsOf gn.g.P ps A.pins bx ys
  have hpq : C64.pqOf ds = pqL ps A.pins bx := pqOf_dsOf ps A.pins bx ys hlen hbx hys
  have hbox := dsOf_bounds (P := gn.g.P) (ps := ps) (pins_d hA.hpins) bx ys
  obtain ⟨hlo, -⟩ := sum_lo_dsOf (P := gn.g.P) ps A.pins bx ys hlen hbx
  have hv := memC_intC (P := gn.g.P) vv
  obtain ⟨hXlo, -⟩ := reConj_bounds hv hA.hSc
  have hX : 0 ≤ ((starRingEnd ℂ) (cOf vv) * C64.S zc).re := by
    rcases hXv with hXv | hXv
    · exact le_trans (div_nonneg (by exact_mod_cast hXv) hP.le) hXlo
    · have : cOf vv = 0 := by rw [hXv]; apply Complex.ext <;> simp [cOf]
      rw [this]; simp
  set tn := tw.n.toNat
  set td := tw.d
  have htn : 0 < tn := by simp only [tn]; omega
  have hττ' : gn.g.tau.val ≤ (tn : ℝ) / td := tau_le_tw hg htw htwd hττ
  set L := reConjLo gn.g.P (intC gn.g.P vv) A.Sc - (mulU gn.g.P (normHi (intC gn.g.P vv)) r' : ℕ) +
    sumBox false (pinBoxes gn.g.P A.pins bx) ys + ivB
  have hrv : ‖cOf vv‖ * ((r' : ℝ) / 2 ^ gn.g.P) ≤ (mulU gn.g.P (normHi (intC gn.g.P vv)) r' : ℝ) / 2 ^ gn.g.P :=
    mulU_le (norm_nonneg _) (by positivity) (norm_le_normHi hv) le_rfl
  have hRHS : (L : ℝ) / 2 ^ gn.g.P ≤ ((starRingEnd ℂ) (cOf vv) * C64.S zc).re - ‖cOf vv‖ * ((r' : ℝ) / 2 ^ gn.g.P) +
      (ds.map fun d => d.lo).sum + (tv.map fun x => x.2.2 - ‖x.2.1‖ * gn.eps.val).sum := by
    rw [hlo]
    simp only [L]
    push_cast
    rw [add_div, add_div, sub_div]
    linarith
  have hLpos' : (0 : ℝ) < (L : ℝ) / 2 ^ gn.g.P := div_pos (by exact_mod_cast hLpos) hP
  intro μ hμ
  exfalso
  have hμ' := hμ.mono hττ' (div_le_div_of_nonneg_right (by exact_mod_cast hrr : (A.r : ℝ) ≤ r') hP.le)
  rw [← h1, ← hpq] at hμ'
  refine C64.nodeSet_empty (by positivity) hbox hX h3 h4 (fun zs hzs t ht => ?_) (lt_of_lt_of_le hLpos' hRHS) hμ'
  obtain ⟨hF, hL⟩ := yTerms_ok hA.hpins false ys
  obtain ⟨p1, p2, p3, p4⟩ := pinDT_ok hF
  set mp : List DTerm := (((starRingEnd ℂ) (cOf vv), zc, (0 : ℝ)), toD (termOf (CBall.conj (intC gn.g.P vv)) A.zT)) ::
    pinDT (yczs false ps ys) (yTerms gn.g.P false A.pins ys) with hmp_def
  set gp := gpOf gn.g false l tubes tcs vts
  have hmp : mp.map Prod.snd = (termOf (CBall.conj (intC gn.g.P vv)) A.zT :: yTerms gn.g.P false A.pins ys).map toD := by
    simp only [hmp_def, List.map_cons, p2]
  have hgp : gp.map (·.map Prod.snd) = ivGroups gn.g.P false l tcs vts :=
    gpOf_snd gn.g false l tubes tcs vts (List.Forall₂.length_eq hTC)
  have htb' : tboundD gn.g.P gn.g.D (mp.map Prod.snd) (gp.map (·.map Prod.snd)) ((L.toNat * td / tn : ℕ) : ℤ) = true := by
    rw [hmp, hgp]; exact htb
  have hmpok : ∀ p ∈ mp, DOK gn.g.P 0 1 p := by
    intro p hp
    simp only [hmp_def, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact toD_ok (termOf_ok hA.hzT (C64Num.CBall.memC_conj hv))
    · exact p1 p hp
  have hmplen : ∀ p ∈ mp, p.2.st.length = gn.g.D := by
    intro p hp
    simp only [hmp_def, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hA.hzT.len
    · have hp2 : p.2 ∈ (yTerms gn.g.P false A.pins ys).map toD := by rw [← p2]; exact List.mem_map_of_mem hp
      obtain ⟨T', hT', heq⟩ := List.mem_map.1 hp2
      rw [← heq]; exact hL T' hT'
  have hl' := levels_ok hTC hl
  have hgpok : ∀ G ∈ gp, ∀ p ∈ G, DOK gn.g.P 0 1 p ∧ p.2.st.length = gn.g.D := by
    rcases hl' with hnil | hl''
    · subst hnil; intro G hG; simp [gp, gpOf_nil] at hG
    · exact gpOf_ok hl'' tubes tcs vts hTC
  obtain ⟨sel, hsel, hfs⟩ := groups_sel (neg := false) tubes tcs vts tv zs hl' hTC h1 h2 hzs
  have hzl : List.Forall₂ (fun z (p : DTerm) => ‖z - p.1.2.1‖ ≤ p.1.2.2) (zc :: (yczs false ps ys).map Prod.snd) mp := by
    simp only [hmp_def]
    exact List.Forall₂.cons (by simp) p3
  have hbound := tboundD_ok htb' hmpok (fun G hG p hp => (hgpok G hG p hp).1) hmplen
    (fun G hG p hp => (hgpok G hG p hp).2) _ hzl sel hsel t ht
  have hzip : List.zipWith (fun z (p : DTerm) => (p.1.1, z)) (zc :: (yczs false ps ys).map Prod.snd) mp =
      ((starRingEnd ℂ) (cOf vv), zc) :: yczs false ps ys := by
    simp only [hmp_def, List.zipWith_cons_cons, p4]
  rw [hzip, fsum_cons, (fsum_yczs (P := gn.g.P) ps A.pins bx ys hlen hbx t).1, hfs t] at hbound
  have hψ : C64.LamL (cOf vv) zc ds t + C64.TL (C64.tvz zs tv) t < (((L.toNat * td / tn : ℕ) : ℤ) : ℝ) / 2 ^ gn.g.P := by
    unfold C64.LamL
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hbound
    linarith
  have hfl := floor_target_le hLpos htn htwd
  have htn' : (0 : ℝ) < (tn : ℝ) / td := by
    have : (0 : ℝ) < tn := by exact_mod_cast htn
    have : (0 : ℝ) < td := by exact_mod_cast htwd
    positivity
  calc ((tn : ℝ) / td) * (C64.LamL (cOf vv) zc ds t + C64.TL (C64.tvz zs tv) t)
      < ((tn : ℝ) / td) * ((((L.toNat * td / tn : ℕ) : ℤ) : ℝ) / 2 ^ gn.g.P) := mul_lt_mul_of_pos_left hψ htn'
    _ = (((tn : ℝ) / td) * ((L.toNat * td / tn : ℕ) : ℝ)) / 2 ^ gn.g.P := by rw [Int.cast_natCast]; ring
    _ ≤ (L : ℝ) / 2 ^ gn.g.P := div_le_div_of_nonneg_right hfl hP.le
    _ ≤ _ := hRHS

end C64Chk
