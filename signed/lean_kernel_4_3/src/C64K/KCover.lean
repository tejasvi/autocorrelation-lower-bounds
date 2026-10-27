import C64K.KSeg

/-!
# Covers of a subtree by local parts and whole sub-subtrees (core Lean only)

A unit of the K proof of a data module is either the local check of one node (`.loc p`: `partOK` at the path `p`, see
`C64K.KParts`; for a big W leaf proved from its head and walk segments, `C64K.KSeg`) or the whole check of the subtree
at a path (`.sub p`: `checkN` at that node, one kernel theorem; the kernel computes the tube data once per theorem, so
grouping many small leaves under one `.sub` unit saves the recomputation of their tubes).

`checkN_of_cover`: if every path of the tree is covered (equal to a `.loc` path or below a `.sub` path, `covered`) and
every unit holds, the tree passes `checkN`.  `checkSubNK_of_cover` gives the statement of a data module.
-/

namespace C64KChk

open KIval KIval.KBall KNum C64Chk

/-- A unit: the local check at a path, or the whole subtree at a path. -/
inductive KUnit where
  | loc (p : List Nat)
  | sub (p : List Nat)

/-- The path `q` is covered by the units: `.loc q` is a unit, or `.sub p` is a unit for a prefix `p` of `q`. -/
def covered (us : List KUnit) (q : List Nat) : Bool :=
  us.any fun u => match u with
    | .loc p => p == q
    | .sub p => p.isPrefixOf q

/-- The fact of a unit in the tree `t` (root fuel `fuel`): the subtree at depth `|p|` gets fuel `fuel - |p|`. -/
def unitOK (gn : GlobN) (A : ACtx) (tubes : List TubeD) (bx : List (Nat × Nat × Nat)) (t : NTree) (fuel : Nat) :
    KUnit → Bool
  | .loc p => partOK gn A p tubes bx t
  | .sub p => (nodeAt p tubes bx t).any fun c => checkN gn A (fuel - p.length) c.1 c.2.1 c.2.2

theorem nodeAt_append : ∀ (p q : List Nat) (tubes : List TubeD) (bx : List (Nat × Nat × Nat)) (t : NTree),
    nodeAt (p ++ q) tubes bx t = (nodeAt p tubes bx t).bind fun c => nodeAt q c.1 c.2.1 c.2.2
  | [], q, tubes, bx, t => by simp [nodeAt]
  | i :: p, q, tubes, bx, t => by
    simp only [List.cons_append, nodeAt]
    cases (children tubes bx t)[i]? with
    | none => rfl
    | some c => exact nodeAt_append p q c.1 c.2.1 c.2.2

theorem mem_paths_child {tubes : List TubeD} {bx : List (Nat × Nat × Nat)} {t : NTree} {i : Nat}
    {c : List TubeD × List (Nat × Nat × Nat) × NTree} (hc : (children tubes bx t)[i]? = some c) {q : List Nat}
    (hq : q ∈ paths c.2.2) : i :: q ∈ paths t :=
  (child_props hc).2 q hq

/-- The cover lemma, for the subtree at the path `p0` of the root tree (fuel `fuel` at the root): if no `.sub` unit
sits strictly above `p0`, every path below `p0` is covered, and every unit holds, then the subtree at `p0` passes. -/
theorem checkN_of_cover_at (gn : GlobN) (A : ACtx) (tubes0 : List TubeD) (bx0 : List (Nat × Nat × Nat)) (t0 : NTree)
    (fuel : Nat) (us : List KUnit) (hus : ∀ u ∈ us, unitOK gn A tubes0 bx0 t0 fuel u = true) :
    ∀ (f : Nat) (p0 : List Nat) (tubes : List TubeD) (bx : List (Nat × Nat × Nat)) (t : NTree),
      nodeAt p0 tubes0 bx0 t0 = some (tubes, bx, t) → f = fuel - p0.length → depth t < f →
      (∀ q ∈ paths t, covered us (p0 ++ q) = true) →
      (∀ p, p.length < p0.length → p.isPrefixOf p0 = true → KUnit.sub p ∉ us) →
      checkN gn A f tubes bx t = true
  | 0, _, _, _, _, _, _, hd, _, _ => absurd hd (Nat.not_lt_zero _)
  | f + 1, p0, tubes, bx, t, hn, hf, hd, hcov, hnosub => by
    -- the unit at `p0`: a `.sub p0` (done), or else a `.loc p0`
    by_cases hs : KUnit.sub p0 ∈ us
    · have h := hus _ hs
      simp only [unitOK, hn, Option.any_some] at h
      rw [← hf] at h
      exact h
    · have hc0 := hcov [] (nil_mem_paths t)
      simp only [List.append_nil, covered, List.any_eq_true] at hc0
      obtain ⟨u, hu, hcu⟩ := hc0
      have hloc : localOK gn A tubes bx t = true := by
        cases u with
        | loc p =>
          simp only [beq_iff_eq] at hcu
          subst hcu
          have h := hus _ hu
          simp only [unitOK, partOK, hn, Option.any_some] at h
          exact h
        | sub p =>
          exfalso
          simp only at hcu
          by_cases hlen : p.length < p0.length
          · exact hnosub p hlen hcu hu
          · have hpl : p.length ≤ p0.length := (List.isPrefixOf_iff_prefix.1 hcu).length_le
            have : p = p0 := (List.isPrefixOf_iff_prefix.1 hcu).eq_of_length (by omega)
            subst this
            exact hs hu
      have hkid : ∀ (i : Nat) (c : List TubeD × List (Nat × Nat × Nat) × NTree), (children tubes bx t)[i]? = some c →
          checkN gn A f c.1 c.2.1 c.2.2 = true := by
        intro i c hc
        obtain ⟨hdc, hpc⟩ := child_props hc
        refine checkN_of_cover_at gn A tubes0 bx0 t0 fuel us hus f (p0 ++ [i]) c.1 c.2.1 c.2.2 ?_ ?_ (by omega)
          ?_ ?_
        · rw [nodeAt_append, hn]
          simp only [Option.bind_some, nodeAt, hc]
        · simp only [List.length_append, List.length_singleton]
          omega
        · intro q hq
          have := hcov (i :: q) (hpc q hq)
          simpa only [List.append_assoc, List.singleton_append] using this
        · intro p hlen hpre hsub
          rcases Nat.lt_or_ge p.length p0.length with hlt | hge
          · refine hnosub p hlt ?_ hsub
            have h1 := List.isPrefixOf_iff_prefix.1 hpre
            refine List.isPrefixOf_iff_prefix.2 ?_
            exact List.prefix_of_prefix_length_le h1 (List.prefix_append p0 [i]) (by omega)
          · have hlen' : p.length = p0.length := by
              simp only [List.length_append, List.length_singleton] at hlen
              omega
            have h1 := List.isPrefixOf_iff_prefix.1 hpre
            have h2 : p <+: p0 := List.prefix_of_prefix_length_le h1 (List.prefix_append p0 [i]) (by omega)
            have : p = p0 := h2.eq_of_length hlen'
            subst this
            exact hs hsub
      cases t with
      | empty tw rX dat => exact hloc
      | wit h n dat hards kids =>
        simp only [localOK, Bool.and_eq_true] at hloc
        simp only [checkN, Bool.and_eq_true, List.all_eq_true]
        refine ⟨hloc, fun x hx => ?_⟩
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
        exact hkid i (tubes ++ [⟨h.ti, x.1.1, x.1.2, h.as⟩], bx, x.2)
          (by simp only [children, List.getElem?_map, hi, Option.map_some])
      | split j c0 c1 c2 c3 =>
        simp only [localOK] at hloc
        simp only [checkN, hloc, Bool.true_and]
        simp only [Bool.and_eq_true]
        exact ⟨⟨⟨hkid 0 _ rfl, hkid 1 _ rfl⟩, hkid 2 _ rfl⟩, hkid 3 _ rfl⟩
      | ivsplit k qm lo hi =>
        simp only [localOK] at hloc
        cases htb : tubes[k]? with
        | none => simp [htb] at hloc
        | some tb =>
          simp only [htb, Bool.and_eq_true] at hloc
          have h0 := hkid 0 (tubes.set k { tb with q1 := qm }, bx, lo) (by simp only [children, htb]; rfl)
          have h1 := hkid 1 (tubes.set k { tb with q0 := qm }, bx, hi) (by simp only [children, htb]; rfl)
          simp only [checkN, htb, Bool.and_eq_true]
          exact ⟨⟨hloc, h0⟩, h1⟩
      | ext => rfl

theorem checkN_of_cover (gn : GlobN) (A : ACtx) (fuel : Nat) (tubes : List TubeD) (bx : List (Nat × Nat × Nat))
    (t : NTree) (us : List KUnit) (hd : depth t < fuel) (hcov : (paths t).all (covered us) = true)
    (hus : ∀ u ∈ us, unitOK gn A tubes bx t fuel u = true) : checkN gn A fuel tubes bx t = true :=
  checkN_of_cover_at gn A tubes bx t fuel us hus fuel [] tubes bx t rfl (by simp) hd
    (fun q hq => by simpa using (List.all_eq_true.1 hcov) q hq) (fun p hp _ => by simp at hp)

/-- The fact of a unit under the arc context. -/
def unitAny (gn : GlobN) (s0 s1 sc : Nat) (pins : List (Q × Q)) (Rs : List Q) (rX : Nat) (tubes : List TubeD)
    (bx : List (Nat × Nat × Nat)) (t : NTree) (u : KUnit) : Bool :=
  (arcCtx gn.g s0 s1 sc pins Rs rX).any fun A => unitOK gn A tubes bx t gn.fuel u

/-- The statement of a subtree module from a cover by units. -/
theorem checkSubNK_of_cover {gn : GlobN} {s0 s1 sc : Nat} {pins : List (Q × Q)} {Rs : List Q} {rX : Nat}
    {tubes : List TubeD} {bx : List (Nat × Nat × Nat)} {t : NTree} (us : List KUnit)
    (hh : hHead gn.g s0 s1 sc pins Rs = true) (hd : Nat.blt (depth t) gn.fuel = true)
    (hne : us ≠ []) (hcov : (paths t).all (covered us) = true)
    (hus : ∀ u ∈ us, unitAny gn s0 s1 sc pins Rs rX tubes bx t u = true) :
    checkSubNK gn s0 s1 sc pins Rs rX tubes bx t = true := by
  have hd' : depth t < gn.fuel := Nat.blt_eq ▸ hd
  unfold checkSubNK
  rw [hh, Bool.true_and]
  obtain ⟨u0, hu0⟩ := List.exists_mem_of_ne_nil us hne
  have h0 := hus u0 hu0
  unfold unitAny at h0
  cases hA : arcCtx gn.g s0 s1 sc pins Rs rX with
  | none => rw [hA] at h0; exact absurd h0 (by simp)
  | some A =>
    refine checkN_of_cover gn A gn.fuel tubes bx t us hd' hcov fun u hu => ?_
    have := hus u hu
    unfold unitAny at this
    rw [hA] at this
    exact this

/-- A `.loc` unit of a W node from its head and walk segments (`partAny_wit_of`). -/
theorem unitAny_loc_of {gn : GlobN} {s0 s1 sc : Nat} {pins : List (Q × Q)} {Rs : List Q} {rX : Nat}
    {tubes : List TubeD} {bx : List (Nat × Nat × Nat)} {t : NTree} {p : List Nat}
    (h : (arcCtx gn.g s0 s1 sc pins Rs rX).any (fun A => partOK gn A p tubes bx t) = true) :
    unitAny gn s0 s1 sc pins Rs rX tubes bx t (.loc p) = true := h

end C64KChk
