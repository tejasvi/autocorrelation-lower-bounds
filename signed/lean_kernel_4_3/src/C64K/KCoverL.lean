import C64K.KCover

/-!
# A linear cover check (core Lean only)

`covL f ps us`: the paths `ps` (in `paths` order) are covered by the units `us` (in the same order): each unit takes the
next path (`.loc p`: equal to it; `.sub p`: a prefix of it, with all following paths that have the prefix `p`). The fuel
`f` bounds the number of units used. This is linear in the number of paths, while `(paths t).all (covered us)` scans the
units for every path. `covL_sound` gives the latter; `checkSubNK_of_coverL` is `checkSubNK_of_cover` with `covL`.
-/

namespace C64KChk

open C64Chk

/-- The linear cover check. -/
def covL : Nat → List (List Nat) → List KUnit → Bool
  | _, [], _ => true
  | 0, _ :: _, _ => false
  | f + 1, q :: qs, us =>
    match us with
    | [] => false
    | .loc p :: us' => (p == q) && covL f qs us'
    | .sub p :: us' => p.isPrefixOf q && covL f (qs.dropWhile fun r => p.isPrefixOf r) us'

theorem covered_cons {u : KUnit} {us : List KUnit} {q : List Nat} (h : covered us q = true) :
    covered (u :: us) q = true := by
  unfold covered at *
  rw [List.any_cons, h, Bool.or_true]

theorem mem_dropWhile_or (P : List Nat → Bool) : ∀ (qs : List (List Nat)) (r : List Nat), r ∈ qs →
    r ∈ qs.dropWhile P ∨ P r = true
  | [], _, h => absurd h List.not_mem_nil
  | x :: xs, r, h => by
    cases hx : P x with
    | true =>
      simp only [List.dropWhile, hx]
      rcases List.mem_cons.1 h with rfl | h'
      · exact Or.inr hx
      · exact mem_dropWhile_or P xs r h'
    | false =>
      simp only [List.dropWhile, hx]
      exact Or.inl h

theorem covL_sound : ∀ (f : Nat) (ps : List (List Nat)) (us : List KUnit), covL f ps us = true →
    ∀ q ∈ ps, covered us q = true
  | _, [], _, _, _, hq => absurd hq List.not_mem_nil
  | 0, _ :: _, _, h, _, _ => by simp [covL] at h
  | _ + 1, _ :: _, [], h, _, _ => by simp [covL] at h
  | f + 1, q0 :: qs, .loc p :: us', h, q, hq => by
    simp only [covL, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hp, hrest⟩ := h
    rcases List.mem_cons.1 hq with rfl | hq'
    · unfold covered
      rw [List.any_cons]
      simp [hp]
    · exact covered_cons (covL_sound f qs us' hrest q hq')
  | f + 1, q0 :: qs, .sub p :: us', h, q, hq => by
    simp only [covL, Bool.and_eq_true] at h
    obtain ⟨hp, hrest⟩ := h
    rcases List.mem_cons.1 hq with rfl | hq'
    · unfold covered
      rw [List.any_cons]
      simp [hp]
    · rcases mem_dropWhile_or (fun r => p.isPrefixOf r) qs q hq' with hd | hpre
      · exact covered_cons (covL_sound f _ us' hrest q hd)
      · unfold covered
        rw [List.any_cons]
        simp [hpre]

/-- The statement of a subtree module from a cover by units, with the linear cover check. -/
theorem checkSubNK_of_coverL {gn : GlobN} {s0 s1 sc : Nat} {pins : List (Q × Q)} {Rs : List Q} {rX : Nat}
    {tubes : List TubeD} {bx : List (Nat × Nat × Nat)} {t : NTree} (us : List KUnit) (f : Nat)
    (hh : hHead gn.g s0 s1 sc pins Rs = true) (hd : Nat.blt (depth t) gn.fuel = true)
    (hne : us ≠ []) (hcov : covL f (paths t) us = true)
    (hus : ∀ u ∈ us, unitAny gn s0 s1 sc pins Rs rX tubes bx t u = true) :
    checkSubNK gn s0 s1 sc pins Rs rX tubes bx t = true :=
  checkSubNK_of_cover us hh hd hne (List.all_eq_true.2 fun q hq => covL_sound f _ us hcov q hq) hus

end C64KChk
