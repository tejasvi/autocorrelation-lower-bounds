import C64K.KNest

/-!
# Parts of a subtree check and their assembly (core Lean only)

A subtree check `checkN gn A fuel tubes bx t` (kernel port `C64K.KNest`) splits into the local checks of its nodes:
`localOK` is what `checkN` tests at a node itself (an empty leaf: `emptyN`; a W node: `witLocalN` and the number of its
children; a split: the box index; an ivsplit: the split point inside the arc of its tube); `children` lists the
children of a node with the tubes and boxes that `checkN` gives them.  `nodeAt p` follows the child indices `p`,
`partOK gn A p tubes bx t` is the local check of the node at `p`, and `paths t` lists the paths of all nodes.

`checkN_of_parts`: if `depth t < fuel` and `partOK` holds at every path of `paths t`, then `checkN` holds.  So the check
of a subtree is the conjunction of separately kernel-checked parts (one theorem per node, or per group of nodes), which
bounds the kernel time and memory per theorem; `checkSubNK_of_parts` / `checkArcNK_of_parts` assemble the statement of
a data module from its parts.
-/

namespace C64KChk

open C64Chk

/-- The children of a node, each with the tubes and boxes that `checkN` gives it. -/
def children (tubes : List TubeD) (bx : List (Nat × Nat × Nat)) :
    NTree → List (List TubeD × List (Nat × Nat × Nat) × NTree)
  | .wit h _ _ hards kids => (hards.zip kids).map fun x => (tubes ++ [⟨h.ti, x.1.1, x.1.2, h.as⟩], bx, x.2)
  | .split j c0 c1 c2 c3 =>
    [(tubes, bx.set j (kid (bx.getD j (0, 0, 0)) 0), c0), (tubes, bx.set j (kid (bx.getD j (0, 0, 0)) 1), c1),
     (tubes, bx.set j (kid (bx.getD j (0, 0, 0)) 2), c2), (tubes, bx.set j (kid (bx.getD j (0, 0, 0)) 3), c3)]
  | .ivsplit k qm lo hi =>
    match tubes[k]? with
    | some tb => [(tubes.set k { tb with q1 := qm }, bx, lo), (tubes.set k { tb with q0 := qm }, bx, hi)]
    | none => []
  | .empty _ _ _ => []
  | .ext => []

/-- The node at the path `p` (child indices), with its tubes and boxes. -/
def nodeAt : List Nat → List TubeD → List (Nat × Nat × Nat) → NTree →
    Option (List TubeD × List (Nat × Nat × Nat) × NTree)
  | [], tubes, bx, t => some (tubes, bx, t)
  | i :: p, tubes, bx, t =>
    match (children tubes bx t)[i]? with
    | some c => nodeAt p c.1 c.2.1 c.2.2
    | none => none

/-- What `checkN` tests at a node itself, apart from its children. -/
def localOK (gn : GlobN) (A : ACtx) (tubes : List TubeD) (bx : List (Nat × Nat × Nat)) : NTree → Bool
  | .empty tw rX dat => emptyN gn A tubes bx tw rX dat
  | .wit h n dat hards kids => witLocalN gn A tubes bx h n dat hards && decide (kids.length = hards.length)
  | .split j _ _ _ _ => decide (j < bx.length)
  | .ivsplit k qm _ _ =>
    match tubes[k]? with
    | some tb => decide (tb.q0 < qm) && decide (qm < tb.q1)
    | none => false
  | .ext => true

/-- The local check of the node at the path `p`. -/
def partOK (gn : GlobN) (A : ACtx) (p : List Nat) (tubes : List TubeD) (bx : List (Nat × Nat × Nat)) (t : NTree) :
    Bool :=
  (nodeAt p tubes bx t).any fun c => localOK gn A c.1 c.2.1 c.2.2

mutual
/-- The paths of all nodes of a tree (depth first). -/
def paths : NTree → List (List Nat)
  | .wit _ _ _ _ kids => [] :: pathsL 0 kids
  | .split _ c0 c1 c2 c3 =>
    [] :: ((paths c0).map (0 :: ·) ++ (paths c1).map (1 :: ·) ++ (paths c2).map (2 :: ·) ++ (paths c3).map (3 :: ·))
  | .ivsplit _ _ lo hi => [] :: ((paths lo).map (0 :: ·) ++ (paths hi).map (1 :: ·))
  | .empty _ _ _ => [[]]
  | .ext => [[]]
/-- The paths of a list of children, the first with index `i`. -/
def pathsL : Nat → List NTree → List (List Nat)
  | _, [] => []
  | i, t :: ts => (paths t).map (i :: ·) ++ pathsL (i + 1) ts
end

mutual
/-- The number of levels of a tree. -/
def depth : NTree → Nat
  | .wit _ _ _ _ kids => depthL kids + 1
  | .split _ c0 c1 c2 c3 => max (max (depth c0) (depth c1)) (max (depth c2) (depth c3)) + 1
  | .ivsplit _ _ lo hi => max (depth lo) (depth hi) + 1
  | .empty _ _ _ => 1
  | .ext => 1
/-- The largest depth in a list of trees. -/
def depthL : List NTree → Nat
  | [] => 0
  | t :: ts => max (depth t) (depthL ts)
end

/-! ## Lemmas -/

theorem nil_mem_paths (t : NTree) : [] ∈ paths t := by
  cases t <;> simp [paths]

theorem depth_le_depthL : ∀ (ts : List NTree) (c : NTree), c ∈ ts → depth c ≤ depthL ts
  | [], c, h => by simp at h
  | t :: ts, c, h => by
    simp only [depthL]
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (depth_le_depthL ts c h) (Nat.le_max_right _ _)

theorem mem_pathsL : ∀ (ts : List NTree) (i j : Nat) (c : NTree) (q : List Nat), ts[j]? = some c → q ∈ paths c →
    (i + j) :: q ∈ pathsL i ts
  | [], _, _, _, _, h, _ => by simp at h
  | t :: ts, i, 0, c, q, h, hq => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [pathsL, List.mem_append, List.mem_map, Nat.add_zero]
    exact Or.inl ⟨q, hq, rfl⟩
  | t :: ts, i, j + 1, c, q, h, hq => by
    simp only [List.getElem?_cons_succ] at h
    have := mem_pathsL ts (i + 1) j c q h hq
    simp only [pathsL, List.mem_append]
    refine Or.inr ?_
    rwa [show i + (j + 1) = i + 1 + j by omega]

theorem mem_map_cons {i : Nat} {q : List Nat} {l : List (List Nat)} (h : q ∈ l) : i :: q ∈ l.map (i :: ·) :=
  List.mem_map.2 ⟨q, h, rfl⟩

/-- A child is lower than its parent, and its paths, prefixed by its index, are paths of the parent. -/
theorem child_props {tubes : List TubeD} {bx : List (Nat × Nat × Nat)} {t : NTree} {i : Nat}
    {c : List TubeD × List (Nat × Nat × Nat) × NTree} (hc : (children tubes bx t)[i]? = some c) :
    depth c.2.2 < depth t ∧ ∀ q ∈ paths c.2.2, i :: q ∈ paths t := by
  cases t with
  | wit h n dat hards kids =>
    simp only [children, List.getElem?_map] at hc
    cases hz : (hards.zip kids)[i]? with
    | none => simp [hz] at hc
    | some x =>
      simp only [hz, Option.map_some, Option.some.injEq] at hc
      subst hc
      have hk : kids[i]? = some x.2 := (List.getElem?_zip_eq_some.1 hz).2
      refine ⟨?_, fun q hq => ?_⟩
      · have := depth_le_depthL kids x.2 (List.mem_of_getElem? hk)
        simp only [depth]
        omega
      · simp only [paths, List.mem_cons]
        refine Or.inr ?_
        have := mem_pathsL kids 0 i x.2 q hk hq
        rwa [Nat.zero_add] at this
  | split j c0 c1 c2 c3 =>
    simp only [children] at hc
    match i, hc with
    | 0, hc =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      refine ⟨by simp only [depth]; omega, fun q hq => ?_⟩
      simp only [paths, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inl (Or.inl (Or.inl (mem_map_cons hq))))
    | 1, hc =>
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      refine ⟨by simp only [depth]; omega, fun q hq => ?_⟩
      simp only [paths, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inl (Or.inl (Or.inr (mem_map_cons hq))))
    | 2, hc =>
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      refine ⟨by simp only [depth]; omega, fun q hq => ?_⟩
      simp only [paths, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inl (Or.inr (mem_map_cons hq)))
    | 3, hc =>
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      refine ⟨by simp only [depth]; omega, fun q hq => ?_⟩
      simp only [paths, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inr (mem_map_cons hq))
    | _ + 4, hc => simp at hc
  | ivsplit k qm lo hi =>
    simp only [children] at hc
    cases htb : tubes[k]? with
    | none => simp [htb] at hc
    | some tb =>
      simp only [htb] at hc
      match i, hc with
      | 0, hc =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
        subst hc
        refine ⟨by simp only [depth]; omega, fun q hq => ?_⟩
        simp only [paths, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl (mem_map_cons hq))
      | 1, hc =>
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hc
        subst hc
        refine ⟨by simp only [depth]; omega, fun q hq => ?_⟩
        simp only [paths, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr (mem_map_cons hq))
      | _ + 2, hc => simp at hc
  | empty tw rX dat => simp [children] at hc
  | ext => simp [children] at hc

theorem partOK_cons {gn : GlobN} {A : ACtx} {i : Nat} {p : List Nat} {tubes : List TubeD}
    {bx : List (Nat × Nat × Nat)} {t : NTree} {c : List TubeD × List (Nat × Nat × Nat) × NTree}
    (hc : (children tubes bx t)[i]? = some c) :
    partOK gn A (i :: p) tubes bx t = partOK gn A p c.1 c.2.1 c.2.2 := by
  simp only [partOK, nodeAt, hc]

/-! ## Assembly -/

/-- A subtree passes `checkN` if every node passes its local check (and the fuel exceeds the depth). -/
theorem checkN_of_parts (gn : GlobN) (A : ACtx) : ∀ (fuel : Nat) (tubes : List TubeD) (bx : List (Nat × Nat × Nat))
    (t : NTree), depth t < fuel → (∀ p ∈ paths t, partOK gn A p tubes bx t = true) →
    checkN gn A fuel tubes bx t = true
  | 0, _, _, _, hd, _ => absurd hd (Nat.not_lt_zero _)
  | fuel + 1, tubes, bx, t, hd, hp => by
    have hloc : localOK gn A tubes bx t = true := hp [] (nil_mem_paths t)
    have hkid : ∀ (i : Nat) (c : List TubeD × List (Nat × Nat × Nat) × NTree), (children tubes bx t)[i]? = some c →
        checkN gn A fuel c.1 c.2.1 c.2.2 = true := by
      intro i c hc
      obtain ⟨hdc, hpc⟩ := child_props hc
      refine checkN_of_parts gn A fuel c.1 c.2.1 c.2.2 (by omega) fun q hq => ?_
      rw [← partOK_cons hc]
      exact hp (i :: q) (hpc q hq)
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

/-- The statement of a subtree module from its parts: the header, the depth, and every node's local check under the
arc context. -/
theorem checkSubNK_of_parts {gn : GlobN} {s0 s1 sc : Nat} {pins : List (Q × Q)} {Rs : List Q} {rX : Nat}
    {tubes : List TubeD} {bx : List (Nat × Nat × Nat)} {t : NTree}
    (hh : hHead gn.g s0 s1 sc pins Rs = true) (hd : Nat.blt (depth t) gn.fuel = true)
    (hp : ∀ p ∈ paths t, (arcCtx gn.g s0 s1 sc pins Rs rX).any (fun A => partOK gn A p tubes bx t) = true) :
    checkSubNK gn s0 s1 sc pins Rs rX tubes bx t = true := by
  have hd' : depth t < gn.fuel := Nat.blt_eq ▸ hd
  unfold checkSubNK
  rw [hh, Bool.true_and]
  have h0 := hp [] (nil_mem_paths t)
  cases hA : arcCtx gn.g s0 s1 sc pins Rs rX with
  | none => rw [hA] at h0; exact absurd h0 (by simp)
  | some A =>
    refine checkN_of_parts gn A gn.fuel tubes bx t hd' fun p hpp => ?_
    have := hp p hpp
    rw [hA] at this
    exact this

/-- The statement of an arc-root module from its parts. -/
theorem checkArcNK_of_parts {gn : GlobN} {s0 s1 sc : Nat} {pins : List (Q × Q)} {Rs : List Q} {rX : Nat} {t : NTree}
    (hh : hHead gn.g s0 s1 sc pins Rs = true) (hd : Nat.blt (depth t) gn.fuel = true)
    (hp : ∀ p ∈ paths t, (arcCtx gn.g s0 s1 sc pins Rs rX).any
      (fun A => partOK gn A p [] (pins.map fun _ => (0, 0, 0)) t) = true) :
    checkArcNK gn (.N s0 s1 sc pins Rs rX t) = true :=
  checkSubNK_of_parts hh hd hp

end C64KChk
