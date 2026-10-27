import C64K.KCover
import C64K.KHint2

/-!
# Hinted segments and hint decoding for the generated kernel-only data modules (core Lean only)

* `segF_of_segFT_len`: `segF_of_segFT` with the segment length as a separate argument, so that a data module states a
  plain segment `segF gn J k` (literal `k`) and proves it from its hinted theorem without unifying `phs.length` with `k`
  (a direct `segF_of_segFT` application hits the elaborator's recursion limit).
* `hb`: tree hints from a bit string. The generator stores the hint of a W1 record as a natural number: the preorder
  bits of the trees, least significant bit first (`PHint`: 1 = split, then the two halves; 0 = piece, then its `CHint`;
  `CHint`: 1 = split, 0 = test). Hints are untrusted data: any tree is sound (`segF_of_segFT`), a wrong one only makes
  the hinted check fail.
-/

namespace C64KChk

open C64Chk

theorem segF_of_segFT_len {gn : GlobN} {s0 s1 sc : Nat} {pins : List (Q × Q)} {Rs : List Q} {rX : Nat} {p : List Nat}
    {tubes : List TubeD} {bx : List (Nat × Nat × Nat)} {t : NTree} {J k : Nat} {phs : List PHint}
    (hh : leafAny gn s0 s1 sc pins Rs rX p tubes bx t (segFT gn J phs) = true) (hk : phs.length = k) :
    leafAny gn s0 s1 sc pins Rs rX p tubes bx t (segF gn J k) = true :=
  hk ▸ segF_of_segFT hh

/-- A `CHint` from the low bits of `b` (at most `fuel` levels), with the remaining bits. -/
def decC : Nat → Nat → CHint × Nat
  | 0, b => (.test, b)
  | f + 1, b =>
    cond (Nat.beq (Nat.mod b 2) 1)
      (match decC f (Nat.div b 2) with
       | (l, b1) => match decC f b1 with
         | (r, b2) => (.split l r, b2))
      (.test, Nat.div b 2)

/-- A `PHint` from the low bits of `b` (at most `fuel` levels), with the remaining bits. -/
def decP : Nat → Nat → PHint × Nat
  | 0, b => (.piece .test, b)
  | f + 1, b =>
    cond (Nat.beq (Nat.mod b 2) 1)
      (match decP f (Nat.div b 2) with
       | (l, b1) => match decP f b1 with
         | (r, b2) => (.split l r, b2))
      (match decC 48 (Nat.div b 2) with
       | (c, b1) => (.piece c, b1))

/-- The tree hint of one W1 record from its bit string. -/
def hb (b : Nat) : PHint := (decP 24 b).1

end C64KChk
