import C64Core.Nest
import C64K.KChk

/-!
# The guard of the lazy pieces of a tube (core Lean only)

`C64KChk.tubeC` builds the pieces of a tube for the functions of `t` (`TubeC.ts`, 508 pieces on 7 levels in the
4/3 proof) lazily when the guard `tsLazyOK` holds: the kernel then computes a piece only when a test reads it. Under the
guard every such piece is `some` (`C64KPiece.tPiece_isSome`, C64K/KPieceSome.lean), so `tubeC` still computes the same
value as `C64Chk.tubeC` (`C64KChk.tubeC_eq`, for all inputs). The guard is cheap: the glob's constants, the tube's end
points, and the tile's magnitudes.

`C64KPiece.tileB` is the tile-size condition of `tPiece_isSome`, defined here (core Lean) so that the guard can evaluate
it.
-/

namespace C64KPiece

open KIval KIval.KBall C64KChk

/-- Size bounds of a tile ellipse (one `decide` per tile). -/
def tileB (E : EllB) : Bool :=
  Nat.ble (absHi E.cr) (2 ^ 84) && Nat.ble (absHi E.ci) (2 ^ 83) && Nat.ble (absHi E.a) (2 ^ 83) &&
    Nat.ble (absHi E.b) (2 ^ 83)

end C64KPiece

namespace C64KChk

open KIval KIval.KBall C64Chk

/-- The glob part of the guard: the constants of the 4/3 glob for which `tPiece_isSome` is proved (`P = 80`, `n = 18`,
`k = 3`, `D = 23`), and the deepest tube level `EQ + lT + nL - 1` below the precision. -/
def globLazyOK (gn : GlobN) : Bool :=
  Nat.beq gn.g.P 80 && Nat.beq gn.g.n 18 && Nat.beq gn.g.k 3 && Nat.beq gn.g.D 23 &&
  Nat.ble (Nat.add (Nat.add gn.g.EQ gn.lT) gn.nL) gn.g.P

/-- The guard of the lazy pieces of the tube `tb` on the tile `E`: the glob part, `q₀ < q₁ ≤ 2^EQ`, and the tile's
size bounds. -/
def tsLazyOK (gn : GlobN) (tb : TubeD) (E : EllB) : Bool :=
  globLazyOK gn && Nat.blt tb.q0 tb.q1 && Nat.ble tb.q1 (Nat.pow 2 gn.g.EQ) && C64KPiece.tileB E

end C64KChk
