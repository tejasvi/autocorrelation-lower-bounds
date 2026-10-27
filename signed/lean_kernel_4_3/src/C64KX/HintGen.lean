import C64K.KHint2

/-!
# Hint pass (run in the interpreter, not part of any proof)

For every W1 record of a W leaf: the tree hint of the checker's own search at tube level 0 (a failing piece test is a
split, a failing cell test is a split), as the bit string read by `C64KChk.hb` (preorder, least significant bit first;
`PHint`: 1 = split / 0 = piece, `CHint`: 1 = split / 0 = test). Output lines: `HB [path] j <hex>` (hard-arc steps: `0`),
`HBFAIL [path] j <reason>`. The hints are untrusted data: a wrong hint only makes the hinted kernel check fail.
This mirrors `C64KChk.checkTANT` / `cellsDT` (KHint2) and the search of `checkTAN` / `cellsD` (KNest).
-/

namespace C64KChk

open KIval KIval.KBall KNum C64Chk

/-- The bits of the cell tree of one tile-arc piece: `(value, length)`. -/
def cellsDbits (P : Nat) (target : SI) : Nat → Nat → Nat → SI → List TermD → List (List TermD) → Option (Nat × Nat)
  | 0, _, _, _, _, _ => none
  | fuel + 1, skip, e, tn, ts, gs =>
    let kids := fun (_ : Unit) =>
      (cellsDbits P target fuel (Nat.sub skip 1) (Nat.add e 1) (SI.sub (SI.mul (SI.ofNat 2) tn) (SI.ofNat 1))
        (ts.map (stepD P true)) (gs.map (·.map (stepD P true)))).bind fun l =>
      (cellsDbits P target fuel (Nat.sub skip 1) (Nat.add e 1) (SI.add (SI.mul (SI.ofNat 2) tn) (SI.ofNat 1))
        (ts.map (stepD P false)) (gs.map (·.map (stepD P false)))).map fun r =>
        (1 + 2 * (l.1 + 2 ^ l.2 * r.1), 1 + l.2 + r.2)
    if Nat.beq skip 0 then
      if cellOKD P ts gs e tn target then some (0, 1)
      else kids ()
    else kids ()

def pieceBits (g : Glob) (A : ACtx) (E : EllB) (r' tn td : Nat) (u v : KCBall) (yts : List TermS) (hiY ivB : SI)
    (gs : List (List TermD)) (n0 n1 e : Nat) : Option (Nat × Nat) :=
  (piece3 ⟨g.P, g.n, g.k⟩ E n0 n1 e).bind fun pd => (ptT ⟨g.P, g.n, g.k⟩ g.D pd.z).bind fun T =>
    (dzOf ⟨g.P, g.n, g.k⟩ pd.z pd.rho).bind fun dz =>
      let a := SI.sub (aTA3 g A r' u v hiY pd) ivB
      if SI.lt (SI.ofNat 0) a then
        cellsDbits g.P (SI.ofNat (Nat.div (Nat.mul (SI.toNat a) td) tn)) (Nat.add g.D 1) 4 1 (SI.ofNat 0)
          (termD (KCBall.conj u) T dz :: toD (termOf (KCBall.neg (KCBall.conj v)) A.zT) :: yts.map toD) gs
      else none

def tanBits (g : Glob) (A : ACtx) (E : EllB) (r' tn td : Nat) (u v : KCBall) (yts : List TermS) (hiY ivB : SI)
    (gs : List (List TermD)) : Nat → Nat → Nat → Nat → Option (Nat × Nat)
  | fuel, n0, n1, e =>
    match pieceBits g A E r' tn td u v yts hiY ivB gs n0 n1 e with
    | some c => some (2 * c.1, 1 + c.2)
    | none => match fuel with
      | 0 => none
      | f + 1 => (tanBits g A E r' tn td u v yts hiY ivB gs f (2 * n0) (n0 + n1) (e + 1)).bind fun l =>
          (tanBits g A E r' tn td u v yts hiY ivB gs f (n0 + n1) (2 * n1) (e + 1)).map fun r =>
            (1 + 2 * (l.1 + 2 ^ l.2 * r.1), 1 + l.2 + r.2)

/-- Print the hints of all steps of the W leaf at the path `p`. -/
def hgPath (gn : GlobN) (A : ACtx) (tubes0 : List TubeD) (bx0 : List (Nat × Nat × Nat)) (t : NTree) (p : List Nat) :
    IO Unit := do
  let key := "[" ++ String.intercalate "," (p.map toString) ++ "]"
  match nodeAt p tubes0 bx0 t with
  | some (tb, bx, .wit h n dat hards _) =>
    match walkCtx gn A tb h with
    | none => IO.println s!"HBFAIL {key} -1 noctx"
    | some w =>
      let g := gn.g
      let B := pinBoxes g.P A.pins bx
      let mut σ : WState := (n, 0, dat, hards)
      for j in List.range (n + hards.length) do
        let hard : Bool := match σ.2.2.2 with
          | (a, _) :: _ => Nat.beq a σ.2.1
          | [] => false
        if hard then
          IO.println s!"HB {key} {j} 0"
        else
          let r := rdTAN A.pins.length w.2.2.length σ.2.2.1
          match ivSum gn true w.2.2 r.2.2.2.2.1 with
          | none => IO.println s!"HBFAIL {key} {j} ivsum"
          | some ivB =>
            match tanBits g A w.1 w.2.1 h.tw.n.toNat h.tw.d (intC g.P r.2.1) (intC g.P r.2.2.1)
                (yTerms g.P true A.pins r.2.2.2.1) (sumBox true B r.2.2.2.1) ivB (ivGroups g.P true 0 w.2.2 r.2.2.2.2.1)
                g.dT σ.2.1 r.1 g.EQ with
            | none => IO.println s!"HBFAIL {key} {j} search"
            | some s => IO.println s!"HB {key} {j} {String.mk (Nat.toDigits 16 s.1)}"
        σ := stepState A w.2.2 σ
  | _ => IO.println s!"HBFAIL {key} -1 notw"

end C64KChk
