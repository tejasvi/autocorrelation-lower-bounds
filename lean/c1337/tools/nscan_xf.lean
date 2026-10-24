import Lean
/-!
Per-module axiom scan for a sharded NATIVE package built with `export_shard --fast` (CheckerXF), strict form.

usage: lean --run nscan_xf.lean LIST OUT PREFIX
  LIST    file with one .olean path per line; OUT  report file;
  PREFIX  the package namespace with a trailing dot, e.g. `Autocorr.C39S.`
As tools/nscan.lean (no environment: `readModuleData` per module; banned references `sorryAx`, `Lean.ofReduceBool`,
`Lean.ofReduceNat`, `Lean.trustCompiler`, `_native` constants outside PREFIX; external references recorded), and in
addition every `axiom` must be the native_decide auxiliary axiom `T._native.native_decide.ax_1_1` of a theorem `T` of
the same module, where
  * `T : @Eq Bool (f a₁ … aₙ) true` with `f` = `Autocorr.Cert.checkJobStrX` or `Autocorr.Cert.checkGroupStrX`, and
  * the axiom's type is `@Eq Bool (Decidable.decide (@Eq Bool (g a₁ … aₙ) true) inst) true` with `g` the matching
    `Autocorr.Cert.checkJobStrXF` / `Autocorr.Cert.checkGroupStrXF` and the SAME arguments (Expr equality);
  or the one root check of the package: `T` = `PREFIX rootOK : (Autocorr.Cert.rootBox (Autocorr.Cert.mkSpec n)).isSome = true`
  and the axiom decides exactly `T`'s statement.
Anything else is a violation.
-/
open Lean

def bannedNames : List String := ["sorryAx", "Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler"]

def banned (pre : String) (n : Name) : Bool :=
  let s := n.toString
  bannedNames.contains s || ((s.splitOn "_native").length > 1 && !s.startsWith pre)

def swapOf (f : Name) : Option Name :=
  if f == `Autocorr.Cert.checkJobStrX then some `Autocorr.Cert.checkJobStrXF
  else if f == `Autocorr.Cert.checkGroupStrX then some `Autocorr.Cert.checkGroupStrXF
  else none

/-- `@Eq Bool lhs true` -> lhs -/
def eqTrueLhs? (e : Expr) : Option Expr :=
  match e.eq? with
  | some (ty, lhs, rhs) => if ty.isConstOf ``Bool && rhs.isConstOf ``Bool.true then some lhs else none
  | none => none

/-- `none` if the auxiliary axiom `c` matches its theorem in `consts`, else the reason. -/
def checkAux (pre : String) (consts : Std.HashMap Name ConstantInfo) (c : ConstantInfo) : Option String :=
  let s := c.name.toString
  if !(s.startsWith pre && s.endsWith "._native.native_decide.ax_1_1") then some "not a native_decide aux of the package"
  else
    let thm := c.name.getPrefix.getPrefix.getPrefix
    match consts.get? thm with
    | none => some s!"theorem {thm} not in the module"
    | some t =>
      match eqTrueLhs? t.type, eqTrueLhs? c.type with
      | some tl, some al =>
        if !al.isAppOfArity ``Decidable.decide 2 then some "aux lhs is not decide" else
        match eqTrueLhs? (al.getArg! 0) with
        | none => some "decided proposition is not `_ = true`"
        | some dl =>
          match swapOf tl.getAppFn.constName with
          | none =>
            if thm.toString == pre ++ "rootOK" && tl.isAppOfArity ``Option.isSome 2
                && (tl.getArg! 1).isAppOfArity `Autocorr.Cert.rootBox 1
                && ((tl.getArg! 1).getArg! 0).isAppOfArity `Autocorr.Cert.mkSpec 1
                && dl == tl then none
            else some s!"theorem head {tl.getAppFn.constName} is not checkJobStrX/checkGroupStrX (and not the rootOK check)"
          | some g =>
            if !dl.getAppFn.isConstOf g then some s!"aux head {dl.getAppFn.constName} is not {g}"
            else if tl.getAppArgs != dl.getAppArgs then some "arguments differ"
            else none
      | _, _ => some "types are not `_ = true`"

def main (args : List String) : IO UInt32 := do
  let [list, out, pre] := args | do IO.eprintln "usage: nscan_xf LIST OUT PREFIX"; return 2
  let files := (← IO.FS.readFile list).splitOn "\n" |>.filter (· ≠ "")
  let mut ext : NameSet := {}
  let mut viol : Array String := #[]
  let mut nmods := 0
  let mut nconst := 0
  let mut heads : Std.HashMap String Nat := {}
  for f in files do
    let (md, _region) ← readModuleData f
    nmods := nmods + 1
    let consts : Std.HashMap Name ConstantInfo := md.constants.foldl (fun m c => m.insert c.name c) {}
    for c in md.constants do
      nconst := nconst + 1
      if c matches .axiomInfo _ then
        match checkAux pre consts c with
        | none =>
          let k := match eqTrueLhs? c.type with
            | some al => match eqTrueLhs? (al.getArg! 0) with
              | some dl => dl.getAppFn.constName.toString
              | none => "?"
            | none => "?"
          heads := heads.insert k (heads.getD k 0 + 1)
        | some why => viol := viol.push s!"axiom {c.name} in {f}: {why}"
      let mut used := c.type.getUsedConstants
      if let some v := c.value? then
        used := used ++ v.getUsedConstants
      for u in used do
        if banned pre u then
          viol := viol.push s!"{c.name} uses {u} ({f})"
        else if !(u.toString.startsWith pre) then
          ext := ext.insert u
  let lines := ext.toList.map toString |>.toArray.qsort (· < ·)
  let hs := heads.toList.map (fun (h, k) => s!"{h} {k}") |>.toArray.qsort (· < ·)
  IO.FS.writeFile out (s!"modules {nmods} constants {nconst} violations {viol.size}\n" ++
    "native_axioms_by_decided_head (each matched to its theorem: head swapped, arguments identical)\n" ++
    String.intercalate "\n" hs.toList ++ "\nviolations\n" ++
    String.intercalate "\n" viol.toList ++ (if viol.isEmpty then "" else "\n") ++
    "external\n" ++ String.intercalate "\n" lines.toList ++ "\n")
  return 0
