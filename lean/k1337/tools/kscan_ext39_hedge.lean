import AutocorrK39.Table
import AutocorrK39.Stk
import AutocorrK39.Load
import AutocorrK39.Sound.Run
import Autocorr.Reduction
import Autocorr.RealForm
import AutocorrK39v2.Table
import AutocorrK39v2.Stk
import AutocorrK39v2.Load
import AutocorrK39v2.Sound.Run
import AutocorrK39v2.Bridge
/-!
kscan_ext39_hedge.lean = tools/kscan_ext39.lean with the namespaced v2 library (AutocorrK39v2.*, its
Bridge) also imported, for the K1337 v2-hedge assembly whose three v2 job modules reference AutocorrK2 constants.
Second step of the per-module axiom scan (tools/kscan.lean): the axioms of every constant that the package's modules
reference outside the package, computed in an environment that holds only the hand-written library and Mathlib.
Reads the external-reference list from the file named by the environment variable KSCAN_EXT (one name per line) and
prints the union of their axioms; a name missing from this environment is reported (it would have to come from the
package itself, which kscan.lean rules out by construction).
-/
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let path := (← IO.getEnv "KSCAN_EXT").getD ""
  let names := (← IO.FS.readFile path).splitOn "\n" |>.filter (· ≠ "")
  let env ← getEnv
  let mut axs : NameSet := {}
  let mut missing : Array String := #[]
  for s in names do
    let n := s.toName
    if env.contains n then
      for a in ← liftCoreM (Lean.collectAxioms n) do
        axs := axs.insert a
    else
      missing := missing.push s
  IO.println s!"external references {names.length}; missing {missing.size} {missing.toList.take 10}"
  IO.println s!"axioms of the external references: {axs.toList}"
