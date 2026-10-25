import AutocorrK39.Sound.Run
import AutocorrK39v2.Sound.Run

/-!
# Bridge from the namespaced v2 copy to the v1 semantic statements

`AutocorrK39v2` is the audited v2 library under the namespace `AutocorrK2` (a scripted rename). Its semantic statements
(`SegK`, `StackOKK`, `BoxOKK`, `InBoxK`) are the v1 ones word for word, over the same shared `Autocorr.Cert` definitions;
the only constants they mention from the checker are `get32`, defined identically in both. So each v2 statement is
definitionally the v1 statement, and these bridges are the identity.
-/

namespace AutocorrK2

open Autocorr.Cert

theorem segK_to_v1 {sp : Spec} {lam : ℝ} {sin sout : List (ℕ × ℕ)} (h : AutocorrK2.SegK sp lam sin sout) :
    AutocorrK.SegK sp lam sin sout := h

theorem stackOKK_to_v1 {sp : Spec} {lam : ℝ} {stk : List (ℕ × ℕ)} (h : AutocorrK2.StackOKK sp lam stk) :
    AutocorrK.StackOKK sp lam stk := h

end AutocorrK2
