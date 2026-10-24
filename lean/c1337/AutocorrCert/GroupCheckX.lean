import AutocorrCert.DecodeX

/-!
PROPOSAL (statement review before any generation): one native_decide per module instead of one per job.

Today every job J of a module has its own `theorem chk : checkJobStrX n lam zo "<root>" [<children>] recs = true :=
by native_decide` and `theorem covered : CoveredX n lam zo "<root>"`.  At n = 39 that is 13,678,676 native_decide
auxiliary axioms and ~55M constants, and Lean writes, for every `covered`, the list of all native axioms below it.

Proposed: a module carries its jobs as one list (post-order, the module's root job last), ONE native_decide over that
list, and ONE `covered` theorem (for the module's root); jobs whose subtree root lives in another module are reached
through that module's `covered` (an `ext` root).  Soundness rests on the unchanged `CoveredX` / `checkJobStrX` (the
final theorem still goes through `halfClaim_of_coveredX`); the only new trusted evaluation is `checkGroupStrX`, which
calls `checkJobStrX` on every job and checks by string equality that every delegated child is an earlier job of the
module or an `ext` root.
-/

namespace Autocorr.Cert

/-- One job: root path, delegated child paths (record order), encoded records (the exporter's strings, as for
`checkJobStrX`). -/
abbrev JobStrX := String × List String × String

/-- The jobs of one module in post-order. `seen` = roots of the jobs already checked (initially `[]`); `ext` = subtree
roots proved in imported modules. Every job must pass `checkJobStrX`, and each delegated child must be in `seen` or
in `ext`. -/
def checkGroupStrX (n : Nat) (lam : Rat) (zo : String) (ext : List String) :
    List String → List JobStrX → Bool
  | _, [] => true
  | seen, (root, children, recs) :: rest =>
      checkJobStrX n lam zo root children recs &&
      children.all (fun c => seen.contains c || ext.contains c) &&
      checkGroupStrX n lam zo ext (root :: seen) rest

/-- Every job of a checked group is covered, given that the imported roots are. -/
theorem coveredX_of_checkGroupStrX_seen {n : Nat} {lam : Rat} {zo : String} {ext : List String}
    (hext : ∀ c ∈ ext, CoveredX n lam zo c) :
    ∀ (jobs : List JobStrX) (seen : List String), checkGroupStrX n lam zo ext seen jobs = true →
      (∀ c ∈ seen, CoveredX n lam zo c) → ∀ j ∈ jobs, CoveredX n lam zo j.1
  | [], _, _, _, j, hj => absurd hj List.not_mem_nil
  | (root, children, recs) :: rest, seen, h, hseen, j, hj => by
    simp only [checkGroupStrX, Bool.and_eq_true] at h
    obtain ⟨⟨hjob, hch⟩, hrest⟩ := h
    have hroot : CoveredX n lam zo root := by
      refine CoveredX.mk root children recs hjob ?_
      intro c hc
      have hc' := List.all_eq_true.mp hch c hc
      simp only [Bool.or_eq_true, List.contains_iff_mem] at hc'
      rcases hc' with h1 | h2
      · exact hseen c h1
      · exact hext c h2
    rcases List.mem_cons.mp hj with rfl | hj'
    · exact hroot
    · refine coveredX_of_checkGroupStrX_seen hext rest (root :: seen) hrest ?_ j hj'
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact hroot
      · exact hseen c hc'

theorem coveredX_of_checkGroupStrX {n : Nat} {lam : Rat} {zo : String} {ext : List String} {jobs : List JobStrX}
    (h : checkGroupStrX n lam zo ext [] jobs = true) (hext : ∀ c ∈ ext, CoveredX n lam zo c) :
    ∀ j ∈ jobs, CoveredX n lam zo j.1 :=
  coveredX_of_checkGroupStrX_seen hext jobs [] h (fun _ hc => absurd hc List.not_mem_nil)

/-- The form the generated modules use: the module's root job is the last element. -/
theorem coveredX_root_of_checkGroupStrX {n : Nat} {lam : Rat} {zo : String} {ext : List String}
    {jobs : List JobStrX} {root : String} {children : List String} {recs : String}
    (h : checkGroupStrX n lam zo ext [] (jobs ++ [(root, children, recs)]) = true)
    (hext : ∀ c ∈ ext, CoveredX n lam zo c) :
    CoveredX n lam zo root :=
  coveredX_of_checkGroupStrX h hext (root, children, recs) (List.mem_append_right _ (List.mem_singleton_self _))

end Autocorr.Cert

/-
Generated module (sketch):
  import Autocorr.PKG.Zo
  import <modules of the ext roots>
  namespace Autocorr.PKG.G<id>
  def jobs : List Autocorr.Cert.JobStrX := [("<root1>", ["<c11>", ...], "<recs1>"), ...]   -- all but the module root
  theorem chk : Autocorr.Cert.checkGroupStrX N LAM Autocorr.PKG.zo ["<ext1>", ...] []
      (jobs ++ [("<root>", ["<c1>", ...], "<recs>")]) = true := by native_decide
  theorem covered : Autocorr.Cert.CoveredX N LAM Autocorr.PKG.zo "<root>" :=
    Autocorr.Cert.coveredX_root_of_checkGroupStrX chk
      (Autocorr.Cert.AllCoveredX.mem ⟨Autocorr.PKG.G<e1>.covered, ..., trivial⟩)
  end Autocorr.PKG.G<id>
Effect at n = 39: ~250k native aux axioms (one per module) instead of 13.7M; ~0.5M package constants instead of ~55M;
axiom lists grow with modules, not jobs.  The assembly module is the same construction over the top jobs.
-/
