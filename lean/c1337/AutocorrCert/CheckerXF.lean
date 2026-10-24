import AutocorrCert.GroupCheckX

/-!
# CheckerXF: a faster evaluation of the extended checker, proved equal to it

`checkJobStrXF` / `checkGroupStrXF` compute the same Booleans as `checkJobStrX` / `checkGroupStrX` for all inputs
(`checkJobStrXF_eq`, `checkGroupStrXF_eq`; standard axioms only). Generated modules keep stating
`checkJobStrX ... = true` (resp. `checkGroupStrX`) and prove it by `rw [← checkJobStrXF_eq]; native_decide`, so the
compiled code that runs is the fast one while `CoveredX`, `SoundX` and the final statements are unchanged.

The fast leaf bound for a compressed leaf (`RecX.leafc ys`), `leafcBoundXF`:
1. one pass over the listed duals: base rows as `dualStepX` (row built once); square rows expanded on the fly with
   integer coefficients and accumulated in an `Int` vector at the common scale `D = lcm` of their multipliers'
   denominators (exact); no `entOK` pass for squares (implied by `keyOKX` once `sp.wf`);
2. the completion (`completeX`'s G/P/ZA duals) computed from that state, and the ZA rows scattered once, by the
   completion itself (used when every key of `zo` is a valid ZA key; otherwise the shipped `dualBoundX`);
3. `colPart` skipping zero entries.
Statement reviewed and approved before the proofs were written.
-/

namespace Autocorr.Cert

/-- Integer entries of the square-cut row, in `sqEnt` order: `sqEnt sp v0 ts = (sqEntI sp v0 ts).map (·, ·)`. -/
def sqEntI (sp : Spec) (v0 : Int) : List (Nat × Int) → List (Nat × Int)
  | [] => []
  | (b, v) :: rest => (sp.canon b b, v * v) :: (b, 2 * v0 * v) ::
      (rest.map (fun t => (sp.canon b t.1, 2 * v * t.2)) ++ sqEntI sp v0 rest)

/-- `acc_k += c · a` for every entry `(k, a)` (integers). -/
def scatterI (acc : Array Int) (c : Int) : List (Nat × Int) → Array Int
  | [] => acc
  | (k, a) :: rest => scatterI (acc.modify k (· + c * a)) c rest

/-- `scatterI acc c (sqEntI sp v0 ts)` without building the entry list (to be proved equal). -/
def sqScatterI (sp : Spec) (c v0 : Int) : Array Int → List (Nat × Int) → Array Int
  | acc, [] => acc
  | acc, (b, v) :: rest =>
    let acc := acc.modify (sp.canon b b) (· + c * (v * v))
    let acc := acc.modify b (· + c * (2 * v0 * v))
    let acc := rest.foldl (fun a t => a.modify (sp.canon b t.1) (· + c * (2 * v * t.2))) acc
    sqScatterI sp c v0 acc rest

/-- One listed dual of a compressed leaf: base rows exactly as `dualStepX`; a square row with `y > 0` adds
`y · (-v0²)` to the scalar and `-(y·D)` times its integer entries to the integer vector (`y·D` is an integer). -/
def stepXF (sp : Spec) (bx : Box) (D : Nat) (st : Rat × Array Rat × Array Int) (ky : XKey × Rat) :
    Rat × Array Rat × Array Int :=
  match ky.1 with
  | .base k =>
    let row := rowOf sp bx k
    if keyOK sp k && entOK sp row.ent then
      if 0 < ky.2 then
        match row.lo with
        | some l => (st.1 + ky.2 * l, scatter st.2.1 (-ky.2) row.ent, st.2.2)
        | none => st
      else if ky.2 < 0 then
        match row.up with
        | some u => (st.1 + ky.2 * u, scatter st.2.1 (-ky.2) row.ent, st.2.2)
        | none => st
      else st
    else st
  | .sq v0 ts =>
    if keyOKX sp (.sq v0 ts) && 0 < ky.2 then
      (st.1 + ky.2 * (-((v0 : Rat) * v0)), st.2.1,
        sqScatterI sp (-(ky.2.num * ((D / ky.2.den : Nat) : Int))) v0 st.2.2 ts)
    else st

/-- Common denominator of the square multipliers of a leaf. -/
def sqDen (ys : List (XKey × Rat)) : Nat :=
  ys.foldl (fun d ky => match ky.1 with | .sq _ _ => Nat.lcm d ky.2.den | .base _ => d) 1

/-- `colPart` without the products of zero entries. -/
def colPartZ (sp : Spec) (bx : Box) (r : Array Rat) : Rat :=
  (List.range sp.NC).foldl
    (fun acc k => let v := r.getD k 0; if v == 0 then acc else acc + min (v * lbOf sp bx k) (v * ubOf sp bx k)) 0

/-- Every key of `zo` is a valid ZA key (true for the generated `zo`). -/
def zoOK (sp : Spec) (zo : List RowKey) : Bool :=
  zo.all (fun k => match k with
    | .ZA _ _ _ => keyOK sp k && entOK sp (rowOf sp ⟨#[], #[]⟩ k).ent
    | _ => false)

/-- The bound of a compressed leaf (`dualBoundX sp bx true (ys ++ completeX sp bx zo ys)`, computed faster). -/
def leafcBoundXF (sp : Spec) (bx : Box) (zo : List RowKey) (ys : List (XKey × Rat)) : Rat :=
  if zoOK sp zo then
    let D := sqDen ys
    let st := ys.foldl (stepXF sp bx D) (0, Array.replicate sp.NC (0 : Rat), Array.replicate sp.NC (0 : Int))
    let r := (List.range sp.NC).foldl (fun (acc : Array Rat) c =>
        let v := st.2.2.getD c 0
        if v == 0 then acc else acc.modify c (· + mkRat v D)) st.2.1
    let m := 2 * sp.n - 1
    let gs : List (Nat × Rat) := (List.range m).foldl (fun acc i =>
        let c := m - 1 - i
        let prev := match acc with | [] => 0 | (_, y) :: _ => y
        (c, prev + r.getD (sp.oG + c) 0) :: acc) []
    let gp : List (XKey × Rat) := gs.foldr (fun cy acc =>
        (.base (.G cy.1), cy.2) :: (.base (.P cy.1), cy.2 + r.getD (sp.oP + cy.1) 0) :: acc) []
    let rza := zo.foldl (fun (a : Array Rat) k =>
        match k with
        | .ZA d e _ => scatter a (-(a.getD (sp.canon d e) 0)) (rowOf sp bx k).ent
        | _ => a) r
    let fin := gp.foldl (dualStepX sp bx) (st.1, rza.setIfInBounds sp.oT (rza.getD sp.oT 0 + 1))
    fin.1 + colPartZ sp bx fin.2
  else dualBoundX sp bx true (ys ++ completeX sp bx zo ys)

def runXF (sp : Spec) (lam : Rat) (zo : List RowKey) : List RecX → List Box → Option (List Box)
  | [], stk => some stk
  | _ :: _, [] => none
  | .split b s :: rs, bx :: stk =>
    runXF sp lam zo rs ((child sp bx b s true).toList ++ (child sp bx b s false).toList ++ stk)
  | .leaf ys :: rs, bx :: stk =>
    if lam ≤ dualBoundX sp bx true ys then runXF sp lam zo rs stk else none
  | .farkas ys :: rs, bx :: stk =>
    if 0 < dualBoundX sp bx false ys then runXF sp lam zo rs stk else none
  | .deleg :: rs, bx :: stk => (runXF sp lam zo rs stk).map (bx :: ·)
  | .leafc ys :: rs, bx :: stk =>
    if lam ≤ leafcBoundXF sp bx zo ys then runXF sp lam zo rs stk else none

def checkJobXF (sp : Spec) (lam : Rat) (zo : List RowKey) (root : Path) (children : List Path)
    (recs : List RecX) : Bool :=
  sp.wf && decide (lam ≤ 3) &&
  match regionOfPath sp root with
  | none => true
  | some R => decide (runXF sp lam zo recs [R] = some (children.filterMap (regionOfPath sp)))

def checkJobStrXF (n : Nat) (lam : Rat) (zo : String) (root : String) (children : List String) (recs : String) :
    Bool :=
  checkJobXF (mkSpec n) lam (Dec.decodeKeys zo) (Dec.decodePath root) (children.map Dec.decodePath)
    (Dec.decodeRecsX recs)

def checkGroupStrXF (n : Nat) (lam : Rat) (zo : String) (ext : List String) :
    List String → List JobStrX → Bool
  | _, [] => true
  | seen, (root, children, recs) :: rest =>
      checkJobStrXF n lam zo root children recs &&
      children.all (fun c => seen.contains c || ext.contains c) &&
      checkGroupStrXF n lam zo ext (root :: seen) rest

/-! ## Proof of the equality (helper lemmas, namespace `XFP`)

Pointwise bookkeeping: for an index `i` below the array size, every `dualStepX` adds a fixed scalar (`stS`) and a
fixed amount at `i` (`stD`, a sum `scD` over the row entries); a fold adds the sums `sumS` / `sumD`.  The fast fold
`stepXF` splits `stD` into its base-row part (`fDb`, rational vector) and its square-row part (`fDI`, integer vector
at scale `D`), and `rB_i + acc_i / D` recovers the shipped vector (`rF_eq`).  The completion's ZA fold adds the same
amounts as its listed ZA duals (`zaFold_getD`), all G/P/ZA rows have zero bounds, and `colPartZ = colPart`. -/

namespace XFP

/-! ### Arrays, `scatter` and the shipped step -/

theorem getD_modify {α} (a : Array α) (k i : Nat) (f : α → α) (d : α) (hi : i < a.size) :
    (a.modify k f).getD i d = if k = i then f (a.getD i d) else a.getD i d := by
  simp [hi, Array.getElem_modify]

theorem getD_setIfInBounds {α} (a : Array α) (k i : Nat) (v : α) (d : α) (hi : i < a.size) :
    (a.setIfInBounds k v).getD i d = if k = i then v else a.getD i d := by
  simp [hi, Array.getElem_setIfInBounds]

theorem getD_replicate {α} (n i : Nat) (v d : α) (hi : i < n) :
    (Array.replicate n v).getD i d = v := by
  simp [hi]

/-- Increment at index `i` of `scatter _ c ent`. -/
def scD (i : Nat) (c : Rat) : List (Nat × Rat) → Rat
  | [] => 0
  | (k, a) :: rest => (if k = i then c * a else 0) + scD i c rest

theorem size_scatter (r : Array Rat) (c : Rat) (ent : List (Nat × Rat)) :
    (scatter r c ent).size = r.size := by
  induction ent generalizing r with
  | nil => rfl
  | cons e rest ih => obtain ⟨k, a⟩ := e; simp [scatter, ih]

theorem getD_scatter (r : Array Rat) (c : Rat) (ent : List (Nat × Rat)) (i : Nat) (hi : i < r.size) :
    (scatter r c ent).getD i 0 = r.getD i 0 + scD i c ent := by
  induction ent generalizing r with
  | nil => simp [scatter, scD, Rat.add_zero]
  | cons e rest ih =>
    obtain ⟨k, a⟩ := e
    simp only [scatter, scD]
    rw [ih _ (by simpa using hi), getD_modify _ _ _ _ _ hi]
    split <;> grind

theorem scD_zero (i : Nat) (ent : List (Nat × Rat)) : scD i 0 ent = 0 := by
  induction ent with
  | nil => rfl
  | cons e rest ih => obtain ⟨k, a⟩ := e; simp [scD, ih, Rat.add_zero]

/-- Scalar increment of one `dualStepX`. -/
def stS (sp : Spec) (bx : Box) (ky : XKey × Rat) : Rat :=
  if keyOKX sp ky.1 && entOK sp (rowOfX sp bx ky.1).ent then
    if 0 < ky.2 then
      match (rowOfX sp bx ky.1).lo with
      | some l => ky.2 * l
      | none => 0
    else if ky.2 < 0 then
      match (rowOfX sp bx ky.1).up with
      | some u => ky.2 * u
      | none => 0
    else 0
  else 0

/-- Increment at index `i` of one `dualStepX`. -/
def stD (sp : Spec) (bx : Box) (i : Nat) (ky : XKey × Rat) : Rat :=
  if keyOKX sp ky.1 && entOK sp (rowOfX sp bx ky.1).ent then
    if 0 < ky.2 then
      match (rowOfX sp bx ky.1).lo with
      | some _ => scD i (-ky.2) (rowOfX sp bx ky.1).ent
      | none => 0
    else if ky.2 < 0 then
      match (rowOfX sp bx ky.1).up with
      | some _ => scD i (-ky.2) (rowOfX sp bx ky.1).ent
      | none => 0
    else 0
  else 0

theorem dualStepX_fst (sp : Spec) (bx : Box) (st : Rat × Array Rat) (ky : XKey × Rat) :
    (dualStepX sp bx st ky).1 = st.1 + stS sp bx ky := by
  unfold dualStepX stS
  generalize rowOfX sp bx ky.1 = row
  obtain ⟨lo, up, ent⟩ := row
  by_cases h1 : (keyOKX sp ky.1 && entOK sp ent) = true
  · simp only [ite_eq_left h1]
    by_cases h2 : 0 < ky.2
    · simp only [ite_eq_left h2]
      cases lo
      · simp only [Rat.add_zero]
      · rfl
    · simp only [ite_eq_right h2]
      by_cases h3 : ky.2 < 0
      · simp only [ite_eq_left h3]
        cases up
        · simp only [Rat.add_zero]
        · rfl
      · simp only [ite_eq_right h3, Rat.add_zero]
  · simp only [ite_eq_right h1, Rat.add_zero]

theorem dualStepX_size (sp : Spec) (bx : Box) (st : Rat × Array Rat) (ky : XKey × Rat) :
    (dualStepX sp bx st ky).2.size = st.2.size := by
  unfold dualStepX
  generalize rowOfX sp bx ky.1 = row
  obtain ⟨lo, up, ent⟩ := row
  by_cases h1 : (keyOKX sp ky.1 && entOK sp ent) = true
  · simp only [ite_eq_left h1]
    by_cases h2 : 0 < ky.2
    · simp only [ite_eq_left h2]
      cases lo
      · rfl
      · exact size_scatter _ _ _
    · simp only [ite_eq_right h2]
      by_cases h3 : ky.2 < 0
      · simp only [ite_eq_left h3]
        cases up
        · rfl
        · exact size_scatter _ _ _
      · simp only [ite_eq_right h3]
  · simp only [ite_eq_right h1]

theorem dualStepX_getD (sp : Spec) (bx : Box) (st : Rat × Array Rat) (ky : XKey × Rat) (i : Nat)
    (hi : i < st.2.size) :
    (dualStepX sp bx st ky).2.getD i 0 = st.2.getD i 0 + stD sp bx i ky := by
  unfold dualStepX stD
  generalize rowOfX sp bx ky.1 = row
  obtain ⟨lo, up, ent⟩ := row
  by_cases h1 : (keyOKX sp ky.1 && entOK sp ent) = true
  · simp only [ite_eq_left h1]
    by_cases h2 : 0 < ky.2
    · simp only [ite_eq_left h2]
      cases lo
      · simp only [Rat.add_zero]
      · exact getD_scatter _ _ _ _ hi
    · simp only [ite_eq_right h2]
      by_cases h3 : ky.2 < 0
      · simp only [ite_eq_left h3]
        cases up
        · simp only [Rat.add_zero]
        · exact getD_scatter _ _ _ _ hi
      · simp only [ite_eq_right h3, Rat.add_zero]
  · simp only [ite_eq_right h1, Rat.add_zero]

def sumS (sp : Spec) (bx : Box) : List (XKey × Rat) → Rat
  | [] => 0
  | ky :: l => stS sp bx ky + sumS sp bx l

def sumD (sp : Spec) (bx : Box) (i : Nat) : List (XKey × Rat) → Rat
  | [] => 0
  | ky :: l => stD sp bx i ky + sumD sp bx i l

theorem sumS_append (sp : Spec) (bx : Box) (l1 l2 : List (XKey × Rat)) :
    sumS sp bx (l1 ++ l2) = sumS sp bx l1 + sumS sp bx l2 := by
  induction l1 with
  | nil => simp [sumS, Rat.zero_add]
  | cons x l ih => simp [sumS, ih, Rat.add_assoc]

theorem sumD_append (sp : Spec) (bx : Box) (i : Nat) (l1 l2 : List (XKey × Rat)) :
    sumD sp bx i (l1 ++ l2) = sumD sp bx i l1 + sumD sp bx i l2 := by
  induction l1 with
  | nil => simp [sumD, Rat.zero_add]
  | cons x l ih => simp [sumD, ih, Rat.add_assoc]

theorem foldX_fst (sp : Spec) (bx : Box) (l : List (XKey × Rat)) (st : Rat × Array Rat) :
    (l.foldl (dualStepX sp bx) st).1 = st.1 + sumS sp bx l := by
  induction l generalizing st with
  | nil => simp [sumS, Rat.add_zero]
  | cons x l ih => simp [List.foldl, sumS, ih, dualStepX_fst, Rat.add_assoc]

theorem foldX_size (sp : Spec) (bx : Box) (l : List (XKey × Rat)) (st : Rat × Array Rat) :
    (l.foldl (dualStepX sp bx) st).2.size = st.2.size := by
  induction l generalizing st with
  | nil => rfl
  | cons x l ih => simp [List.foldl, ih, dualStepX_size]

theorem foldX_getD (sp : Spec) (bx : Box) (l : List (XKey × Rat)) (st : Rat × Array Rat) (i : Nat)
    (hi : i < st.2.size) :
    (l.foldl (dualStepX sp bx) st).2.getD i 0 = st.2.getD i 0 + sumD sp bx i l := by
  induction l generalizing st with
  | nil => simp [sumD, Rat.add_zero]
  | cons x l ih =>
    simp only [List.foldl, sumD]
    rw [ih _ (by rw [dualStepX_size]; exact hi), dualStepX_getD _ _ _ _ _ hi, Rat.add_assoc]

/-! ### Integer scatter -/

def scDI (i : Nat) (c : Int) : List (Nat × Int) → Int
  | [] => 0
  | (k, a) :: rest => (if k = i then c * a else 0) + scDI i c rest

theorem size_scatterI (acc : Array Int) (c : Int) (ent : List (Nat × Int)) :
    (scatterI acc c ent).size = acc.size := by
  induction ent generalizing acc with
  | nil => rfl
  | cons e rest ih => obtain ⟨k, a⟩ := e; simp [scatterI, ih]

theorem getD_scatterI (acc : Array Int) (c : Int) (ent : List (Nat × Int)) (i : Nat) (hi : i < acc.size) :
    (scatterI acc c ent).getD i 0 = acc.getD i 0 + scDI i c ent := by
  induction ent generalizing acc with
  | nil => simp [scatterI, scDI]
  | cons e rest ih =>
    obtain ⟨k, a⟩ := e
    simp only [scatterI, scDI]
    rw [ih _ (by simpa using hi), getD_modify _ _ _ _ _ hi]
    by_cases h : k = i
    · rw [ite_eq_left h, ite_eq_left h]; grind
    · rw [ite_eq_right h, ite_eq_right h]; grind

theorem scatterI_append (acc : Array Int) (c : Int) (l1 l2 : List (Nat × Int)) :
    scatterI acc c (l1 ++ l2) = scatterI (scatterI acc c l1) c l2 := by
  induction l1 generalizing acc with
  | nil => rfl
  | cons e rest ih => obtain ⟨k, a⟩ := e; simp [scatterI, ih]

theorem scatterI_map (acc : Array Int) (c : Int) (g : Nat × Int → Nat) (h : Nat × Int → Int)
    (l : List (Nat × Int)) :
    scatterI acc c (l.map (fun t => (g t, h t))) = l.foldl (fun a t => a.modify (g t) (· + c * h t)) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons t rest ih => simp [scatterI, ih]

theorem sqScatterI_eq (sp : Spec) (c v0 : Int) (acc : Array Int) (ts : List (Nat × Int)) :
    sqScatterI sp c v0 acc ts = scatterI acc c (sqEntI sp v0 ts) := by
  induction ts generalizing acc with
  | nil => rfl
  | cons t rest ih =>
    obtain ⟨b, v⟩ := t
    simp only [sqScatterI, sqEntI, scatterI, scatterI_append, ih]
    rw [scatterI_map]

theorem sqEnt_eq (sp : Spec) (v0 : Int) (ts : List (Nat × Int)) :
    sqEnt sp v0 ts = (sqEntI sp v0 ts).map (fun e => (e.1, (e.2 : Rat))) := by
  induction ts with
  | nil => rfl
  | cons t rest ih =>
    obtain ⟨b, v⟩ := t
    simp [sqEnt, sqEntI, ih, List.map_append, List.map_map, Rat.intCast_mul]

/-! ### Rational identities -/

theorem intCast_eq_mkRat (a : Int) : (a : Rat) = mkRat a 1 := by
  have := Rat.mkRat_self (a : Rat)
  rw [Rat.num_intCast, Rat.den_intCast] at this
  exact this.symm

theorem mkRat_add_same (x y : Int) (D : Nat) (hD : D ≠ 0) : mkRat (x + y) D = mkRat x D + mkRat y D := by
  rw [Rat.mkRat_add_mkRat x y hD hD]
  have : x * (D : Int) + y * (D : Int) = (x + y) * ((D : Nat) : Int) := by grind
  rw [this, Rat.mkRat_mul_right hD]

theorem neg_mul_intCast (y : Rat) (D : Nat) (hD : D ≠ 0) (hden : y.den ∣ D) (a : Int) :
    (-y) * (a : Rat) = mkRat (-(y.num * ((D / y.den : Nat) : Int)) * a) D := by
  obtain ⟨k, hk⟩ := hden
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hD (by simpa using hk)
  have hdiv : D / y.den = k := by
    rw [hk]; exact Nat.mul_div_cancel_left k y.den_pos
  rw [hdiv, hk]
  have e1 : -(y.num * (k : Int)) * a = (-y.num * a) * ((k : Nat) : Int) := by grind
  rw [e1, Rat.mkRat_mul_right hk0]
  conv => lhs; rw [← Rat.mkRat_self y]
  rw [Rat.neg_mkRat, intCast_eq_mkRat a, Rat.mkRat_mul_mkRat, Nat.mul_one]

theorem scD_cast (i : Nat) (y : Rat) (c : Int) (D : Nat)
    (hyc : ∀ a : Int, (-y) * (a : Rat) = mkRat (c * a) D) (hD : D ≠ 0) (ent : List (Nat × Int)) :
    scD i (-y) (ent.map (fun e => (e.1, (e.2 : Rat)))) = mkRat (scDI i c ent) D := by
  induction ent with
  | nil => simp [scD, scDI]
  | cons e rest ih =>
    obtain ⟨k, a⟩ := e
    simp only [List.map_cons, scD, scDI, ih]
    by_cases h : k = i
    · rw [ite_eq_left h, ite_eq_left h, hyc a, mkRat_add_same _ _ _ hD]
    · rw [ite_eq_right h, ite_eq_right h, Int.zero_add, Rat.zero_add]

/-! ### Well-formedness bounds -/

theorem wf_blk (sp : Spec) (hwf : sp.wf = true) (b : Nat) (hb : b < sp.nB) :
    (sp.blk b).lo < (sp.blk b).hi ∧ (sp.blk b).hi ≤ sp.n := by
  unfold Spec.wf at hwf
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hwf
  have := hwf.1.2 b hb
  simp only [decide_eq_true_eq] at this
  exact this.1

theorem canon_lt (sp : Spec) (hwf : sp.wf = true) (d e : Nat) (hd : d < sp.nB) (he : e < sp.nB) :
    sp.canon d e < sp.NC := by
  have h1 := wf_blk sp hwf d hd
  have h2 := wf_blk sp hwf e he
  unfold Spec.canon Spec.zIdx Spec.zaIdx Spec.NC Spec.oT Spec.oG Spec.oP Spec.oZA Spec.oZ
  split
  · have hm : min (sp.blk d).lo (sp.blk e).lo + 1 ≤ sp.n := by omega
    have := Nat.mul_le_mul_right sp.n hm
    rw [Nat.add_mul, Nat.one_mul] at this
    have : max (sp.blk d).lo (sp.blk e).lo < sp.n := by omega
    omega
  · have hm : min d e + 1 ≤ sp.nB := by omega
    have := Nat.mul_le_mul_right sp.nB hm
    rw [Nat.add_mul, Nat.one_mul] at this
    have : max d e < sp.nB := by omega
    omega

theorem blk_lt_NC (sp : Spec) (b : Nat) (hb : b < sp.nB) : b < sp.NC := by
  unfold Spec.NC Spec.oT Spec.oG Spec.oP Spec.oZA Spec.oZ
  omega

theorem entOK_sqEnt (sp : Spec) (hwf : sp.wf = true) (v0 : Int) (ts : List (Nat × Int))
    (hk : keyOKX sp (.sq v0 ts) = true) : entOK sp (sqEnt sp v0 ts) = true := by
  simp only [keyOKX, List.all_eq_true, decide_eq_true_eq] at hk
  induction ts with
  | nil => rfl
  | cons t rest ih =>
    obtain ⟨b, v⟩ := t
    have hb : b < sp.nB := hk (b, v) (List.mem_cons_self ..)
    have hrest : ∀ x ∈ rest, x.1 < sp.nB := fun x hx => hk x (List.mem_cons_of_mem _ hx)
    have ih' := ih hrest
    simp only [entOK, List.all_eq_true, decide_eq_true_eq] at ih'
    simp only [sqEnt, entOK, List.all_eq_true, decide_eq_true_eq, List.mem_cons, List.mem_append,
      List.mem_map]
    intro x hx
    rcases hx with rfl | rfl | ⟨t, ht, rfl⟩ | hx
    · exact canon_lt sp hwf b b hb hb
    · exact blk_lt_NC sp b hb
    · exact canon_lt sp hwf b t.1 hb (hrest t ht)
    · exact ih' x hx

/-! ### One step of the fast fold -/

def fDb (sp : Spec) (bx : Box) (i : Nat) (ky : XKey × Rat) : Rat :=
  match ky.1 with
  | .base _ => stD sp bx i ky
  | .sq _ _ => 0

def fDI (sp : Spec) (D : Nat) (i : Nat) (ky : XKey × Rat) : Int :=
  match ky.1 with
  | .base _ => 0
  | .sq v0 ts => if (keyOKX sp (.sq v0 ts) && decide (0 < ky.2)) = true then
      scDI i (-(ky.2.num * ((D / ky.2.den : Nat) : Int))) (sqEntI sp v0 ts) else 0

theorem dualStepX_base (sp : Spec) (bx : Box) (st : Rat × Array Rat) (k : RowKey) (y : Rat) :
    dualStepX sp bx st (.base k, y) =
      (if (keyOK sp k && entOK sp (rowOf sp bx k).ent) = true then
        if 0 < y then
          match (rowOf sp bx k).lo with
          | some l => (st.1 + y * l, scatter st.2 (-y) (rowOf sp bx k).ent)
          | none => st
        else if y < 0 then
          match (rowOf sp bx k).up with
          | some u => (st.1 + y * u, scatter st.2 (-y) (rowOf sp bx k).ent)
          | none => st
        else st
      else st) := rfl

theorem stepXF_base' (sp : Spec) (bx : Box) (D : Nat) (st : Rat × Array Rat × Array Int) (k : RowKey)
    (y : Rat) :
    stepXF sp bx D st (.base k, y) =
      (if (keyOK sp k && entOK sp (rowOf sp bx k).ent) = true then
        if 0 < y then
          match (rowOf sp bx k).lo with
          | some l => (st.1 + y * l, scatter st.2.1 (-y) (rowOf sp bx k).ent, st.2.2)
          | none => st
        else if y < 0 then
          match (rowOf sp bx k).up with
          | some u => (st.1 + y * u, scatter st.2.1 (-y) (rowOf sp bx k).ent, st.2.2)
          | none => st
        else st
      else st) := rfl

theorem stepXF_base (sp : Spec) (bx : Box) (D : Nat) (st : Rat × Array Rat × Array Int) (k : RowKey)
    (y : Rat) :
    stepXF sp bx D st (.base k, y) =
      ((dualStepX sp bx (st.1, st.2.1) (.base k, y)).1, (dualStepX sp bx (st.1, st.2.1) (.base k, y)).2,
        st.2.2) := by
  rw [stepXF_base', dualStepX_base]
  generalize rowOf sp bx k = row
  obtain ⟨lo, up, ent⟩ := row
  by_cases h1 : (keyOK sp k && entOK sp ent) = true
  · simp only [ite_eq_left h1]
    by_cases h2 : 0 < y
    · simp only [ite_eq_left h2]; cases lo <;> rfl
    · simp only [ite_eq_right h2]
      by_cases h3 : y < 0
      · simp only [ite_eq_left h3]; cases up <;> rfl
      · simp only [ite_eq_right h3]
  · simp only [ite_eq_right h1]

theorem stepXF_sq (sp : Spec) (bx : Box) (D : Nat) (st : Rat × Array Rat × Array Int) (v0 : Int)
    (ts : List (Nat × Int)) (y : Rat) :
    stepXF sp bx D st (.sq v0 ts, y) =
      if (keyOKX sp (.sq v0 ts) && decide (0 < y)) = true then
        (st.1 + y * (-((v0 : Rat) * v0)), st.2.1,
          sqScatterI sp (-(y.num * ((D / y.den : Nat) : Int))) v0 st.2.2 ts)
      else st := rfl

theorem stS_sq (sp : Spec) (hwf : sp.wf = true) (bx : Box) (v0 : Int) (ts : List (Nat × Int)) (y : Rat) :
    stS sp bx (.sq v0 ts, y) =
      if (keyOKX sp (.sq v0 ts) && decide (0 < y)) = true then y * (-((v0 : Rat) * v0)) else 0 := by
  unfold stS
  simp only [rowOfX]
  by_cases hk : keyOKX sp (.sq v0 ts) = true
  · have he := entOK_sqEnt sp hwf v0 ts hk
    by_cases h2 : 0 < y
    · simp [hk, he, h2]
    · simp [hk, he, h2]
  · simp [hk]

theorem stD_sq (sp : Spec) (hwf : sp.wf = true) (bx : Box) (i : Nat) (v0 : Int) (ts : List (Nat × Int))
    (y : Rat) :
    stD sp bx i (.sq v0 ts, y) =
      if (keyOKX sp (.sq v0 ts) && decide (0 < y)) = true then scD i (-y) (sqEnt sp v0 ts) else 0 := by
  unfold stD
  simp only [rowOfX]
  by_cases hk : keyOKX sp (.sq v0 ts) = true
  · have he := entOK_sqEnt sp hwf v0 ts hk
    by_cases h2 : 0 < y
    · simp [hk, he, h2]
    · simp [hk, he, h2]
  · simp [hk]

theorem stepXF_fst (sp : Spec) (hwf : sp.wf = true) (bx : Box) (D : Nat) (st : Rat × Array Rat × Array Int)
    (ky : XKey × Rat) : (stepXF sp bx D st ky).1 = st.1 + stS sp bx ky := by
  obtain ⟨key, y⟩ := ky
  cases key with
  | base k => rw [stepXF_base]; exact dualStepX_fst sp bx (st.1, st.2.1) (.base k, y)
  | sq v0 ts =>
    rw [stepXF_sq, stS_sq sp hwf]
    by_cases h : (keyOKX sp (.sq v0 ts) && decide (0 < y)) = true
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h, Rat.add_zero]

theorem stepXF_size1 (sp : Spec) (bx : Box) (D : Nat) (st : Rat × Array Rat × Array Int)
    (ky : XKey × Rat) : (stepXF sp bx D st ky).2.1.size = st.2.1.size := by
  obtain ⟨key, y⟩ := ky
  cases key with
  | base k => rw [stepXF_base]; exact dualStepX_size sp bx (st.1, st.2.1) (.base k, y)
  | sq v0 ts =>
    rw [stepXF_sq]
    by_cases h : (keyOKX sp (.sq v0 ts) && decide (0 < y)) = true
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]

theorem stepXF_size2 (sp : Spec) (bx : Box) (D : Nat) (st : Rat × Array Rat × Array Int)
    (ky : XKey × Rat) : (stepXF sp bx D st ky).2.2.size = st.2.2.size := by
  obtain ⟨key, y⟩ := ky
  cases key with
  | base k => rw [stepXF_base]
  | sq v0 ts =>
    rw [stepXF_sq]
    by_cases h : (keyOKX sp (.sq v0 ts) && decide (0 < y)) = true
    · rw [ite_eq_left h]; dsimp only; rw [sqScatterI_eq, size_scatterI]
    · rw [ite_eq_right h]

theorem stepXF_getD1 (sp : Spec) (bx : Box) (D : Nat) (st : Rat × Array Rat × Array Int)
    (ky : XKey × Rat) (i : Nat) (hi : i < st.2.1.size) :
    (stepXF sp bx D st ky).2.1.getD i 0 = st.2.1.getD i 0 + fDb sp bx i ky := by
  obtain ⟨key, y⟩ := ky
  cases key with
  | base k => rw [stepXF_base]; exact dualStepX_getD sp bx (st.1, st.2.1) (.base k, y) i hi
  | sq v0 ts =>
    rw [stepXF_sq]
    simp only [fDb]
    by_cases h : (keyOKX sp (.sq v0 ts) && decide (0 < y)) = true
    · rw [ite_eq_left h, Rat.add_zero]
    · rw [ite_eq_right h, Rat.add_zero]

theorem stepXF_getD2 (sp : Spec) (bx : Box) (D : Nat) (st : Rat × Array Rat × Array Int)
    (ky : XKey × Rat) (i : Nat) (hi : i < st.2.2.size) :
    (stepXF sp bx D st ky).2.2.getD i 0 = st.2.2.getD i 0 + fDI sp D i ky := by
  obtain ⟨key, y⟩ := ky
  cases key with
  | base k => rw [stepXF_base]; simp only [fDI, Int.add_zero]
  | sq v0 ts =>
    rw [stepXF_sq]
    simp only [fDI]
    by_cases h : (keyOKX sp (.sq v0 ts) && decide (0 < y)) = true
    · rw [ite_eq_left h, ite_eq_left h]; dsimp only; rw [sqScatterI_eq, getD_scatterI _ _ _ _ hi]
    · rw [ite_eq_right h, ite_eq_right h, Int.add_zero]

/-! ### The fast fold -/

def sumDb (sp : Spec) (bx : Box) (i : Nat) : List (XKey × Rat) → Rat
  | [] => 0
  | ky :: l => fDb sp bx i ky + sumDb sp bx i l

def sumDI (sp : Spec) (D : Nat) (i : Nat) : List (XKey × Rat) → Int
  | [] => 0
  | ky :: l => fDI sp D i ky + sumDI sp D i l

theorem foldF_fst (sp : Spec) (hwf : sp.wf = true) (bx : Box) (D : Nat) (l : List (XKey × Rat))
    (st : Rat × Array Rat × Array Int) :
    (l.foldl (stepXF sp bx D) st).1 = st.1 + sumS sp bx l := by
  induction l generalizing st with
  | nil => simp [sumS, Rat.add_zero]
  | cons x l ih => simp only [List.foldl_cons, sumS, ih, stepXF_fst sp hwf, Rat.add_assoc]

theorem foldF_size1 (sp : Spec) (bx : Box) (D : Nat) (l : List (XKey × Rat))
    (st : Rat × Array Rat × Array Int) :
    (l.foldl (stepXF sp bx D) st).2.1.size = st.2.1.size := by
  induction l generalizing st with
  | nil => rfl
  | cons x l ih => simp only [List.foldl_cons, ih, stepXF_size1]

theorem foldF_size2 (sp : Spec) (bx : Box) (D : Nat) (l : List (XKey × Rat))
    (st : Rat × Array Rat × Array Int) :
    (l.foldl (stepXF sp bx D) st).2.2.size = st.2.2.size := by
  induction l generalizing st with
  | nil => rfl
  | cons x l ih => simp only [List.foldl_cons, ih, stepXF_size2]

theorem foldF_getD1 (sp : Spec) (bx : Box) (D : Nat) (l : List (XKey × Rat))
    (st : Rat × Array Rat × Array Int) (i : Nat) (hi : i < st.2.1.size) :
    (l.foldl (stepXF sp bx D) st).2.1.getD i 0 = st.2.1.getD i 0 + sumDb sp bx i l := by
  induction l generalizing st with
  | nil => simp only [List.foldl_nil, sumDb, Rat.add_zero]
  | cons x l ih =>
    simp only [List.foldl_cons, sumDb]
    rw [ih _ (by rw [stepXF_size1]; exact hi), stepXF_getD1 _ _ _ _ _ _ hi, Rat.add_assoc]

theorem foldF_getD2 (sp : Spec) (bx : Box) (D : Nat) (l : List (XKey × Rat))
    (st : Rat × Array Rat × Array Int) (i : Nat) (hi : i < st.2.2.size) :
    (l.foldl (stepXF sp bx D) st).2.2.getD i 0 = st.2.2.getD i 0 + sumDI sp D i l := by
  induction l generalizing st with
  | nil => simp only [List.foldl_nil, sumDI, Int.add_zero]
  | cons x l ih =>
    simp only [List.foldl_cons, sumDI]
    rw [ih _ (by rw [stepXF_size2]; exact hi), stepXF_getD2 _ _ _ _ _ _ hi, Int.add_assoc]

/-! ### Splitting the shipped increments -/

def denOK (D : Nat) (ky : XKey × Rat) : Prop :=
  match ky.1 with
  | .sq _ _ => ky.2.den ∣ D
  | .base _ => True

theorem stD_split (sp : Spec) (hwf : sp.wf = true) (bx : Box) (D : Nat) (hD : D ≠ 0) (i : Nat)
    (ky : XKey × Rat) (hky : denOK D ky) :
    stD sp bx i ky = fDb sp bx i ky + mkRat (fDI sp D i ky) D := by
  obtain ⟨key, y⟩ := ky
  cases key with
  | base k => simp only [fDb, fDI, Rat.zero_mkRat, Rat.add_zero]
  | sq v0 ts =>
    simp only [fDb, fDI, Rat.zero_add]
    rw [stD_sq sp hwf]
    by_cases h : (keyOKX sp (.sq v0 ts) && decide (0 < y)) = true
    · rw [ite_eq_left h, ite_eq_left h, sqEnt_eq]
      exact scD_cast i y _ D (fun a => neg_mul_intCast y D hD hky a) hD _
    · rw [ite_eq_right h, ite_eq_right h, Rat.zero_mkRat]

theorem sumD_split (sp : Spec) (hwf : sp.wf = true) (bx : Box) (D : Nat) (hD : D ≠ 0) (i : Nat)
    (l : List (XKey × Rat)) (hl : ∀ ky ∈ l, denOK D ky) :
    sumD sp bx i l = sumDb sp bx i l + mkRat (sumDI sp D i l) D := by
  induction l with
  | nil => simp only [sumD, sumDb, sumDI, Rat.zero_mkRat, Rat.add_zero]
  | cons ky l ih =>
    simp only [sumD, sumDb, sumDI]
    rw [stD_split sp hwf bx D hD i ky (hl ky (List.mem_cons_self ..)),
      ih (fun k hk => hl k (List.mem_cons_of_mem _ hk)), mkRat_add_same _ _ _ hD]
    grind

/-! ### The common denominator -/

theorem denOK_dvd {a b : Nat} {ky : XKey × Rat} (h : denOK a ky) (hab : a ∣ b) : denOK b ky := by
  obtain ⟨key, y⟩ := ky
  cases key with
  | base k => trivial
  | sq v0 ts => exact Nat.dvd_trans h hab

theorem fold_lcm_props (f : Nat → XKey × Rat → Nat)
    (hf1 : ∀ d ky, d ∣ f d ky) (hf2 : ∀ d ky, denOK (f d ky) ky) (hf3 : ∀ d ky, d ≠ 0 → f d ky ≠ 0) :
    ∀ (l : List (XKey × Rat)) (d : Nat), d ≠ 0 →
      l.foldl f d ≠ 0 ∧ d ∣ l.foldl f d ∧ ∀ ky ∈ l, denOK (l.foldl f d) ky
  | [], d, hd => ⟨hd, Nat.dvd_refl d, fun _ h => absurd h List.not_mem_nil⟩
  | x :: l, d, hd => by
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := fold_lcm_props f hf1 hf2 hf3 l (f d x) (hf3 d x hd)
    refine ⟨h1, Nat.dvd_trans (hf1 d x) h2, ?_⟩
    intro ky hky
    rcases List.mem_cons.mp hky with rfl | hky'
    · exact denOK_dvd (hf2 d ky) h2
    · exact h3 ky hky'

theorem sqDen_props (ys : List (XKey × Rat)) : sqDen ys ≠ 0 ∧ ∀ ky ∈ ys, denOK (sqDen ys) ky := by
  have h := fold_lcm_props
    (fun d ky => match ky.1 with | .sq _ _ => Nat.lcm d ky.2.den | .base _ => d) ?_ ?_ ?_ ys 1 (by decide)
  · exact ⟨h.1, h.2.2⟩
  · intro d ky; obtain ⟨key, y⟩ := ky
    cases key with
    | base k => exact Nat.dvd_refl d
    | sq v0 ts => exact Nat.dvd_lcm_left d y.den
  · intro d ky; obtain ⟨key, y⟩ := ky
    cases key with
    | base k => trivial
    | sq v0 ts => exact Nat.dvd_lcm_right d y.den
  · intro d ky hd; obtain ⟨key, y⟩ := ky
    cases key with
    | base k => exact hd
    | sq v0 ts => exact Nat.lcm_ne_zero hd y.den_nz

/-! ### Conversion of the fast state to a rational vector -/

/-- The conversion step of `leafcBoundXF` (`r_c := rB_c + acc_c / D`), as a named function. -/
def convF (acc : Array Int) (D : Nat) (a : Array Rat) (c : Nat) : Array Rat :=
  if acc.getD c 0 == 0 then a else a.modify c (· + mkRat (acc.getD c 0) D)

theorem convF_size (acc : Array Int) (D : Nat) (a : Array Rat) (c : Nat) : (convF acc D a c).size = a.size := by
  unfold convF
  by_cases hv : (acc.getD c 0 == 0) = true
  · rw [ite_eq_left hv]
  · rw [ite_eq_right hv, Array.size_modify]

theorem convF_getD (acc : Array Int) (D : Nat) (a : Array Rat) (c i : Nat) (hi : i < a.size) :
    (convF acc D a c).getD i 0 = if c = i then a.getD i 0 + mkRat (acc.getD i 0) D else a.getD i 0 := by
  unfold convF
  by_cases hv : (acc.getD c 0 == 0) = true
  · rw [ite_eq_left hv]
    have hv' : acc.getD c 0 = 0 := by simpa using hv
    by_cases hc : c = i
    · subst hc; rw [ite_eq_left rfl, hv', Rat.zero_mkRat, Rat.add_zero]
    · rw [ite_eq_right hc]
  · rw [ite_eq_right hv, getD_modify _ _ _ _ _ hi]
    by_cases hc : c = i
    · subst hc; rw [ite_eq_left rfl]
    · rw [ite_eq_right hc, ite_eq_right hc]

theorem foldl_size_of {β : Type} (F : Array Rat → β → Array Rat) (hF : ∀ a c, (F a c).size = a.size) :
    ∀ (l : List β) (a : Array Rat), (l.foldl F a).size = a.size
  | [], _ => rfl
  | c :: l, a => by rw [List.foldl_cons, foldl_size_of F hF l, hF]

theorem fold_range_getD (F : Array Rat → Nat → Array Rat) (g : Nat → Rat)
    (hsize : ∀ a c, (F a c).size = a.size)
    (hF : ∀ a c i, i < a.size → (F a c).getD i 0 = if c = i then a.getD i 0 + g i else a.getD i 0) :
    ∀ (n : Nat) (rB : Array Rat) (i : Nat), i < rB.size →
      ((List.range n).foldl F rB).getD i 0 = rB.getD i 0 + (if i < n then g i else 0)
  | 0, rB, i, hi => by simp only [List.range_zero, List.foldl_nil, Nat.not_lt_zero, ite_false, Rat.add_zero]
  | n + 1, rB, i, hi => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hs : i < ((List.range n).foldl F rB).size := by rw [foldl_size_of F hsize]; exact hi
    rw [hF _ _ _ hs, fold_range_getD F g hsize hF n rB i hi]
    by_cases h1 : n = i
    · subst h1
      rw [ite_eq_left rfl, ite_eq_right (Nat.lt_irrefl n), ite_eq_left (Nat.lt_succ_self n), Rat.add_zero]
    · rw [ite_eq_right h1]
      by_cases h2 : i < n
      · rw [ite_eq_left h2, ite_eq_left (Nat.lt_succ_of_lt h2)]
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

/-! ### Reduced-cost part -/

theorem foldl_congr_mem {α β : Type} (f g : β → α → β) :
    ∀ (l : List α) (init : β), (∀ x ∈ l, ∀ acc, f acc x = g acc x) → l.foldl f init = l.foldl g init
  | [], _, _ => rfl
  | x :: l, init, h => by
    simp only [List.foldl_cons]
    rw [h x (List.mem_cons_self ..) init]
    exact foldl_congr_mem f g l _ (fun y hy acc => h y (List.mem_cons_of_mem _ hy) acc)

theorem colPart_congr (sp : Spec) (bx : Box) (a b : Array Rat) (h : ∀ k < sp.NC, a.getD k 0 = b.getD k 0) :
    colPart sp bx a = colPart sp bx b := by
  unfold colPart
  apply foldl_congr_mem
  intro k hk acc
  rw [h k (List.mem_range.mp hk)]

theorem colPartZ_eq (sp : Spec) (bx : Box) (a : Array Rat) : colPartZ sp bx a = colPart sp bx a := by
  unfold colPartZ colPart
  apply foldl_congr_mem
  intro k _ acc
  show (if a.getD k 0 == 0 then acc else acc + min (a.getD k 0 * lbOf sp bx k) (a.getD k 0 * ubOf sp bx k)) =
    acc + min (a.getD k 0 * lbOf sp bx k) (a.getD k 0 * ubOf sp bx k)
  by_cases hv : (a.getD k 0 == 0) = true
  · rw [ite_eq_left hv]
    have hv' : a.getD k 0 = 0 := by simpa using hv
    rw [hv', Rat.zero_mul, Rat.zero_mul, Rat.min_def, ite_self, Rat.add_zero]
  · rw [ite_eq_right hv]

/-! ### Completion pieces (named copies of the inline code) -/

def gpXF (sp : Spec) (r : Array Rat) : List (XKey × Rat) :=
  let m := 2 * sp.n - 1
  let gs : List (Nat × Rat) := (List.range m).foldl (fun acc i =>
      let c := m - 1 - i
      let prev := match acc with | [] => 0 | (_, y) :: _ => y
      (c, prev + r.getD (sp.oG + c) 0) :: acc) []
  gs.foldr (fun cy acc =>
      (.base (.G cy.1), cy.2) :: (.base (.P cy.1), cy.2 + r.getD (sp.oP + cy.1) 0) :: acc) []

def zaStep (sp : Spec) (bx : Box) (st : Array Rat × List (XKey × Rat)) (k : RowKey) :
    Array Rat × List (XKey × Rat) :=
  match k with
  | .ZA d e _ =>
    let y := st.1.getD (sp.canon d e) 0
    (scatter st.1 (-y) (rowOf sp bx k).ent, (.base k, y) :: st.2)
  | _ => st

def zaFStep (sp : Spec) (bx : Box) (a : Array Rat) (k : RowKey) : Array Rat :=
  match k with
  | .ZA d e _ => scatter a (-(a.getD (sp.canon d e) 0)) (rowOf sp bx k).ent
  | _ => a

def pS (sp : Spec) (bx : Box) (ys : List (XKey × Rat)) : Rat × Array Rat :=
  ys.foldl (dualStepX sp bx) (0, Array.replicate sp.NC (0 : Rat))

def stF (sp : Spec) (bx : Box) (ys : List (XKey × Rat)) : Rat × Array Rat × Array Int :=
  ys.foldl (stepXF sp bx (sqDen ys)) (0, Array.replicate sp.NC (0 : Rat), Array.replicate sp.NC (0 : Int))

def rF (sp : Spec) (bx : Box) (ys : List (XKey × Rat)) : Array Rat :=
  (List.range sp.NC).foldl (convF (stF sp bx ys).2.2 (sqDen ys)) (stF sp bx ys).2.1

def finXF (sp : Spec) (bx : Box) (zo : List RowKey) (s : Rat) (r : Array Rat) : Rat × Array Rat :=
  (gpXF sp r).foldl (dualStepX sp bx)
    (s, (zo.foldl (zaFStep sp bx) r).setIfInBounds sp.oT ((zo.foldl (zaFStep sp bx) r).getD sp.oT 0 + 1))

theorem leafcBoundXF_unfold (sp : Spec) (bx : Box) (zo : List RowKey) (ys : List (XKey × Rat))
    (hzo : zoOK sp zo = true) :
    leafcBoundXF sp bx zo ys =
      (finXF sp bx zo (stF sp bx ys).1 (rF sp bx ys)).1 +
        colPartZ sp bx (finXF sp bx zo (stF sp bx ys).1 (rF sp bx ys)).2 := by
  unfold leafcBoundXF
  rw [ite_eq_left hzo]
  rfl

theorem completeX_unfold (sp : Spec) (bx : Box) (zo : List RowKey) (ys : List (XKey × Rat)) :
    completeX sp bx zo ys = gpXF sp (pS sp bx ys).2 ++ (zo.foldl (zaStep sp bx) ((pS sp bx ys).2, [])).2 :=
  rfl

/-! ### The fast state equals the shipped one -/

theorem rF_eq (sp : Spec) (hwf : sp.wf = true) (bx : Box) (ys : List (XKey × Rat)) :
    rF sp bx ys = (pS sp bx ys).2 := by
  obtain ⟨hD, hden⟩ := sqDen_props ys
  have hsz1 : (stF sp bx ys).2.1.size = sp.NC := by unfold stF; rw [foldF_size1]; simp
  have hsz2 : (stF sp bx ys).2.2.size = sp.NC := by unfold stF; rw [foldF_size2]; simp
  have hszR : (rF sp bx ys).size = sp.NC := by unfold rF; rw [foldl_size_of _ (convF_size _ _)]; exact hsz1
  have hszP : (pS sp bx ys).2.size = sp.NC := by unfold pS; rw [foldX_size]; simp
  apply Array.ext
  · rw [hszR, hszP]
  · intro i h1 h2
    have hi : i < sp.NC := hszR ▸ h1
    rw [Array.getElem_eq_getD 0, Array.getElem_eq_getD 0]
    unfold rF
    rw [fold_range_getD (convF (stF sp bx ys).2.2 (sqDen ys))
      (fun i => mkRat ((stF sp bx ys).2.2.getD i 0) (sqDen ys)) (convF_size _ _) (convF_getD _ _) sp.NC _ i
      (by rw [hsz1]; exact hi)]
    rw [ite_eq_left hi]
    unfold stF pS
    rw [foldF_getD1 _ _ _ _ _ _ (by simpa using hi), foldF_getD2 _ _ _ _ _ _ (by simpa using hi),
      foldX_getD _ _ _ _ _ (by simpa using hi)]
    rw [sumD_split sp hwf bx (sqDen ys) hD i ys hden]
    simp [getD_replicate _ _ _ _ hi, Rat.zero_add, Int.zero_add]

theorem stF_fst (sp : Spec) (hwf : sp.wf = true) (bx : Box) (ys : List (XKey × Rat)) :
    (stF sp bx ys).1 = (pS sp bx ys).1 := by
  unfold stF pS
  rw [foldF_fst sp hwf, foldX_fst]

/-! ### ZA duals of the completion -/

def zoKeyOK (sp : Spec) (k : RowKey) : Bool :=
  match k with
  | .ZA _ _ _ => keyOK sp k && entOK sp (rowOf sp ⟨#[], #[]⟩ k).ent
  | _ => false

theorem zoOK_mem (sp : Spec) (zo : List RowKey) (h : zoOK sp zo = true) : ∀ k ∈ zo, zoKeyOK sp k = true := by
  unfold zoOK at h
  rw [List.all_eq_true] at h
  intro k hk
  have := h k hk
  cases k <;> exact this

theorem stD_ZA (sp : Spec) (bx : Box) (d e s : Nat) (h : zoKeyOK sp (.ZA d e s) = true) (i : Nat) (y : Rat) :
    stD sp bx i (.base (.ZA d e s), y) = scD i (-y) (rowOf sp bx (.ZA d e s)).ent := by
  unfold stD
  have h' : (keyOKX sp (XKey.base (RowKey.ZA d e s), y).1 &&
      entOK sp (rowOfX sp bx (XKey.base (RowKey.ZA d e s), y).1).ent) = true := h
  rw [ite_eq_left h']
  by_cases h2 : 0 < y
  · rw [ite_eq_left h2]; rfl
  · rw [ite_eq_right h2]
    by_cases h3 : y < 0
    · rw [ite_eq_left h3]; rfl
    · rw [ite_eq_right h3]
      have hy : y = 0 := Rat.le_antisymm (Rat.not_lt.mp h2) (Rat.not_lt.mp h3)
      rw [hy, Rat.neg_zero, scD_zero]

theorem stS_ZA (sp : Spec) (bx : Box) (d e s : Nat) (h : zoKeyOK sp (.ZA d e s) = true) (y : Rat) :
    stS sp bx (.base (.ZA d e s), y) = 0 := by
  unfold stS
  have h' : (keyOKX sp (XKey.base (RowKey.ZA d e s), y).1 &&
      entOK sp (rowOfX sp bx (XKey.base (RowKey.ZA d e s), y).1).ent) = true := h
  rw [ite_eq_left h']
  by_cases h2 : 0 < y
  · rw [ite_eq_left h2]; show y * 0 = 0; exact Rat.mul_zero y
  · rw [ite_eq_right h2]
    by_cases h3 : y < 0
    · rw [ite_eq_left h3]; show y * 0 = 0; exact Rat.mul_zero y
    · rw [ite_eq_right h3]

theorem zaStep_size (sp : Spec) (bx : Box) (st : Array Rat × List (XKey × Rat)) (k : RowKey) :
    (zaStep sp bx st k).1.size = st.1.size := by
  cases k with
  | ZA d e s => exact size_scatter _ _ _
  | _ => rfl

theorem zaStep_getD (sp : Spec) (bx : Box) (st : Array Rat × List (XKey × Rat)) (k : RowKey)
    (hk : zoKeyOK sp k = true) (i : Nat) (hi : i < st.1.size) :
    (zaStep sp bx st k).1.getD i 0 + sumD sp bx i st.2 =
      st.1.getD i 0 + sumD sp bx i (zaStep sp bx st k).2 := by
  cases k with
  | ZA d e s =>
    show (scatter st.1 (-(st.1.getD (sp.canon d e) 0)) (rowOf sp bx (.ZA d e s)).ent).getD i 0 +
        sumD sp bx i st.2 =
      st.1.getD i 0 + sumD sp bx i ((XKey.base (RowKey.ZA d e s), st.1.getD (sp.canon d e) 0) :: st.2)
    rw [getD_scatter _ _ _ _ hi]
    simp only [sumD]
    rw [stD_ZA sp bx d e s hk]
    grind
  | _ => rfl

theorem zaStep_sumS (sp : Spec) (bx : Box) (st : Array Rat × List (XKey × Rat)) (k : RowKey)
    (hk : zoKeyOK sp k = true) : sumS sp bx (zaStep sp bx st k).2 = sumS sp bx st.2 := by
  cases k with
  | ZA d e s =>
    show sumS sp bx ((XKey.base (RowKey.ZA d e s), st.1.getD (sp.canon d e) 0) :: st.2) = sumS sp bx st.2
    simp only [sumS]
    rw [stS_ZA sp bx d e s hk, Rat.zero_add]
  | _ => rfl

theorem zaStep_fst (sp : Spec) (bx : Box) (st : Array Rat × List (XKey × Rat)) (k : RowKey) :
    (zaStep sp bx st k).1 = zaFStep sp bx st.1 k := by
  cases k <;> rfl

theorem zaFold_size (sp : Spec) (bx : Box) :
    ∀ (zo : List RowKey) (st : Array Rat × List (XKey × Rat)), (zo.foldl (zaStep sp bx) st).1.size = st.1.size
  | [], _ => rfl
  | k :: zo, st => by rw [List.foldl_cons, zaFold_size sp bx zo, zaStep_size]

theorem zaFold_fst (sp : Spec) (bx : Box) :
    ∀ (zo : List RowKey) (st : Array Rat × List (XKey × Rat)),
      (zo.foldl (zaStep sp bx) st).1 = zo.foldl (zaFStep sp bx) st.1
  | [], _ => rfl
  | k :: zo, st => by rw [List.foldl_cons, List.foldl_cons, zaFold_fst sp bx zo, zaStep_fst]

theorem zaFold_getD (sp : Spec) (bx : Box) :
    ∀ (zo : List RowKey) (st : Array Rat × List (XKey × Rat)), (∀ k ∈ zo, zoKeyOK sp k = true) →
      ∀ i, i < st.1.size →
        (zo.foldl (zaStep sp bx) st).1.getD i 0 + sumD sp bx i st.2 =
          st.1.getD i 0 + sumD sp bx i (zo.foldl (zaStep sp bx) st).2
  | [], st, _, i, _ => rfl
  | k :: zo, st, h, i, hi => by
    rw [List.foldl_cons]
    have h1 := zaFold_getD sp bx zo (zaStep sp bx st k) (fun k' hk' => h k' (List.mem_cons_of_mem _ hk')) i
      (by rw [zaStep_size]; exact hi)
    have h2 := zaStep_getD sp bx st k (h k (List.mem_cons_self ..)) i hi
    grind

theorem zaFold_sumS (sp : Spec) (bx : Box) :
    ∀ (zo : List RowKey) (st : Array Rat × List (XKey × Rat)), (∀ k ∈ zo, zoKeyOK sp k = true) →
      sumS sp bx (zo.foldl (zaStep sp bx) st).2 = sumS sp bx st.2
  | [], _, _ => rfl
  | k :: zo, st, h => by
    rw [List.foldl_cons, zaFold_sumS sp bx zo _ (fun k' hk' => h k' (List.mem_cons_of_mem _ hk')),
      zaStep_sumS sp bx st k (h k (List.mem_cons_self ..))]

theorem final_eq (sp : Spec) (bx : Box) (zo : List RowKey) (ys : List (XKey × Rat))
    (hzo : zoOK sp zo = true) :
    (finXF sp bx zo (pS sp bx ys).1 (pS sp bx ys).2).1 +
        colPartZ sp bx (finXF sp bx zo (pS sp bx ys).1 (pS sp bx ys).2).2 =
      dualBoundX sp bx true (ys ++ (gpXF sp (pS sp bx ys).2 ++ (zo.foldl (zaStep sp bx) ((pS sp bx ys).2, [])).2)) := by
  have hNC : sp.oT < sp.NC := by unfold Spec.NC; omega
  have hzk := zoOK_mem sp zo hzo
  have hp1 : (pS sp bx ys).1 = 0 + sumS sp bx ys := by unfold pS; rw [foldX_fst]
  have hpsz : (pS sp bx ys).2.size = sp.NC := by unfold pS; rw [foldX_size]; simp
  have hp2 : ∀ i < sp.NC, (pS sp bx ys).2.getD i 0 = 0 + sumD sp bx i ys := by
    intro i hi
    unfold pS
    rw [foldX_getD _ _ _ _ _ (by simpa using hi)]
    simp [getD_replicate _ _ _ _ hi]
  generalize (pS sp bx ys).2 = r at hpsz hp2 ⊢
  generalize (pS sp bx ys).1 = s at hp1 ⊢
  have hza1 := zaFold_fst sp bx zo (r, [])
  have hzasz : (zo.foldl (zaFStep sp bx) r).size = sp.NC := by
    have := zaFold_size sp bx zo (r, [])
    rw [hza1] at this
    rw [this]; exact hpsz
  have hzag : ∀ i < sp.NC, (zo.foldl (zaFStep sp bx) r).getD i 0 =
      r.getD i 0 + sumD sp bx i (zo.foldl (zaStep sp bx) (r, [])).2 := by
    intro i hi
    have := zaFold_getD sp bx zo (r, []) hzk i (by simpa [hpsz] using hi)
    rw [hza1] at this
    simpa [sumD, Rat.add_zero] using this
  have hzaS : sumS sp bx (zo.foldl (zaStep sp bx) (r, [])).2 = 0 := zaFold_sumS sp bx zo (r, []) hzk
  generalize (zo.foldl (zaStep sp bx) (r, [])).2 = Z at hzag hzaS ⊢
  unfold finXF
  generalize zo.foldl (zaFStep sp bx) r = rza at hzasz hzag ⊢
  generalize gpXF sp r = G
  simp only [dualBoundX, ↓reduceIte]
  rw [foldX_fst, foldX_fst, sumS_append, sumS_append, hzaS, colPartZ_eq]
  congr 1
  · simp only []
    rw [hp1]
    grind
  · apply colPart_congr
    intro k hk
    rw [foldX_getD _ _ _ _ _ (by simpa [hzasz] using hk), foldX_getD _ _ _ _ _ (by simpa using hk)]
    rw [sumD_append, sumD_append]
    simp only []
    rw [getD_setIfInBounds _ _ _ _ _ (by rw [hzasz]; exact hk),
      getD_setIfInBounds _ _ _ _ _ (by simpa using hk), getD_replicate _ _ _ _ hk]
    by_cases hk' : sp.oT = k
    · subst hk'
      rw [ite_eq_left rfl, ite_eq_left rfl, hzag _ hk, hp2 _ hk]
      grind
    · rw [ite_eq_right hk', ite_eq_right hk', hzag _ hk, hp2 _ hk]
      grind

end XFP

/-! ## The statements to be proved (standard axioms only) -/

/-- The core fact: the fast leaf bound is the shipped one (the `zoOK` branch; the other branch is the shipped code). -/
theorem leafcBoundXF_eq (sp : Spec) (hwf : sp.wf = true) (bx : Box) (zo : List RowKey) (ys : List (XKey × Rat)) :
    leafcBoundXF sp bx zo ys = dualBoundX sp bx true (ys ++ completeX sp bx zo ys) := by
  by_cases hzo : zoOK sp zo = true
  · rw [XFP.leafcBoundXF_unfold sp bx zo ys hzo, XFP.completeX_unfold, XFP.rF_eq sp hwf bx ys,
      XFP.stF_fst sp hwf bx ys]
    exact XFP.final_eq sp bx zo ys hzo
  · unfold leafcBoundXF
    rw [ite_eq_right hzo]

/-- The stack machines agree once `sp.wf` holds. -/
theorem XFP.runXF_eq (sp : Spec) (hwf : sp.wf = true) (lam : Rat) (zo : List RowKey) :
    ∀ (recs : List RecX) (stk : List Box), runXF sp lam zo recs stk = runX sp lam zo recs stk
  | [], stk => by simp only [runXF, runX]
  | _ :: _, [] => by simp only [runXF, runX]
  | .split b s :: rs, bx :: stk => by simp only [runXF, runX, XFP.runXF_eq sp hwf lam zo rs]
  | .leaf ys :: rs, bx :: stk => by simp only [runXF, runX, XFP.runXF_eq sp hwf lam zo rs]
  | .farkas ys :: rs, bx :: stk => by simp only [runXF, runX, XFP.runXF_eq sp hwf lam zo rs]
  | .deleg :: rs, bx :: stk => by simp only [runXF, runX, XFP.runXF_eq sp hwf lam zo rs]
  | .leafc ys :: rs, bx :: stk => by
    simp only [runXF, runX, XFP.runXF_eq sp hwf lam zo rs, leafcBoundXF_eq sp hwf]

theorem checkJobXF_eq (sp : Spec) (lam : Rat) (zo : List RowKey) (root : Path) (children : List Path)
    (recs : List RecX) : checkJobXF sp lam zo root children recs = checkJobX sp lam zo root children recs := by
  unfold checkJobXF checkJobX
  cases hwf : sp.wf with
  | false => rfl
  | true =>
    simp only [XFP.runXF_eq sp hwf lam zo]
    rfl

theorem checkJobStrXF_eq (n : Nat) (lam : Rat) (zo root : String) (children : List String) (recs : String) :
    checkJobStrXF n lam zo root children recs = checkJobStrX n lam zo root children recs :=
  checkJobXF_eq _ _ _ _ _ _

theorem checkGroupStrXF_eq (n : Nat) (lam : Rat) (zo : String) (ext : List String) :
    ∀ (seen : List String) (jobs : List JobStrX),
      checkGroupStrXF n lam zo ext seen jobs = checkGroupStrX n lam zo ext seen jobs
  | _, [] => rfl
  | seen, (root, children, recs) :: rest => by
    simp only [checkGroupStrXF, checkGroupStrX, checkJobStrXF_eq, checkGroupStrXF_eq n lam zo ext (root :: seen) rest]

end Autocorr.Cert

/-
Generated modules (only the `chk` proofs change):
  per job:  theorem chk : Autocorr.Cert.checkJobStrX n lam PKG.zo "<root>" [<children>] recs = true := by
              rw [← Autocorr.Cert.checkJobStrXF_eq]; native_decide
  group:    theorem chk : Autocorr.Cert.checkGroupStrX n lam PKG.zo ext [] (jobs ++ [rootJob]) = true := by
              rw [← Autocorr.Cert.checkGroupStrXF_eq]; native_decide
The native_decide auxiliary axiom then decides `checkJobStrXF ... = true` (resp. `checkGroupStrXF`); the axiom scan
checks that every native axiom's proposition has one of these two heads.
Files: AutocorrCert/CheckerXF.lean (definitions above, precompiled like CheckerX) and the proofs in core Lean (no
Mathlib), so that shard modules keep importing core only.
-/
