/-!
# Kernel checker (milestone M4): computation (core Lean, evaluated by the kernel)

Everything is `Nat`-only and written with raw `Nat.*` functions, explicit `Nat.rec` loops in
continuation-passing style, and the conditional `sel` (`Bool.rec`), so that the kernel evaluates it
without instance unfolding.  The semantics is that of `tools/kc_ref.py`; the soundness proof is in
`Autocorr/KSound`.

Scales: duals `y = ±m / 2^64`; box bounds `L_b = l_b / 2^30` (32-bit slots); reduced costs of the columns
`c < NC1` (all columns but `t`) in packed 136-bit digits at scale `2^94`, split into a positive part
`rp` and a negative part `rn`; `2n·2^64·r_t = tp - tn`; `2^124·rowpart = ap - an`.

Row descriptors (80-bit entries of `KP.T`, indexed by row number):
`kind (3) | f1 (13) | f2 (13) | f3 (13) | f4 (13) | flag (1) | k1 (7) | k2 (7) | k3 (7)` (77 bits used),
see `descOK` in `AutocorrK/Table.lean` for the meaning of the fields of each kind.

Square cuts (format 2): a leaf may also list cut records `(v0, d, v1, e, v2, M)` for the row
`v1² [m_d m_d] + 2 v1 v2 [m_d m_e] + v2² [m_e m_e] + 2 v0 v1 m_d + 2 v0 v2 m_e ≥ -v0²` with the dual `M / 2^94 ≥ 0`
(`cutStep`); the product columns come from the table `KP.canonTab` (`canonT`, checked by `canonOK`).

K39 version (n = 39 and the `k`-block square cuts of the C1 >= 1337/1000 certificate), changes from the KC36 checker:
dual records are 88-bit chunks with a 15-bit row field (`NR < 32766`; the KC36 checker had 87-bit chunks and 14-bit
rows), the two-block cut is escape `32767` (its fields one bit higher), and escape `32766` is a square cut with up to
126 blocks (`denseStep`): `(v0 + Σ_i v_i m_{b_i})² ≥ 0` expanded on the product columns.
-/

namespace AutocorrK

universe u

noncomputable section

/-- Kernel-cheap conditional. -/
def sel {α : Sort u} (c : Bool) (t e : α) : α := Bool.rec (motive := fun _ => α) e t c

/-- Constants for one `n`. Checked once against `Autocorr.Cert.mkSpec n` (`kpOK`). -/
structure KP where
  n : Nat
  nB : Nat
  oZ : Nat
  oP : Nat
  oG : Nat
  NC1 : Nat
  NR : Nat
  T : Nat
  symP : Nat
  symN : Nat
  intTab : Nat
  nInt : Nat
  canonTab : Nat

/-- `v · 2^(136 c)` -/
def atc (v c : Nat) : Nat := Nat.shiftLeft v (Nat.mul 136 c)

/-- Field `k` (13 bits) of a descriptor. -/
def f13 (x k : Nat) : Nat := Nat.mod (Nat.shiftRight x (Nat.add 3 (Nat.mul 13 k))) 8192

/-- The flag bit of a descriptor. -/
def dflag (x : Nat) : Bool := Nat.beq (Nat.mod (Nat.shiftRight x 55) 2) 1

/-- 32-bit slot `i`. -/
def get32 (x i : Nat) : Nat := Nat.mod (Nat.shiftRight x (Nat.mul 32 i)) 4294967296

/-- 16-bit slot `i`. -/
def get16 (x i : Nat) : Nat := Nat.mod (Nat.shiftRight x (Nat.mul 16 i)) 65536

/-- Product column `[m_d m_e]` of the blocks `d, e < 128` (slot `128 d + e` of `canonTab`). -/
def canonT (P : KP) (d e : Nat) : Nat := get16 P.canonTab (Nat.add (Nat.mul 128 d) e)

/-- Descriptor of row `r` (a mask, not `Nat.mod`: the kernel's `Nat.mod` by `2^80` is a long division of the
shifted table). -/
def desc (P : KP) (r : Nat) : Nat :=
  Nat.land (Nat.shiftRight P.T (Nat.mul 80 r)) 1208925819614629174706175   -- 2^80 - 1

def zIdxK (oZ n i j : Nat) : Nat :=
  sel (Nat.ble i j) (Nat.add oZ (Nat.add (Nat.mul i n) j)) (Nat.add oZ (Nat.add (Nat.mul j n) i))

/-- Pattern of row `P(c)` on the `Z` columns: one unit digit per ordered entry `(i, c-i)`. -/
def patP (oZ n c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => sel (Nat.ble i c) (sel (Nat.ble (Nat.add (Nat.sub c i) 1) n)
      (Nat.add acc (atc 1 (zIdxK oZ n i (Nat.sub c i)))) acc) acc) n

/-- Pattern of row `rlt(i)`: one unit digit per cell `zIdx(i, j)`, `j < n`. -/
def patR (oZ n i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun j acc => Nat.add acc (atc 1 (zIdxK oZ n i j))) n

/-- The continuation type: `data rp rn tp tn ap an ↦ result`. -/
abbrev K := Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool

/-- Equality row: `tgt` = digits of the +1 part, `trm` = digits of the −1 part (both times `m·2^30`).
`r += -y·a`: for `y > 0` the +1 part is negative. -/
def eqRow (yn : Bool) (tgt trm : Nat) (k : K) (data rp rn tp tn ap an : Nat) : Bool :=
  sel yn (k data (Nat.add rp tgt) (Nat.add rn trm) tp tn ap an)
    (k data (Nat.add rp trm) (Nat.add rn tgt) tp tn ap an)

/-- McCormick row (only for `y < 0`, so `-y·a = m·a`). -/
def mcRow (lp up d m : Nat) (k : K) (data rp rn tp tn ap an : Nat) : Bool :=
  let mz := atc (Nat.shiftLeft m 30) (f13 d 0)
  let dd := f13 d 1
  let ee := f13 d 2
  let q := f13 d 3
  let ld := get32 lp dd
  let ud := get32 up dd
  let le := get32 lp ee
  let ue := get32 up ee
  sel (dflag d)
    (sel (Nat.beq q 0)
      (k data (Nat.add rp (atc (Nat.mul m (Nat.mul 2 ld)) dd)) (Nat.add rn mz) tp tn ap
        (Nat.add an (Nat.mul m (Nat.mul ld ld))))
      (sel (Nat.beq q 1)
        (k data (Nat.add rp (atc (Nat.mul m (Nat.mul 2 ud)) dd)) (Nat.add rn mz) tp tn ap
          (Nat.add an (Nat.mul m (Nat.mul ud ud))))
        (k data (Nat.add rp mz) (Nat.add rn (atc (Nat.mul m (Nat.add ld ud)) dd)) tp tn
          (Nat.add ap (Nat.mul m (Nat.mul ld ud))) an)))
    (sel (Nat.beq q 0)
      (k data (Nat.add rp (Nat.add (atc (Nat.mul m le) dd) (atc (Nat.mul m ld) ee))) (Nat.add rn mz)
        tp tn ap (Nat.add an (Nat.mul m (Nat.mul ld le))))
      (sel (Nat.beq q 1)
        (k data (Nat.add rp (Nat.add (atc (Nat.mul m ue) dd) (atc (Nat.mul m ud) ee))) (Nat.add rn mz)
          tp tn ap (Nat.add an (Nat.mul m (Nat.mul ud ue))))
        (sel (Nat.beq q 2)
          (k data (Nat.add rp mz) (Nat.add rn (Nat.add (atc (Nat.mul m ue) dd) (atc (Nat.mul m ld) ee)))
            tp tn (Nat.add ap (Nat.mul m (Nat.mul ld ue))) an)
          (k data (Nat.add rp mz) (Nat.add rn (Nat.add (atc (Nat.mul m le) dd) (atc (Nat.mul m ud) ee)))
            tp tn (Nat.add ap (Nat.mul m (Nat.mul ud le))) an))))

/-- One dual: descriptor `d`, sign `yn` (`y < 0`), magnitude `m`. -/
def step (P : KP) (lp up : Nat) (d : Nat) (yn : Bool) (m : Nat)
    (k : K) (data rp rn tp tn ap an : Nat) : Bool :=
  let kind := Nat.mod d 8
  let m30 := Nat.shiftLeft m 30
  sel (Nat.beq kind 4)
    (eqRow yn (atc m30 (f13 d 0))
      (sel (dflag d)
        (Nat.add (atc m30 (f13 d 1)) (Nat.add (atc m30 (f13 d 2)) (atc (Nat.mul 2 m30) (f13 d 3))))
        (Nat.add (atc m30 (f13 d 1)) (atc m30 (f13 d 2))))
      k data rp rn tp tn ap an)
  (sel (Nat.beq kind 7)
    (sel yn (mcRow lp up d m k data rp rn tp tn ap an) (k data rp rn tp tn ap an))
  (sel (Nat.beq kind 1)
    (eqRow yn (atc m30 (f13 d 0)) (Nat.mul m30 (patP P.oZ P.n (f13 d 1))) k data rp rn tp tn ap an)
  (sel (Nat.beq kind 2)
    (eqRow yn (atc m30 (f13 d 0))
      (Nat.add (atc m30 (f13 d 1)) (sel (dflag d) (atc m30 (f13 d 2)) 0)) k data rp rn tp tn ap an)
  (sel (Nat.beq kind 3)
    (eqRow yn (atc m30 (f13 d 0)) (Nat.add (atc m30 (f13 d 1)) (atc m30 (f13 d 2))) k data rp rn tp tn ap an)
  (sel (Nat.beq kind 5)
    (eqRow yn (Nat.mul m30 (patR P.oZ P.n (f13 d 0))) (atc m30 (f13 d 1)) k data rp rn tp tn ap an)
  (sel (Nat.beq kind 0)
    (sel yn
      (k data (Nat.add rp (atc m30 (f13 d 0))) (Nat.add rn (sel (dflag d) (atc m30 (f13 d 1)) 0))
        tp (Nat.add tn (Nat.mul m (f13 d 2))) ap an)
      (k data rp rn tp tn ap an))
    (sel yn (k data (Nat.add rp (Nat.mul m P.symP)) (Nat.add rn (Nat.mul m P.symN)) tp tn ap an)
      (k data rp rn tp tn ap an))))))))

/-- A square cut, read from the low 176 bits of `data` (two 88-bit chunks):
`32767 (15) | 0 (1) | d (7) | e (7) | s0 (1) | a0 (21) | s1 (1) | a1 (21) | s2 (1) | a2 (21) | M (64)`, with
`v_i = ±a_i` (sign bit `s_i`) and the dual `M / 2^94`.  The coefficients of the cut row are `a1²` on `[m_d m_d]`,
`a2²` on `[m_e m_e]`, `±2 a1 a2` on `[m_d m_e]` (`+` iff `s1 = s2`), `±2 a0 a1` on `m_d` and `±2 a0 a2` on `m_e`; the
contribution `-y·coef` of a positive coefficient goes to `rn`, of a negative one to `rp`, and `y·(-v0²)` to `an`.
Requires `d, e < nB`.  Continues with `data >>> 176`. -/
def cutStep (P : KP) (data : Nat) (k : K) (rp rn tp tn ap an : Nat) : Bool :=
  let d := Nat.mod (Nat.shiftRight data 16) 128
  let e := Nat.mod (Nat.shiftRight data 23) 128
  let s0 := Nat.mod (Nat.shiftRight data 30) 2
  let a0 := Nat.mod (Nat.shiftRight data 31) 2097152
  let s1 := Nat.mod (Nat.shiftRight data 52) 2
  let a1 := Nat.mod (Nat.shiftRight data 53) 2097152
  let s2 := Nat.mod (Nat.shiftRight data 74) 2
  let a2 := Nat.mod (Nat.shiftRight data 75) 2097152
  let M := Nat.mod (Nat.shiftRight data 96) 18446744073709551616
  let tde := Nat.mul 2 (Nat.mul M (Nat.mul a1 a2))
  let tmd := Nat.mul 2 (Nat.mul M (Nat.mul a0 a1))
  let tme := Nat.mul 2 (Nat.mul M (Nat.mul a0 a2))
  let x12 := Nat.beq s1 s2
  let x01 := Nat.beq s0 s1
  let x02 := Nat.beq s0 s2
  sel (Nat.blt d P.nB)
    (sel (Nat.blt e P.nB)
      (k (Nat.shiftRight data 176)
        (Nat.add rp (Nat.add (atc (sel x12 0 tde) (canonT P d e))
          (Nat.add (atc (sel x01 0 tmd) d) (atc (sel x02 0 tme) e))))
        (Nat.add rn (Nat.add (atc (Nat.mul M (Nat.mul a1 a1)) (canonT P d d))
          (Nat.add (atc (Nat.mul M (Nat.mul a2 a2)) (canonT P e e))
            (Nat.add (atc (sel x12 tde 0) (canonT P d e))
              (Nat.add (atc (sel x01 tmd 0) d) (atc (sel x02 tme 0) e))))))
        tp tn ap (Nat.add an (Nat.shiftLeft (Nat.mul M (Nat.mul a0 a0)) 30)))
      false)
    false

/-! ## Square cuts with up to 126 blocks (escape `32766`)

Terms are 29-bit fields `b (7) | s (1) | a (21)` (block `b`, `v = ±a`, sign bit `s`), read from the low end of `td`. -/

/-- The blocks of the next `cnt` terms of `td` are all `< nB`. -/
def dValid (P : KP) (cnt : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih td => sel (Nat.blt (Nat.mod td 128) P.nB) (ih (Nat.shiftRight td 29)) false) cnt

/-- The mixed terms of one term (block `b`, sign bit `s`, `ma = 2 M a`) with the next `cnt` terms of `td`: the
coefficient `2 v v'` on `[m_b m_b']` contributes `ma · a'` to `neg` if the signs agree (positive coefficient), else
to `pos`.  Returns the accumulators `(pos, neg)`. -/
def dMix (P : KP) (b s ma : Nat) (cnt : Nat) : Nat → Nat → Nat → Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat × Nat) (fun _ pos neg => (pos, neg))
    (fun _ ih td pos neg =>
      let v := atc (Nat.mul ma (Nat.mod (Nat.shiftRight td 8) 2097152)) (canonT P b (Nat.mod td 128))
      sel (Nat.beq s (Nat.mod (Nat.shiftRight td 7) 2))
        (ih (Nat.shiftRight td 29) pos (Nat.add neg v))
        (ih (Nat.shiftRight td 29) (Nat.add pos v) neg))
    cnt

/-- The `cnt` terms of `td` of a cut with `v0 = ±a0` (sign bit `s0`, `ma0 = 2 M a0`) and dual `M / 2^94`: per term,
`M a²` on `[m_b m_b]` (to `neg`), `ma0 · a` on `m_b` (to `neg` iff `s0 = s`) and the mixed terms with the later
terms (`dMix`; the recursor's index is the number of later terms). -/
def dOuter (P : KP) (s0 ma0 M : Nat) (cnt : Nat) : Nat → Nat → Nat → Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat × Nat) (fun _ pos neg => (pos, neg))
    (fun n ih td pos neg =>
      let b := Nat.mod td 128
      let s := Nat.mod (Nat.shiftRight td 7) 2
      let a := Nat.mod (Nat.shiftRight td 8) 2097152
      let mx := dMix P b s (Nat.mul 2 (Nat.mul M a)) n (Nat.shiftRight td 29) pos
        (Nat.add neg (atc (Nat.mul M (Nat.mul a a)) (canonT P b b)))
      sel (Nat.beq s0 s)
        (ih (Nat.shiftRight td 29) mx.1 (Nat.add mx.2 (atc (Nat.mul ma0 a) b)))
        (ih (Nat.shiftRight td 29) (Nat.add mx.1 (atc (Nat.mul ma0 a) b)) mx.2))
    cnt

/-- A square cut with `k ≤ 126` blocks, read from `data`:
`32766 (15) | 0 (1) | k (7) | s0 (1) | a0 (21) | M (64)`, then `k` terms (from bit 109), with `v0 = ±a0`, `v_i = ±a_i`
and the dual `M / 2^94 ≥ 0`, for the row
`Σ_i v_i² [m_bi m_bi] + Σ_{i<j} 2 v_i v_j [m_bi m_bj] + Σ_i 2 v0 v_i m_bi ≥ -v0²`
(at the true point the left side plus `v0²` is `(v0 + Σ_i v_i m_bi)²`).  Requires every `b_i < nB`.  The record
occupies `⌈(109 + 29k)/88⌉` chunks; continues with the data after them. -/
def denseStep (P : KP) (data : Nat) (k : K) (rp rn tp tn ap an : Nat) : Bool :=
  let kk := Nat.mod (Nat.shiftRight data 16) 128
  let s0 := Nat.mod (Nat.shiftRight data 23) 2
  let a0 := Nat.mod (Nat.shiftRight data 24) 2097152
  let M := Nat.mod (Nat.shiftRight data 45) 18446744073709551616
  let td := Nat.land (Nat.shiftRight data 109) (Nat.sub (Nat.pow 2 (Nat.mul 29 kk)) 1)
  sel (Nat.ble kk 126)
    (sel (dValid P kk td)
      (let r := dOuter P s0 (Nat.mul 2 (Nat.mul M a0)) M kk td 0 0
       k (Nat.shiftRight data (Nat.mul 88 (Nat.div (Nat.add (Nat.mul 29 kk) 196) 88)))
         (Nat.add rp r.1) (Nat.add rn r.2) tp tn ap (Nat.add an (Nat.shiftLeft (Nat.mul M (Nat.mul a0 a0)) 30)))
      false)
    false

/-- The dual loop over `cnt` chunks of 88 bits: a row record `row (15) | sign (1) | magnitude (72)`, or (row field
`32767`) a two-block square cut occupying two chunks (`cutStep`), or (row field `32766`) a square cut with up to 126
blocks occupying `⌈(109 + 29k)/88⌉` chunks (`denseStep`).  Neither escape is a row (`NR < 32766`).  A cut takes one
iteration; the exporter counts all of its chunks in `cnt`, so the loop ends with no-op chunks (zero data is row 0
with magnitude 0). -/
def loop (P : KP) (lp up : Nat) (fin : K) (cnt : Nat) : K :=
  Nat.rec (motive := fun _ => K) fin
    (fun _ ih data rp rn tp tn ap an =>
      let r := Nat.land data 309485009821345068724781055   -- 2^88 - 1
      let ri := Nat.mod r 32768
      sel (Nat.beq ri 32767)
        (cutStep P data ih rp rn tp tn ap an)
        (sel (Nat.beq ri 32766)
          (denseStep P data ih rp rn tp tn ap an)
          (sel (Nat.ble (Nat.add ri 1) P.NR)
            (step P lp up (desc P ri) (Nat.beq (Nat.mod (Nat.shiftRight r 15) 2) 1)
              (Nat.shiftRight r 16) ih (Nat.shiftRight data 88) rp rn tp tn ap an)
            false)))
    cnt

/-- `2^136 - 1` -/
def W1 : Nat := 87112285931760246646623899502532662132735

/-- SWAR: `Σ_{c<s} max(0, N_c - P_c)` for 136-bit digit vectors with digits `< 2^135`. -/
def swarNeg (s pv nv : Nat) : Nat :=
  let ones := Nat.div (Nat.sub (Nat.pow 2 (Nat.mul 136 s)) 1) W1
  let H := Nat.shiftLeft ones 135
  let X := Nat.sub (Nat.add nv H) pv
  let M := Nat.mul (Nat.shiftRight (Nat.land X H) 135) W1
  Nat.mod (Nat.sub (Nat.land X M) (Nat.land H M)) W1

/-- The m columns `c < nB`: `Σ min(R_c l_c, R_c u_c)` as a (positive, negative) pair. -/
def mcols (lp up : Nat) (cnt : Nat) : Nat → Nat → Nat → Nat → Nat → Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Nat × Nat)
    (fun _ _ _ ap an => (ap, an))
    (fun _ ih pv nv c ap an =>
      let x := Nat.mod pv 87112285931760246646623899502532662132736   -- 2^136
      let y := Nat.mod nv 87112285931760246646623899502532662132736
      sel (Nat.ble y x)
        (ih (Nat.shiftRight pv 136) (Nat.shiftRight nv 136) (Nat.add c 1)
          (Nat.add ap (Nat.mul (Nat.sub x y) (get32 lp c))) an)
        (ih (Nat.shiftRight pv 136) (Nat.shiftRight nv 136) (Nat.add c 1)
          ap (Nat.add an (Nat.mul (Nat.sub y x) (get32 up c)))))
    cnt

/-- Final comparison: `b · LBs ≥ a · 2n · 2^124` with
`LBs = 2n·A + 2n·Σ_m min(R l, R u) + 2n·2^30·Σ_{[0,1]} min(0,R) + 2^60·min(0, 3T)`. -/
def fin (P : KP) (lp up lamA lamB : Nat) : K := fun _ rp rn tp tn ap an =>
  let w := Nat.mul 136 P.nB
  let mc := mcols lp up P.nB (Nat.mod rp (Nat.pow 2 w)) (Nat.mod rn (Nat.pow 2 w)) 0 0 0
  let neg01 := swarNeg (Nat.sub P.NC1 P.nB) (Nat.shiftRight rp w) (Nat.shiftRight rn w)
  let n2 := Nat.mul 2 P.n
  Nat.ble
    (Nat.add (Nat.mul lamB (Nat.add (Nat.mul n2 (Nat.add an (Nat.add mc.2 (Nat.shiftLeft neg01 30))))
        (sel (Nat.ble (Nat.add tp 1) tn) (Nat.shiftLeft (Nat.mul 3 (Nat.sub tn tp)) 60) 0)))
      (Nat.mul (Nat.mul lamA n2) 21267647932558653966460912964485513216))   -- 2^124
    (Nat.mul lamB (Nat.mul n2 (Nat.add ap mc.1)))

/-- Leaf check for the packed box `(lp, up)` and `cnt` duals in `data` (`cnt < 2^14`). -/
def leafOK (P : KP) (lamA lamB lp up cnt data : Nat) : Bool :=
  sel (Nat.ble cnt 16383)
    (loop P lp up (fin P lp up lamA lamB) cnt data 0 0 (Nat.mul (Nat.mul 2 P.n) 18446744073709551616) 0 0 0)
    false

/-! ## Propagation on packed boxes -/

/-- Replace 32-bit slot `i` of `x` by `v` (`v < 2^32`). -/
def set32 (x i v : Nat) : Nat :=
  Nat.add (Nat.sub x (Nat.shiftLeft (get32 x i) (Nat.mul 32 i))) (Nat.shiftLeft v (Nat.mul 32 i))

def nmax (a b : Nat) : Nat := sel (Nat.ble a b) b a
def nmin (a b : Nat) : Nat := sel (Nat.ble a b) a b

/-- One update at an internal block `(b, c1, c2)`, all six values from the old ones (`verify.Spec.propagate`).
Subtractions are truncated (sound: they only loosen bounds). -/
def upd (b c1 c2 : Nat) (lp up : Nat) (k : Nat → Nat → Nat × Nat) : Nat × Nat :=
  let Lb := get32 lp b
  let Ub := get32 up b
  let L1 := get32 lp c1
  let U1 := get32 up c1
  let L2 := get32 lp c2
  let U2 := get32 up c2
  k (set32 (set32 (set32 lp b (nmax Lb (Nat.add L1 L2))) c1 (nmax L1 (Nat.sub Lb U2))) c2 (nmax L2 (Nat.sub Lb U1)))
    (set32 (set32 (set32 up b (nmin Ub (Nat.add U1 U2))) c1 (nmin U1 (Nat.sub Ub L2))) c2 (nmin U2 (Nat.sub Ub L1)))

/-- One sweep over the internal blocks listed in `intTab` (21-bit entries `b | c1 | c2`, 7 bits each). -/
def sweep (P : KP) (lp up : Nat) : Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat × Nat) (fun _ lp up => (lp, up))
    (fun _ ih tab lp up =>
      let e := Nat.mod tab 2097152
      upd (Nat.mod e 128) (Nat.mod (Nat.shiftRight e 7) 128) (Nat.shiftRight e 14) lp up
        (ih (Nat.shiftRight tab 21)))
    P.nInt P.intTab lp up

/-- `k` sweeps after fixing the root mass to 1 (`2^30`). -/
def propK (P : KP) (k lp up : Nat) : Nat × Nat :=
  Nat.rec (motive := fun _ => Nat × Nat)
    (set32 lp 0 (nmax (get32 lp 0) 1073741824), set32 up 0 (nmin (get32 up 0) 1073741824))
    (fun _ ih => sweep P ih.1 ih.2) k

/-! ## The DFS stack machine on packed boxes -/

/-- Records (LSB first), tag 2 bits: `0` split `b (7) | s (31) | k0 (4) | k1 (4)`; `1` leaf `cnt (14)` then the
duals (`cnt` chunks of 88 bits); `2` delegated (the popped box is moved to the output, as an `S` record of verify.py).
The result is the delegated boxes (in record order) followed by the final stack. -/
def runK (P : KP) (lamA lamB : Nat) (nrec : Nat) : Nat → List (Nat × Nat) → Option (List (Nat × Nat)) :=
  Nat.rec (motive := fun _ => Nat → List (Nat × Nat) → Option (List (Nat × Nat)))
    (fun _ stk => some stk)
    (fun _ ih data stk =>
      List.rec (motive := fun _ => Option (List (Nat × Nat))) none
        (fun bx stk' _ =>
          sel (Nat.beq (Nat.mod data 4) 0)
            (ih (Nat.shiftRight data 48)
              (propK P (Nat.mod (Nat.shiftRight data 44) 16)
                  (set32 bx.1 (Nat.mod (Nat.shiftRight data 2) 128) (Nat.mod (Nat.shiftRight data 9) 2147483648)) bx.2 ::
                propK P (Nat.mod (Nat.shiftRight data 40) 16) bx.1
                  (set32 bx.2 (Nat.mod (Nat.shiftRight data 2) 128) (Nat.mod (Nat.shiftRight data 9) 2147483648)) ::
                stk'))
            (sel (Nat.beq (Nat.mod data 4) 1)
              (sel (leafOK P lamA lamB bx.1 bx.2 (Nat.mod (Nat.shiftRight data 2) 16384)
                  (Nat.land (Nat.shiftRight data 16)
                    (Nat.sub (Nat.pow 2 (Nat.mul 88 (Nat.mod (Nat.shiftRight data 2) 16384))) 1)))
                (ih (Nat.shiftRight (Nat.shiftRight data 16) (Nat.mul 88 (Nat.mod (Nat.shiftRight data 2) 16384))) stk')
                none)
              (Option.map (List.cons bx) (ih (Nat.shiftRight data 2) stk'))))
        stk)
    nrec

/-- Kernel-friendly equality of box lists. -/
def stkEq : List (Nat × Nat) → List (Nat × Nat) → Bool :=
  List.rec (motive := fun _ => List (Nat × Nat) → Bool)
    (fun t => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) t)
    (fun x _ ih t => List.rec (motive := fun _ => Bool) false
      (fun y ys _ => sel (Nat.beq x.1 y.1) (sel (Nat.beq x.2 y.2) (ih ys) false) false) t)

/-- A segment: from the stack `sin`, `nrec` records in `data` end with `sout`. -/
def segCheck (P : KP) (lamA lamB nrec data : Nat) (sin sout : List (Nat × Nat)) : Bool :=
  Option.rec (motive := fun _ => Bool) false (fun s => stkEq s sout) (runK P lamA lamB nrec data sin)

end

end AutocorrK
