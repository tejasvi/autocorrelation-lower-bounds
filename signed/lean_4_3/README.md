# Lean 4 proof of C₃ ≥ C₃′ ≥ 4/3

This directory holds a Lean 4 + Mathlib proof of Theorem 1.3 of the paper, C₃ ≥ C₃′ ≥ 4/3, for the signed third
autocorrelation constants. The proof is built from the nested certificate with τ = 1/4 in the Zenodo record:
`one_sided_tau1_4_parts.tar` holds the 2,048 parts `cert_t25_sub_000.json.gz` … `cert_t25_sub_2047.json.gz` and their
`SHA256SUMS` (sha256 4116fdcd8591e1926784f7791af10d1124d7981af4d2ae755c276f9f6298947c). Docstrings in `src/` number some
lemmas of Section 6 differently from the paper; `../lean_25_19/README.md` gives the correspondence for the shared files.

C₃ ≥ C₃′ ≥ 4/3 is verified in Lean 4 with Mathlib. The 207,572 finite certificate checks are evaluated by `native_decide`,
with one auxiliary axiom per check. An independent rebuild from the certificate reproduced every compiled file byte for
byte and re-checked every module in Lean's kernel. A seeded sample of 20 data modules and one arc's assembly module was
exported and accepted by `leanchecker`, nanoda and lean4lean. The complete export has not been checked by external
kernels.

There is no kernel-only proof of 4/3. The 25/19 and 30/23 bounds have kernel-only proofs, in `../lean_kernel_25_19` and
`../lean_kernel`.

## Statements (`src/C64/Defs.lean`)

* `C64NData.mainStatement : C64.MainStatement`. Let `f : ℝ → ℝ` be integrable and zero almost everywhere outside
  `[−1/4, 1/4]`, with `∫ f ≠ 0`. Then every real number `M` with `(f ⋆ f)(t) ≤ M` for almost every `t` satisfies
  `(4/3) (∫ f)² < M`.
* `C64NData.mainStatementEss : C64.MainStatementEss`. For the same `f`, with essential suprema in `EReal`:
  `(4/3) (∫ f)² < ess sup (f ⋆ f) ≤ ess sup |f ⋆ f|`.
* `C64NData.constStatement : C64.ConstStatement`, i.e. `4/3 ≤ C₃′ ≤ C₃`. Here `C₃′` is the supremum in `EReal` of the
  constants `C` such that every admissible `f` and every real almost-everywhere upper bound `M` of `f ⋆ f` satisfy
  `C (∫ f)² ≤ M`. `C₃` is defined the same way with `|f ⋆ f|` in place of `f ⋆ f`.

Here `f ⋆ f` is Mathlib's convolution with respect to Lebesgue measure. The theorems have no further hypotheses.

## How the proof works

* `src/C64/` contains the soundness proofs. They use only the three standard axioms. It is the tree of the 25/19 proof in
  `../lean_25_19`, with these changes and additions:
  * `C64/Defs.lean` sets the constant to 4/3, which corresponds to τ = 1/4.
  * `C64/Check/SoundMain.lean` sets τ = 1/4 in the hypothesis of `mainStatement_of`, and the constant 4/3 = 1/(1 − 1/4)
    in its proofs.
  * The nested-certificate layer: `C64/Check/SoundNT.lean`, `SettleN.lean`, `SDerivN.lean`, `SoundNP.lean`,
    `SoundNL.lean`, `SoundNW.lean` and `SoundNMain.lean`. It covers node sets with interval tubes, and lets each
    subtree be checked as a separate statement.
  * `C64/Check/SoundMirror.lean` proves the mirror lemma: the lower half of `T₁` follows from the upper half
    (`C64.arcSettled_mirror`, `coverHalfOK_ok`, `mainStatementN_mirror_of`). So the proof checks only the 1,229 arcs of
    the upper half (parts 000 to 1228).
* `src/C64Core/` is the checker. It is written in core Lean and compiled to native code.
  * `Check.lean`, `Ival.lean` and `Num.lean` are as in the 25/19 proof. `C64Core.lean` also imports `C64Core.Nest`.
  * `Nest.lean` checks the nested certificates: witness leaves with interval tubes, empty leaves, interval splits, and
    subtrees as separate statements.
  * The checker's search parameters are part of the data. The exporter sets nL = 7, dS = 4 and dT = 12 (fields of
    `GlobN` and `Glob`). They enter the proof only through the bounds that `checkGlobN` checks.
* `src/tools/` holds the exporter, the assembly generator and the build scripts.
  * `gen_nest_data.py`, with `gen_lean_data.py`, translates each upper-half part into Lean data:
    * `C64NData/Glob.lean` holds the global data, the same for every part.
    * For the arc of part p, the exporter writes `C64NData/A<p>.lean`. Every subtree with more than 16,000 W1 records
      below a hard arc gets its own module `A<p>S<j>.lean`.
    * There are 207,571 data modules. Each proves `checkArcN glob A<p>.arc = true` or `checkSubN glob … node = true` by
      `native_decide`, and `Glob.lean` proves `checkGlobN glob = true`.
  * `gen_main_nest_r2.py` writes the assembly:
    * `C64NData/Hgn.lean`.
    * One module `R<p>.lean` per arc. It proves every subtree statement `SubOK` of that arc, children first, from
      `checkSubN_ok` and the subtree's ext list (by `rfl`). It also proves the arc's own ext facts.
    * `Main.lean` proves `AllOKN` for the 1,229 arcs. It checks by `decide +kernel` that the arcs cover [0, 1/2]
      (`cover_ok`) and derives the three statements with the mirror lemma.
  * The statements do not mention the certificate, so the exporter need not be trusted.
  * `export_parts.sh`, `build_modules.sh` and `assemble.sh` run the build (below). `check_axioms.py` checks the axioms.

## Axioms

Each of the three theorems depends on:
* `propext`, `Classical.choice` and `Quot.sound`;
* 207,572 `native_decide` auxiliary axioms: one for `C64NData.globOK`, and one for each data module `C64NData.<m>.ok`.
  There are 207,571 data modules: the 1,229 arc modules and 206,342 subtree modules.

`native_decide` makes the Lean compiler part of the trusted base. `tools/check_axioms.py` checks the output of
`Axioms.lean` against the merged index. `axioms_summary.txt` is its output for this build.

## Independent check

An independent rebuild did the following:
* It regenerated all data from the certificate parts with the shipped exporter.
* It rebuilt every data module and the assembly from scratch.
* It reproduced every compiled file byte for byte: the 207,571 data modules, `Glob`, `Hgn`, the 1,229 R modules and
  `Main`.
* Lean's kernel re-checked every module at compile time and again by replay.
* The three theorems have exactly the types `C64.MainStatement`, `C64.MainStatementEss` and `C64.ConstStatement`.
* Every auxiliary axiom is tied to its own module's statement.

A seeded sample of 20 data modules and one arc's assembly module was exported and accepted by three kernels:
`leanchecker`, nanoda (with the auxiliaries permitted by name) and lean4lean. A corrupted export was rejected by all three.
The complete export, built from about 16 GB of data source, has not been checked by external kernels.

## Versions and hashes

* Toolchain: `leanprover/lean4:v4.35.0-rc3`. Mathlib: `v4.35.0-rc3`, commit c55e6e786f49 (`src/lake-manifest.json`).
* `source_sha256.txt` gives the sha256 of every file in `src/`. Two of them identify the run's tools:
  * `src/tools/gen_nest_data.py`, the exporter of the run: 5a1e93234d380bae1e9a0a1a5341203924d74517007025c550d9bd5606e5dcbd;
  * `src/tools/gen_main_nest_r2.py`, the assembly generator: 89fb645d973486407892f14310f3ad1e0cc7819e20c72afcf7452be7ce3b8e62.
* `src/lakefile.toml` sets `Elab.async = false` (no parallel elaboration threads). Its comment about kernel-only proofs is
  inherited from the shared project; the nested checker has no kernel-only proof.
* Three files, `src/C64/Check/SettleN.lean`, `SoundNMain.lean` and `SoundNW.lean`, differ from the audited sources only in
  comments, which cite the paper's numbering (Lemma 6.9, Lemma 6.10, Proposition 6.12).
* `data_oleans_sha256.txt` gives the sha256 of the 207,571 compiled data modules (`C64NData/<m>.olean`).
  `top_oleans_sha256.txt` covers `Glob`, `Hgn`, `Main` and the 1,229 R modules. A rebuild with the same toolchain
  reproduces both lists byte for byte; the independent check did.
* The merged index written by `assemble.sh` has sha256 73b7f9481948cf4ee79904e9725a69d101db001569b2503bced6db9e3a0eaa30.
* The generated sources (about 16 GB) are not in this directory. The tools regenerate them from the certificate.

## Building

Requirements:
* elan (`src/lean-toolchain`), Mathlib as pinned above, and Python 3 with `python-flint` 0.9.0;
* about 300 GB of disk;
* for `Main.lean`: about 100 GB of memory, an open-file limit of at least 300,000, and `vm.max_map_count` of at least
  1,000,000, since `Main` maps about 208,800 compiled files.

Run the steps in `src/`. `PARTS`, `OUT`, `BUILD` and `ASM` are directories of your choice; `JOBS` is the number of
parallel processes.

0. Unpack `one_sided_tau1_4_parts.tar` into `PARTS` and check it: `(cd PARTS && sha256sum -c SHA256SUMS)`. Only parts
   000 to 1228 are used.
1. Build Mathlib, the checker (compiled to shared libraries under `.lake/build/lib/lean`) and the soundness proof:

       lake exe cache get
       lake build C64Core C64Core.Load C64.Check.SoundMirror

2. Write the Lean data, one part per process. The script prints `exported 1229 of 1229`:

       tools/export_parts.sh PARTS OUT JOBS

3. Compile `Glob` and the 207,571 data modules. The logs end with `OK ms` or `FAIL ms`, and the last line of output is
   the number of failed modules, which must be 0:

       tools/build_modules.sh OUT BUILD JOBS

4. Assemble. The script merges the index, writes `Hgn`, the 1,229 R modules and `Main`, and compiles them:

       tools/assemble.sh OUT BUILD ASM JOBS

5. Print the axioms and check them. `check_axioms.py` prints OK for each of the three theorems:

       LEAN_PATH=$(lake env printenv LEAN_PATH):BUILD $(lake env which lean) ../Axioms.lean > axioms.txt
       python3 -I tools/check_axioms.py axioms.txt ASM/C64NData/index.json

6. Optionally, compare `BUILD/C64NData/*.olean` with `../data_oleans_sha256.txt` and `../top_oleans_sha256.txt`.

These scripts were tested on two parts, 082 and 1092. They reproduced the run's compiled files byte for byte: `Glob`,
the four data modules, `Hgn` and both R modules.

Resources of this build:
* Data modules: about 8,700 CPU-hours in total (hardware threads of fully loaded servers). That was about two hours of
  wall-clock time on 19 servers with 384 hardware threads each. The median module took 107 s and the slowest 85 minutes;
  a module needs about 2 GB of memory. The compiled data take about 260 GB.
* Assembly: the 1,229 R modules took about 450 CPU-hours. The slowest took about 2.6 hours and up to 9 GB of memory.
  `Hgn` takes about a minute and a half. `Main` took 80 seconds and about 100 GB of memory: the peak was 102.7 GB, and
  102 GB in the independent rebuild. `Axioms.lean` takes about a minute and a half.
