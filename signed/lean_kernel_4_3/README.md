# Lean 4 kernel-only proof of C₃ ≥ C₃′ ≥ 4/3

This directory holds a Lean 4 + Mathlib proof of Theorem 1.3 of the paper, C₃ ≥ C₃′ ≥ 4/3, for the signed third
autocorrelation constants, in which every finite certificate check is proved by `decide +kernel`. The three theorems
depend only on `propext`, `Classical.choice` and `Quot.sound`. The trusted base is Lean's kernel, including its built-in
arithmetic on natural numbers; `native_decide` is not used. The proof is built from the same nested certificate with
τ = 1/4 as `../lean_4_3`: `one_sided_tau1_4_parts.tar` in the Zenodo record holds the 2,048 parts
`cert_t25_sub_000.json.gz` … `cert_t25_sub_2047.json.gz` and their `SHA256SUMS`
(sha256 4116fdcd8591e1926784f7791af10d1124d7981af4d2ae755c276f9f6298947c).

An independent check found this build "SOUND (kernel only, sampled)": the three theorems have exactly the reviewed
statements and depend only on `propext`, `Classical.choice` and `Quot.sound`. The check rebuilt the library byte for
byte. It compared all 211,588 compiled data files with our hash lists and confirmed that none declares an axiom or
refers to native evaluation, that each of the 207,571 data modules carries the same data as the corresponding module
of `../lean_4_3`, and that the `C64NData` modules in `Main`'s import closure are exactly these data files plus `Glob`,
`Hgn`, the 1,229 R modules and `Main` (212,820 in all). It regenerated and recompiled `Hgn`, the 1,229 R modules and
`Main` byte for byte, and replayed them and the library in Lean's kernel with `leanchecker`. The proofs of the data
files were re-checked in Lean's kernel only in samples: 12 parts recompiled byte for byte, 184 files replayed with
`leanchecker`, the 102 files that were compiled again after reaching the time limit (see "Build record") together with
the 102 modules built on them, and 30 randomly chosen of the 426 files whose first builds left no logs. External kernels
checked 5 sampled data modules, and `leanchecker`, nanoda and lean4lean accepted the export of the assembly of one arc
with every declaration it depends on. For the kernel check of the other data files, the proof rests on our build.

## Statements (`src/C64/Defs.lean`)

The statements are those of `../lean_4_3`, with the same proofs of soundness:
* `C64NData.mainStatement : C64.MainStatement`. Let `f : ℝ → ℝ` be integrable and zero almost everywhere outside
  `[−1/4, 1/4]`, with `∫ f ≠ 0`. Then every real number `M` with `(f ⋆ f)(t) ≤ M` for almost every `t` satisfies
  `(4/3) (∫ f)² < M`.
* `C64NData.mainStatementEss : C64.MainStatementEss`. For the same `f`, with essential suprema in `EReal`:
  `(4/3) (∫ f)² < ess sup (f ⋆ f) ≤ ess sup |f ⋆ f|`.
* `C64NData.constStatement : C64.ConstStatement`, i.e. `4/3 ≤ C₃′ ≤ C₃`.

## How the proof works

The native proof in `../lean_4_3` proves 207,572 statements of the form `checkSubN glob … node = true`,
`checkArcN glob A<p>.arc = true` and `checkGlobN glob = true` by `native_decide`, and assembles the theorems from them.
This proof proves the same statements in Lean's kernel and reuses the assembly.

* `src/C64/` and `src/C64Core/` are the soundness proofs and the checker of `../lean_4_3`. Here the checker is not
  compiled; it serves as the definition of the statements. The Lean files in `src/` are the sources that were compiled,
  except for one docstring line of `C64/Check/SettleN.lean` (see "Versions and hashes"). So the comments of
  `C64/Check/SettleN.lean`, `SoundNMain.lean` and `SoundNW.lean` use the earlier numbering of Section 6: their Lemma X
  is Lemma 6.9 of the paper, L8-iv is Lemma 6.10, and Theorem 3 is Proposition 6.12. `../lean_4_3` cites the paper's
  numbering in these comments; the code is the same.
* `src/C64K/` is the kernel layer, in core Lean except for the simulation files:
  * `KBall.lean`, `KNum.lean`, `KChk.lean` and `KNest.lean` port the checker function by function to sign-magnitude
    balls with natural-number primitives, a form the kernel evaluates quickly.
  * `KNestSim.lean` (with `KBallSim.lean`, `KNumSim.lean`, `KChkSim.lean`, `KChkSim2.lean`, which use Mathlib) proves
    for all inputs `checkSubNK_eq`, `checkArcNK_eq` and `checkGlobNK_eq`: the port computes exactly the values of
    `C64Chk.checkSubN`, `checkArcN` and `checkGlobN`. So a kernel-checked `checkSubNK … = true` gives the native
    statement by rewriting (`checkSubN_of_K`, `checkArcN_of_K`, `checkGlobN_of_K`).
  * Lazy tube data. Each tube carries 508 pieces for the functions of t on 7 levels, of which a check usually reads only
    level 0. Under a cheap guard on the glob's constants, the tube's end points and the tile's size (`tsLazyOK`,
    `KPieceGood.lean`), `KNest.tubeC` builds these pieces lazily, so the kernel computes a piece only when a check reads
    it. `KPieceSome.lean` proves that every such piece exists (`C64KPiece.tPiece_isSome`), so `tubeC` has the same
    value either way (`tubeC_eq`, for all inputs).
  * `KParts.lean`, `KSeg.lean`, `KCover.lean`, `KCoverL.lean`, `KHint2.lean` and `KHintGlue.lean` split one statement
    `checkSubNK … = true` into many kernel checks: node parts, segments of a witness leaf's walk, and units of whole
    subtrees, and prove the statement from them. A hinted segment follows a record of the checker's own search (a
    tree of splits); `segF_of_segFT` proves the plain segment from the hinted one for every hint, so hints are untrusted
    data. A wrong hint makes the hinted check fail; it cannot make a false statement provable.
* `src/C64KX/HintGen.lean` is the hint pass of the generator. No proof module imports it.
* `src/tools/` holds the generator, the assembly generator and the build scripts:
  * The generator `gen_nest_data_k_v2.py` writes, for each of the 207,571 data modules of `../lean_4_3` (same names), a
    kernel data module that states `okK : checkSubNK glob … node = true` (arc modules: `checkArcNK`) and proves it from
    its units by `decide +kernel`. It imports the native exporter in `tools/n/` and takes the module split, the names,
    the statements and the data terms from it. A module with more than about 8 hours of kernel time is split into
    several files: the data module, files `KD_<M>_<k>` of units, and a last `KD_<M>_<k>` that proves `okK` from them.
    In all, the 207,571 modules take 211,588 files. `Glob.lean` holds the global data; the kernel proof of
    `checkGlobNK glob = true` is in `Hgn.lean`.
  * The assembly generator `gen_main_nest_k_v3.py` writes `Hgn`, the 1,229 modules `R<p>` and `Main` with the statements
    of the native assembly (`gen_main_nest_r2.py`); only the proofs change, to `checkSubN_of_K <M>.okK`,
    `checkArcN_of_K <A>.okK` and `checkGlobN_of_K globOKK`. The kernel arc modules define `arc` as `noncomputable`
    (no compiled code), so the lists `arcs0` … `arcs12` and `arcs` in `Main` are `noncomputable def` as well; this
    switches off code generation only. `check_k_vs_n_v3.py` checks that undoing these changes gives the native
    assembly's sources byte for byte.
  * `export_parts_k.sh`, `build_modules_k.sh` and `assemble_k.sh` run the steps under "Building"; `check_axioms_k.py`
    checks the output of `Axioms.lean`; `kbuild_raw_v1.py` compiles the library without lake; `hints_from_sources_k.py`
    writes the hint files of a part from its generated sources and the compile logs of its native data modules.

## Axioms

`Axioms.lean` is the file that `assemble_k.sh` writes and compiles in step 4. In our build it printed

    'C64NData.constStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
    'C64NData.mainStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
    'C64NData.mainStatementEss' depends on axioms: [propext, Classical.choice, Quot.sound]

`tools/check_axioms_k.py` accepts this output only if each of the three theorems depends on exactly these three axioms.

## Versions and hashes

* Toolchain: `leanprover/lean4:v4.35.0-rc3`. Mathlib: `v4.35.0-rc3`, commit c55e6e786f49 (`src/lake-manifest.json`).
* `source_sha256.txt` gives the sha256 of every file in `src/`. Outside `src/tools/` these are the sources that were
  compiled, except `C64/Check/SettleN.lean`: one line of its module docstring was edited after the build, keeping its
  length, and `SCRUBBED_FILES.tsv` lists the sha256 of both versions of the file and of its compiled file, which stores
  the docstring and differs in those bytes only. Four Python tools differ from the copies that ran only in comments
  and docstrings: without their docstrings, both copies parse to the same syntax tree (Python's `ast` module). The
  copies that ran have sha256
  * `gen_nest_data_k_v2.py`: 2b0bb58ee22ea3d5b7610dfd66ffc5f36560bcfefe859dc4894856a52066ad76,
  * `gen_main_nest_k_v3.py`: 1cc7c135b653f424b500cc6d1b430ab9102d863b7ad96edf620aa85504bcf565,
  * `check_k_vs_n_v3.py`: 7bf3b9fbef9d211343f859a5ea051742716bca29d06ac944baf2beca8e39e965,
  * `kbuild_raw_v1.py`: b6ca163bbfd5aebc956ca11af32f1be576f1aa2b5e251b88696a7c60533e6c66.

  `gen_main_nest_r2.py` and the files in `tools/n/` are byte for byte those of the native run in
  `../lean_4_3/src/tools/` (where `gen_nest_data_run3.py` is called `gen_nest_data.py`). The other scripts in
  `src/tools/` were written for this directory.
* The library was compiled once with the toolchain above and the lake options of `src/lakefile.toml` passed as `-D`
  flags, every module with `lean -o` in import order, in the directory `/k43/kdev`. Modules that import Mathlib record
  the path of their own source file in the compiled file, so a byte-for-byte rebuild of those modules needs the same
  directory; the checker (`C64Core/`) and the files of `C64K/` that use only core Lean do not depend on it.
* The Zenodo record holds two lists in the format of `sha256sum`, one line per file:
  * `k43_sources.sha256.gz`: the 216,504 files that the generator writes for the 1,229 parts, with paths `P<p>/…`
    relative to `OUT` (step 2 below), and the 1,235 files that step 4 writes into `m/C64NData` (`Hgn`, the R modules,
    `Main`, `Axioms.lean` and the merged index files), with paths `m/…` relative to `/k43/asm`;
  * `k43_oleans.sha256.gz`: the compiled files of the 54 library modules, with paths relative to
    `src/.lake/build/lib/lean`, and of the 212,820 generated modules (`Glob`, the 211,588 data files, `Hgn`, the 1,229
    R modules and `Main`), with paths `C64NData/…` relative to `BUILD` (step 3 below). Its line for
    `C64/Check/SettleN.olean` is that of the file compiled from the source in this directory.

  `k43_sources.sha256.gz` has 217,739 lines, 9,182,325 bytes and sha256
  32e8f8d8e162cc48199f17504ef11c75f4d142a5c83e2c47a8600354c585f4cc; `k43_oleans.sha256.gz` has 212,874 lines,
  8,948,433 bytes and sha256 5b8d685dd13bdf87f195d8a68118facdd8fe288e1e70f19e7b9cbb682ee20abf.
* The merged index that step 4 writes, `m/C64NData/index.json`, has sha256
  73b7f9481948cf4ee79904e9725a69d101db001569b2503bced6db9e3a0eaa30, the same as the native assembly's.

## Building

Requirements:
* elan (`src/lean-toolchain`), Mathlib as pinned above, and Python 3 with `python-flint` 0.9.0;
* the certificate `one_sided_tau1_4_parts.tar` and the hint archive `one_sided_tau1_4_kernel_hints.tar.xz` from the
  Zenodo record (764,524,144 bytes, sha256 b46851a3f21b0c4ea2bdcdfc16b39a1b757a63a5519c5fd59753a7540c8b8365). The
  archive holds, for each part p, the hints `P<p>/<M>.hb` of its modules and `P<p>/ntimes.tsv`, the compile times of the
  native data modules, which decide how large modules are split; with the certificate it regenerates every generated
  source;
* memory and time: the scripts set no limit on the memory or the time of a single file, so a compile stops early only if
  the machine runs out of memory. Column 3 of each `jobs.tsv` gives the estimated peak memory of a data file, at most
  21.9 GB, but in our build 11,602 of the 211,162 data files with a measured peak (5.5%) needed more than 22 GB. Of the
  118,691 files estimated at 21.9 GB, the median peak was 16.3 GB, the 99th percentile 27.5 GB, the 99.9th percentile
  32.4 GB and the maximum 70.8 GB; files with smaller estimates needed at most 50.6 GB. Nineteen files needed more than
  40 GB: `KD_A0170_2` (70.8 GB), `KD_A0174_2` (65.4), `KD_A0173_2` (56.8), `A0279S375` (54.9), `A0280S369` (54.1),
  `A0278S377` (52.7), `A0275S340` (51.8), `A0341S477` (50.6), `A0335S480` (49.3), `A0277S378` (48.2), `A0277S377`
  (47.3), `A0277S379` (45.2), `KD_A0509_2` (43.5), `A0278S375` (43.1), `A0278S374` (43.1), `A0471S263` (42.3),
  `A0277S373` (42.0), `A0314S289` (40.5) and `A0310S288` (40.4). Give step 3 at least JOBS × 22 GB + 60 GB of
  memory. If a compile is stopped for lack of memory anyway, its log does not end with `OK`; running step 3 again,
  with a smaller `JOBS` if needed, skips every file whose log ends with `OK` and compiles the others. Step 4 compiles
  the R modules `JOBS` at a time, each with at most 9 GiB in our build, and then `Main` alone, which needs about
  170 GB (156 GiB at its peak), an open-file limit of at least 300,000 and `vm.max_map_count` of at least 2,000,000;
  when run again, step 4 compiles all R modules again. The time estimates (column 4) of the 1,199 last files of split
  modules are far too low: 102 of them did not finish within 15 minutes in our build, and compiled again on less loaded
  servers they took 5 to 17 minutes each (median 12.5 minutes), with at most 2.8 GiB of memory.

Run the steps in `src/`. `PARTS`, `HINTS`, `OUT` and `BUILD` are directories of your choice; `JOBS` is the number of
parallel processes. The scripts are run with `bash`.

0. Unpack the certificate into `PARTS` and check it: `(cd PARTS && sha256sum -c SHA256SUMS)`. Unpack the hint archive
   into `HINTS` and check it the same way. Only parts 000 to 1228 are used.
1. Build Mathlib and the library:

       lake exe cache get
       lake build C64Core C64Core.Load C64K C64KX C64.Check.SoundMirror

   The compiled files of the checker and of the core-Lean files of `C64K/` do not depend on the directory. To reproduce
   the published compiled files of the modules that import Mathlib as well, put `src/` at `/k43/kdev` and build with
   `tools/kbuild_raw_v1.py` instead, as described in its header.
2. Write the kernel data modules from the certificate and the hints, one part per process. The script prints
   `exported 1229 of 1229`:

       bash tools/export_parts_k.sh PARTS HINTS OUT JOBS

3. Compile `Glob` and the data files. The logs end with `OK ms` or `FAIL ms`, and the last line of output is the number
   of failed or missing files, which must be 0; if it is not, run the step again (see the memory note above):

       bash tools/build_modules_k.sh OUT BUILD JOBS

4. Assemble in `/k43/asm`. The script merges the index, writes `Hgn`, the 1,229 R modules and `Main`, checks that they
   state what the native assembly states, compiles them, and checks the axioms of the three theorems:

       bash tools/assemble_k.sh OUT BUILD JOBS

5. Optionally, compare the sources and the compiled files with the two lists of the Zenodo record (see "Versions and
   hashes"). Each command prints nothing if all files match:

       zcat k43_sources.sha256.gz | grep '  P' | (cd OUT && sha256sum -c --quiet)
       zcat k43_sources.sha256.gz | grep '  m/' | (cd /k43/asm && sha256sum -c --quiet)
       zcat k43_oleans.sha256.gz | grep '  C64NData/' | (cd BUILD && sha256sum -c --quiet)
       zcat k43_oleans.sha256.gz | grep -v '  C64NData/' | (cd .lake/build/lib/lean && sha256sum -c --quiet)

   The compiled files of the modules that import Mathlib (`C64/`, the simulation files of `C64K/`, `Hgn`, the R modules
   and `Main`) match only if the library was built with `kbuild_raw_v1.py` in `/k43/kdev` (step 1) and the assembly
   was written in `/k43/asm`.

The scripts were tested as follows. From the certificate and the hint archive, `export_parts_k.sh` regenerated the
sources of all 1,229 parts (216,504 files) byte for byte. For parts 744 and 1092, `build_modules_k.sh` reproduced the
compiled data modules and `Glob` byte for byte, and an earlier version of `assemble_k.sh`, which differs only in how it
writes `Main`, compiled `Hgn`, `R0744` and `R1092` for these two parts byte for byte as in our build. From the merged
index of our build, `gen_main_nest_k_v3.py` wrote `Hgn`, the 1,229 R modules and `Main` byte for byte as in our build,
and `check_k_vs_n_v3.py` accepted them.

## Build record

Our build compiled the 54 library modules and the 212,820 generated modules. The data files were
compiled one per hardware thread on 105 servers with 176 hardware threads each, in 47.3 hours of wall-clock time. The
compile jobs used about 312,300 CPU-hours (measured user and system time; about 2,250 more on three servers that failed
early were not recorded), while the servers were allocated for 3,670 server-hours (645,500 thread-hours). The largest
memory of a data file was 66 GiB (`KD_A0170_2`, estimated at 21.9 GB). The 1,229 R modules then took 609 CPU-hours on
one server with 360 hardware threads; the longest, `R0321`, took 3.6 hours, and none needed more than 9 GiB. `Main` took
92 seconds and 156 GiB of memory. The assembly ended 52.0 hours after the start of the build.

Our scheduler stopped 184 compiles, and each was run again and finished. 82 were data files: 53 went over the memory
limit that the scheduler had set from their estimates, and 29 were stopped because their server ran short of memory.
The other 102 were last files of split modules, in 42 parts, which reached the scheduler's shortest time limit of
900 seconds, since their estimated times were under a minute; they were compiled again with a shortest limit of
6 hours. The published hash lists contain the files of the successful runs. The scripts in `src/tools/` set no memory
or time limit.
