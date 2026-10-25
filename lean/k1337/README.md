# C₁ ≥ 1337/1000 checked by the Lean kernel alone (K1337)

This subpackage re-checks the n = 39 certificate of `C₁ ≥ 1337/1000` (the same certificate as `lean/c1337/`) with
the K39 kernel checker: no native code is involved. Every segment of every job's depth-first log is a
`decide +kernel` check of `AutocorrK.segCheck`; the per-job checks are composed by the inductive `AutocorrK.StkK` in
252 group modules and `Top`, and three jobs are composed semantically in `Sem` (see "The tail jobs"). The final theorem
is `Autocorr.KC1337.autocorr_lower` (`KC1337/Main.lean`), from the approved assembly template; `KC1337/Forms.lean` is
the approved native `Forms` with its import and namespace renamed.

## Contents

* `AutocorrK39/`: the K39 checker library (core Lean: `Core`, `Table`, `Load`, `Stk`) and its soundness proofs
  (`Sound/*`, with Mathlib). It extends the audited KC36 checker for n = 39 (15-bit LP row fields, two-block and
  k-block square cuts).
* `AutocorrK39v2/`: the audited v2 checker under a renamed module prefix and namespace (`AutocorrK39v2.*`,
  `AutocorrK2`; produced by `tools/ns_rename.py`), plus `Bridge.lean`: `AutocorrK2.segK_to_v1` turns a v2 segment
  statement into the v1 `AutocorrK.SegK` at the same spec and λ (definitional, no hypotheses).
* `KC1337/Params.lean`, `KC1337v2/Params.lean`: the certificate's parameter records for the two checkers.
* `KC1337/Top.lean`, `KC1337/Sem.lean`, `KC1337/Main.lean`, `KC1337/Forms.lean`: the assembly. The 252 group modules
  `KC1337/G*.lean` (5.3 GB) are not shipped; `tools/k39asm_sem3.py` regenerates them, byte-identical, from the job
  metadata (available on request with the logs).
* `tools/`: the exporter (`k39export.py`, `kb39.py`, `kc_*.py`, `verify*.py`), the assembly generator (`k39asm.py`;
  `k39asm_sem3.py` adds the semantic mode used here), the scans (`kscan.lean`, `kscan_ext39.lean`,
  `kscan_ext39_hedge.lean`), the merge checks of the tail jobs (`tailfix_*.py`, `hedge_check.py`), the cache prefetch
  (`prefetch_olean.py`), the exporter patch for the tail jobs (`kb39_segfix.diff`) and the v2 rename (`ns_rename.py`).
  Nothing in `tools/` is trusted: the kernel checks every module.
* `scripts/`: the fleet node (`startup3c.sh`, `k39node3b.sh`), the partial-chunk export (`partial_chunk_v1.sh`) and
  the assembly stages (`k39asmnode3.sh`, `k39asmnode6.sh`, `k39asmsem4.sh`). Run them with `bash x.sh`. They expect
  `CERT_URL` (the certificate's storage location), `RESULTS_URL` (the results location) and `KIT_URL` (the kit
  location); `startup3c.sh` also takes the fleet item from `K39_SET`, `K39_TARS` and `K39_PART` (on the fleet, these
  were the VM's metadata attributes).
* `results/`: the plan (`plan.json`), the list sources of every chunk (`asm_list_sources.txt`), the module scan
  (`kscan_modules.txt`, `external.txt`, `ext.txt`, `ext_hedge.txt`), the stage log (`stages.txt`), the build times of
  the assembly modules (`times.txt`), the sha256 of the assembly oleans (`k1337_top_oleans.sha256`), and the records of
  the tail jobs (`tailfix/`, `hedge_v2/`).

## The tail jobs

Nine of the 5,033,964 jobs checked very slowly under v1: in each, one segment took hours (the slowest finished job
needed 9.1 hours). They were handled without changing any trusted file:

* Six jobs were re-exported with `tools/kb39_segfix.diff` (an untrusted exporter change: a leaf always starts a new
  segment) and checked under the same v1 library. Their root path hash, leaf count and delegated subtrees are
  unchanged, so the assembly links them as before (`results/tailfix/`).
* Three jobs (`49ba5d56…`, `b103f942…`, `e2ba295e…`, all parts) were checked by the v2 checker in their original
  segmentation (`KC1337v2/…`; `results/hedge_v2/`). They have no `StkK` derivation, so they and their 40 ancestor jobs
  are composed in `Sem`: per segment `AutocorrK.segK_of_check` (v1) or `AutocorrK2.segK_to_v1 ∘ AutocorrK2.segK_of_check`
  (v2), per delegated child `AutocorrK.StackOKK.cons` with `(AutocorrK.stkK_sound jfull_<child>).head`, giving
  `okfull_<job> : AutocorrK.StackOKK (mkSpec 39) (1337/1000) [box]`. `Main` uses `okfull_root.head` where the native
  path uses `(stkK_sound … jfull_root).head`; its statements are unchanged.

Each job comes from exactly one source: the fleet, the re-export, or v2.

## Figures

- Jobs: 5,033,964, with 89,673,710 leaves; check modules: 5,164,010 (5,163,994 from the fleet, 10 re-exported,
  6 from v2); 252 group modules of at most 20,000 jobs, `Top` (343 top jobs), `Sem` (43 jobs), `Main`, `Forms`.
- Build of the check modules: 186,605 CPU-hours (user and system time of the builds that produced the shipped oleans),
  on spot VMs with 80 to 176 vCPUs.
- Assembly, on one server with 224 vCPUs and 2.9 TB of memory: the group modules in 28 minutes (216 in parallel);
  `Top` 1,681 s, `Sem` 2,069 s, `Main` 1,062 s, `Forms` 1,037 s, each importing all modules (up to 2.38 TB resident,
  almost all of it mapped olean files). Importing every module needs `vm.max_map_count` above 5.2 million.
- Module scan (`results/`): 5,164,268 modules and 373,604,858 constants, 0 violations; the 133 external references
  depend on `propext`, `Classical.choice` and `Quot.sound` only.

## Independent audit

The independent audit (verdict: sound, kernel only, sampled) replayed the whole assembly in its own kernel (`Params`,
the 252 group modules, `Top`, `Sem`, `Main` and `Forms`). It found the three final statements equal, as expressions,
to the reviewed statement template with λ = 1337/1000, and depending only on `propext`, `Classical.choice` and
`Quot.sound`. All 5,164,004 `KC1337` job oleans equal the published lists, and its own rebuilds were byte-identical
for a 2% sample of the job units (103,602 modules), the five most CPU-heavy modules, the ten re-exported tail modules and
the six v2 job modules with their parameters. "Sampled" means that the job modules' own constants (368,569,492) were
kernel-checked by the fleet's builds and re-checked by the audit only on that sample. One planned control (a job
theorem given another job's proof) ran, but its result was lost. In its place, a theorem of type `False` carrying a job
proof was rejected, and in a miniature of the group modules built from two rebuilt jobs, a swapped job proof, a job olean
under another job's name and two altered job theorems were all rejected.

## Comparing a rebuild with the published hashes

`k1337_check_oleans.sha256.gz` (a separate file of the record, in two parts) lists the sha256 of every check module,
5,164,010 lines; each line is `sha256  KC1337/<dir>/<module>.olean` or `sha256  KC1337v2/<dir>/<module>.olean`, with
the path relative to the build root that holds `KC1337/` and `KC1337v2/`. To join the parts and compare:

    cat k1337_check_oleans.sha256.gz.part00 k1337_check_oleans.sha256.gz.part01 > k1337_check_oleans.sha256.gz
    sha256sum -c k1337_check_oleans.sha256.gz.sha256
    cd /path/to/build/root
    zcat /path/to/k1337_check_oleans.sha256.gz | sha256sum -c --quiet --ignore-missing

`results/k1337_top_oleans.sha256` lists the assembly oleans the same way.
