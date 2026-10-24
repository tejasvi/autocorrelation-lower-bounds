# c1337: native Lean proof of C1 ≥ 1337/1000 (C1337)

This directory is a self-contained Lean package: the library and tools with which C1337 was built, unchanged, plus
the build scripts (`scripts/`), the reviewed statement files (`proposal/`) and the results (`results/C1337/`).

Its library is the one in `../kc36/`, byte for byte (`Autocorr/`, `AutocorrCert/{Checker,CheckerX,Decode,DecodeX}.lean`,
`AutocorrK/`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, and the tools `export.py`, `export_jobsx.py`,
`checker_path.py`, `build_dag.py`, `forms.py`), with these additions:

* `AutocorrCert/GroupCheckX.lean`: `checkGroupStrX`, the check of one group of jobs (each job by `checkJobStrX` of
  `AutocorrCert/DecodeX.lean`, plus the links between the jobs of the group and the subtree roots it imports), with
  the lemmas `coveredX_of_checkGroupStrX` and `coveredX_root_of_checkGroupStrX`: one `native_decide` per group module
  gives the coverage of all its jobs;
* `AutocorrCert/CheckerXF.lean`: a faster evaluation of `checkJobStrX` and `checkGroupStrX`, with equalities for all
  inputs (`checkJobStrXF_eq`, `checkGroupStrXF_eq`); each module's `native_decide` runs the fast code, and its theorem
  still states the check with `checkGroupStrX`;
* `tools/export_shard_v2.py`: the exporter (`--pack --group-check --fast --group-leaves 1000 --main`). Nothing in it is
  trusted: the theorem of every group module is checked by `native_decide`;
* `tools/nscan_xf.lean`, `tools/nscan_ext_xf.lean`: the module scan and the scan of external references.

Package C1337: λ = 1337/1000, certificate c1337 (n = 39), checked through `native_decide`; all three theorems
(`Autocorr.C1337.autocorr_lower`, `autocorr_lower_ess`, `autocorr_lower_real`, with the statements of `../README.md`
for a/b = 1337/1000). `#print axioms` for each: propext, Classical.choice, Quot.sound and 124,632 `native_decide`
axioms (one per group module, plus `rootOK`), nothing else (`results/C1337/axioms_summary.txt`).

## Building from the certificate

The input is the c1337 certificate (178 D-log archives, 5,033,964 job files, 89,673,710 leaves) with its 2,412
tree-only jobs filled. The filled files are archived with the D logs, and `c1337_filled_jobs.sha256` (a separate file
of the record) lists their hashes. `../../checker/verify_tree_dump.py` with `VT_DUMP_DIR` set writes them again, with
the same content but new time stamps in their gzip headers, so their file hashes differ from that list. Only inputs
identical to the certificate's manifests and to that list reproduce the hashes in `c1337_oleans.sha256.gz`: a rebuild
from regenerated files gives the same three theorems, but the group modules that hold filled jobs record each input's
sha256 in their manifest and so get other hashes.

`scripts/drive5.sh` runs the stages below in order on one server (paths under `/scratch` as on the build server;
`scripts/setup_vm.sh` prepared that server). The other scripts are the ones it calls. The scripts read the certificate,
results and kit locations from `CERT_URL`, `RESULTS_URL` and `KIT_URL`, and `setup_vm.sh` reads the local NVMe devices
from `LOCAL_SSD_GLOB`.

1. `lake build` in this directory (Lean v4.35.0-rc3, Mathlib per `lake-manifest.json`), then compile `CheckerXF` and
   `GroupCheckX` to shared libraries (`lean -c`, `leanc -shared`; see `scripts/setup_vm.sh`). The build loads six checker
   libraries: Checker, Decode, CheckerX, DecodeX, GroupCheckX, CheckerXF.
2. Scan (`scripts/scan.py`): every job file against the sha256 manifests of the certificate.
3. Fill: `../../checker/verify_tree_dump.py` writes the 2,412 filled jobs; they replace the originals (the build used
   the files listed in `c1337_filled_jobs.sha256`).
4. Export: `tools/export_shard_v2.py CERTDIR C1337 --pack --group-check --fast --group-leaves 1000 --main` writes 124,631
   group modules and `Zo`, `Main`, `Forms`.
5. Job map (`scripts/jobmap.py`): every job file is in exactly one group module, with the sha256 of its input.
6. Statements: `tools/forms.py C1337 39 1337 1000`; `Forms.lean` must equal `proposal/C1337_Forms.lean`, and
   `scripts/check_bound.py` checks the bound in `Main.lean` against `proposal/C1337_bound_expected.lean`.
7. Build: `tools/build_dag.py` (native, with the six libraries).
8. Axioms: `#print axioms` of the three theorems (`scripts/axsum.py` summarizes it); `tools/nscan_xf.lean` over every
   compiled module and `tools/nscan_ext_xf.lean` over the external references they name.
9. Manifest check (`scripts/mcheck.py`): the inputs of the export against the 178 manifests.

## Figures

- Modules: 124,634 (124,631 group modules of at most 1,000 leaves each, plus `Zo`, `Main`, `Forms`).
- Build: the modules in 4.54 hours of wall time on one server with 360 hardware threads and 1.4 TiB of memory.
- CPU time: 2,589.5 CPU-hours for export, build and checks (user and system time of every process).
- Checks: the job map, the statements, the module scan (0 violations), the external references (propext,
  Classical.choice, Quot.sound only) and the manifest check (5,033,964 of 5,033,964 inputs equal) all pass;
  details in `results/C1337/summary.txt`.

## Comparing a rebuild with the published hashes

`c1337_oleans.sha256.gz` (a separate file of the record) lists the sha256 of every compiled C1337 module: 124,634 lines,
sorted by path. Each line is `sha256  Autocorr/C1337/[<dir>/]<module>.olean`, with the path relative to
`.lake/build/lib/lean`. To compare:

    cd .lake/build/lib/lean
    zcat /path/to/c1337_oleans.sha256.gz | sha256sum -c --quiet                   # a complete build
    zcat /path/to/c1337_oleans.sha256.gz | sha256sum -c --quiet --ignore-missing  # a partial build

In the independent audit, the rebuilt modules reproduced their hashes except `Forms`, whose olean differed in bytes
while its imports and constants were identical.
