# Notes on the runs reported in the paper

The first section below keeps the details of the runs and audits that Appendix A of the paper summarizes. The other
sections record settings and incidents of the runs that the paper reports; none of them can make a checker accept a
leaf whose exact bound is below lam.

## Runs and audits summarized in Appendix A of the paper

Up to version 12, Appendix A of the paper gave the following details of the runs and audits in full. From version 13
on, the paper summarizes them and refers to this file. The text below is that of version 12, with its macros written
out; theorem, section, table and equation numbers refer to version 12 of the paper.

### What each second checker shares with the first checker of the same certificates

| Second checker | Shared with the first checker | Its own |
|---|---|---|
| `iv_verify.py` | no code with the first checker or with the search, although we knew the code of the first checker | all of its code |
| `indep_three_level.py` | the reading of the file, the walk over the tree of leaves, the corner rule for the extremes of Re(conj(y_j) x) over a box and the outline of the winding count, with about fifty short lines in common; it re-implements the ball-based bound for r of the first checker | its enclosures of arcs and tiles, its bounds in t, its coverage test for the leaves and its acceptance test for the pieces of the winding count |
| `indep_nested.py` | nothing imported; 36 lines of at least 25 characters in common, 23 of them verbatim and the others up to the names of variables (the description of the format lists what these lines do); the way it schedules the subtrees of a witness as separate jobs follows the design of `check_nested.py` | its checks of the inequalities: its enclosures of S, S', S'', K_t, the transform of nu and G_nu, its bounds for the extrema over arcs and in t, its bound for r_N, the rest of its winding count, its bounds for the tube conditions and for the rectangles, and its test of the intervals of type E |

### Runs behind Table 1 (the certificate of Theorem 2.2)

| Run | Cost |
|---|---|
| Search (wall time) | 215 min on up to 179 servers (52,123 worker processes), about 112,700 CPU-hours |
| First checker (search logs) | on 178 servers, about 70 min (wall time) |
| Second checker (search logs) | about 12,700 worker-hours |
| Lean check (`native_decide`) | 124,634 modules; about 2,600 CPU-hours on one server for export, build and checks (the modules in 4.5 h) |
| Lean check (kernel only) | 5,164,010 check modules, about 186,600 CPU-hours; assembly in about 2 h on one server |

SHA-256 of `meta.json`: `5fa65703265cba2d10b36d5a4f5669c9e75a51d52de1f18007b62708dc93192f`

- **First checker.** The first checker ran on the logs held by each of the 178 servers, writing one summary file per
  server; a final run of the first checker combined the 178 summary files and checked the partition.
- **Search logs.** After the first checker had accepted the logs of a server, these logs were made read-only, their
  SHA-256 hashes were listed, and they were packed into one tar file per server. These 178 tar files, with the file
  `meta.json` of the run, which fixes n, lam and the rows and columns, are the certificate. A later pass read every tar
  file and found the listed hash for each of the 5,033,964 job files.
- **Second checker.** It ran after the first checker, on the logs of every server, and each time it confirmed that the
  job files it read have the SHA-256 hashes of that list. A separate script combined the per-server results, with the
  identification of the job files and the partition check of item (c) in Section 4.
- **Coverage.** For the run of the first checker and for its run on the certificate for V_36 >= 133/100, a separate
  count confirmed that the per-job results cover every job exactly once.
- **Lean input.** A variant of the first checker, with identical acceptance logic, also writes the dual vectors that it
  accepts. It is in the repository and in the archive of the certificate for V_36 >= 133/100. The Lean checker read the
  search logs with the dual vectors of the 2,446 leaves without data filled in by this variant; these leaves lie in
  2,412 job files. The 2,412 filled job files are kept with the search logs; their SHA-256 hashes are archived as
  `c1337_filled_jobs.sha256`, and the list of all files that the Lean checker read, with their SHA-256 hashes, as
  `c1337_filled_certificate.sha256.gz`. Any filled certificate that the Lean checker accepts gives the theorem.
- **Lean proof.** The formal theorem states (1.1) with C = 1337/1000 for measurable f: R -> [0, infinity] with lower
  Lebesgue integrals. We also derive in Lean the stronger statement with the essential supremum, and a version for
  measurable f: R -> R that is nonnegative and vanishes outside [-1/4, 1/4], stated with Mathlib's convolution and the
  L-infinity norm on [-1/2, 1/2]. The Lean checker re-implements the constraints of Section 3 and proves them valid. An
  exporter translates the search logs, completed as in the previous item, into Lean source; since the formal theorem
  does not mention the certificate, the exporter need not be trusted. The final theorem of the proof through
  `native_decide` depends on Lean's three standard axioms and on 124,632 further axioms. Each records the result of a
  compiled evaluation: one for each generated module, which checks a group of jobs, and one for the root region. In an
  audit, all 124,634 modules of the Lean proof of Theorem 1.1 were rebuilt with a separate toolchain and compiled
  checker, from our sources, which the audit checked against the list of their SHA-256 hashes
  (`c1337_sources.sha256.gz`). For a pre-registered random sample of 2,493 of the 124,631 modules that check groups of
  jobs, the audit also regenerated the sources from the certificate; they were byte-identical to ours. All rebuilt
  modules except the module of the statements were byte-identical to ours; that module's olean differed in bytes, but
  its imports, constant names and types were identical and its constants passed kernel replay. The audit's compiled
  checker also evaluated every step of the proof that `native_decide` accepts a second time.
- **Kernel-only Lean proof.** The kernel-only proof of Theorem 1.1 checks the segments of the depth-first records of all
  jobs in 5,164,010 generated modules, and 252 group modules and the final modules compose these checks. Six jobs were
  cut into segments differently, by a patch of the exporter, which need not be trusted, and three jobs were checked by
  a second version of the checker and composed in a separate module. Building the check modules took about 186,600
  CPU-hours; the assembly took about two hours on one server. An audit found the three final statements of this proof
  equal to the reviewed statements with lam = 1337/1000 and depending only on `propext`, `Classical.choice` and
  `Quot.sound`.
- **The certificate for V_39 >= 267/200.** Both checkers accepted its search logs, and the first checker also its
  archived form (Section 5), in about 320,000 worker-hours and with smallest bound 1.3350000000004...; a separate
  script confirmed that the two have the same tree. The Lean checker read the logs, completed as above; the list of
  these files, with their SHA-256 hashes, is archived as `c39t_filled_certificate.sha256.gz`.
- **The certificate for V_36 >= 133/100.** For this certificate we ran the variant of the first checker, which also
  wrote, for the Lean checker, a certificate in which every leaf stores its dual vector. That certificate (about 2.1
  terabytes) is not archived, but the list of its files with their SHA-256 hashes is
  (`c36t_filled_certificate.sha256.gz`). The Lean check of that certificate through `native_decide` used 490,501
  modules and about 2,200 CPU-hours. The kernel-only check used 2,274,566 generated modules: 78 check modules for the
  620 jobs at the top of the tree; 2,274,486 shard modules for the 6,372 subtrees below them, which were split into 202
  shards; one module of shared parameters; and a final assembly module that imports all the others and proves the
  theorems. The shard modules were built in about 4.7 hours on 202 servers, and the final module took 50 minutes and
  2.6 TiB of memory on one server. Printing the axioms of the theorems would need one process that loads all these
  modules. Instead, a scan of every compiled module found no declared axiom and no reference to `sorryAx` or to native
  evaluation, and the constants used from outside these modules depend only on Lean's three standard axioms. In an
  audit, this scan was repeated with separate code, and the module of shared parameters, the 78 check modules and all
  2,274,486 shard modules were rebuilt from the same inputs, with results byte-identical to ours. The final assembly
  module, which imports all the others, was not rebuilt but was replayed in Lean's kernel. This rebuild used about
  54,000 CPU-hours of Lean user time, on up to 20 servers that each ran 178 Lean processes, in about one day.
- **The certificate for V_28 >= 131/100.** We ran checker (c) of Table 3 on the jobs in parallel on 32 machines and
  combined the per-job results, a step that includes the partition check.
- **The nested certificate of Table 4.** Its archive `one_sided_tau1_4_parts.tar` has the SHA-256 hash
  `311796500af5dcdf61c36b2d9aa9e9f752b43afccaa49ff830c39be2ef919d87`. The check by `check_nested.py` took 3 h 27 min of
  wall-clock time on two servers with 384 threads and four with 96 threads, and the check by `indep_nested.py` took
  8 h 45 min on three servers with 384 threads.
- **The certificate for tau = 6/25.** Both checkers of multi-level certificates accepted it in 38 min and 13 min with
  382 workers each on a server with 384 threads. Its file `one_sided_tau6_25.json.gz` has the SHA-256 hash
  `2a76bd9b523ac8991bf99c5a8a00e9eefca84b867dc2a1b558cfa2d3eaa686d8`.

### Audits of the Lean proofs of the signed bounds

For the proof of C_3 >= C_3' >= 25/19 through `native_decide`, every module was rebuilt from scratch, with the data
regenerated from the certificate, and re-checked in Lean's kernel. With the auxiliary axioms taken as given, its
exported proof is accepted by Lean's kernel (`leanchecker`) and by two other kernel implementations, nanoda and
lean4lean, and a corrupted export is rejected by all three. For the kernel-only proof of the same bound only a sample
was re-checked: a seeded random 10% of the piece modules was checked again by Lean's kernel, while the other piece
modules, and the check that the three final theorems depend only on the standard axioms, rest on our own build. For
the bound 30/23, the exported proof through `native_decide` is accepted by `leanchecker`, nanoda and lean4lean, and the
15,663 modules of the kernel-only proof were rebuilt from regenerated sources on other machines. For the proof of
C_3 >= C_3' >= 4/3 through `native_decide`, in an independent rebuild from the certificate, every compiled file was
reproduced byte for byte and every module was re-checked in Lean's kernel; other kernel implementations are discussed
under "Partial checks" below. For the kernel-only proof of C_3 >= C_3' >= 4/3, an audit confirmed that the three
theorems of this proof state the same as those of the proof by `native_decide` and use no axioms beyond the standard
ones. In this audit the library and all assembly modules were rebuilt with identical bytes and replayed in Lean's
kernel, and for every data module the audit checked the hash, the absence of declared axioms and of native code, and
that the module's tree of nodes equals that of the proof by `native_decide`. The proofs in the data modules were
checked again only in samples. Twelve parts were rebuilt with identical bytes. Lean's kernel replayed 184 sampled
files; the 102 files that were compiled again after reaching a time limit, together with the 102 modules built on
them; and 30 of the 426 files whose first builds left no logs, chosen at random. The other data modules rest on the
kernel checks of our build.

Lean proofs of the signed bounds: generated modules and build times.

| Bound | Checks by | Modules | Build |
|---|---|---|---|
| 4/3 | `native_decide` | 208,803 | about 9,150 CPU-hours (2.25 h on 19 servers with 384 threads each, and 4 h on one more for the assembly) |
| 4/3 | `decide +kernel` | 212,820 | about 313,000 CPU-hours (47 h on up to 89 servers with 176 threads each, and 18 server-hours for the assembly, most of them during the build) |
| 25/19 | `native_decide` | 2,375 | about 124 CPU-hours (27 min on one server) |
| 25/19 | `decide +kernel` | 41,353 | about 13,900 CPU-hours (3.2 h on 12 servers with 384 threads each) |
| 30/23 | `native_decide` | 2,627 | about 133 CPU-hours (77 min on two servers with 140 threads in total) |
| 30/23 | `decide +kernel` | 15,663 | about 11,300 CPU-hours (6.4 h on 24 servers with 96 threads each) |

### Partial checks

For the kernel-only proof of Theorem 1.1, an independent kernel replay covered the whole assembly: the module of
parameters, the 252 group modules and the final modules. The 5,164,004 job modules of the first version of the checker
were kernel-checked by our build, and all of them match the SHA-256 lists of the build. A 2% sample of the job units
(103,602 modules), the five most CPU-heavy modules, the re-segmented ones and those of the second version were rebuilt
independently and are byte-identical; the other job modules rest on the kernel checks of our build. A separate,
reduced audit used a modified copy of the second checker; this copy confirmed the SHA-256 hashes of all job files,
replayed the records, regions and delegations of every job exactly, and confirmed that the jobs partition the region
(2.2). Of the leaves, it certified 6,810,514 listed ones exactly, with the same smallest bound, and re-solved
1,882,155 of them with its own linear programs, given the square constraints that the stored vectors name; all of
these reached lam. The re-solved leaves are a seeded random 2% of the leaves with stored dual vectors together with
the 0.1% with the smallest stored margins. The audit does not certify every leaf; the certification of every leaf
rests on the two checkers of Section 4.2. For the Lean proof of C_3 >= C_3' >= 4/3, the exported forms of a seeded
sample of 20 data modules and of the assembly module of one arc were accepted by `leanchecker`, nanoda and lean4lean;
no other kernel implementation has checked the complete export. For its kernel-only proof, five sampled data modules
were exported; `leanchecker` and nanoda accepted all five, and lean4lean accepted three of them. The assembly module
of one arc was exported with every declaration it depends on; all three kernels accepted it and rejected a corrupted
export. None of the three has checked the complete export. For the kernel-only proof of the bound 30/23, besides
Lean's kernel, nanoda and lean4lean accepted the soundness proof, the lemmas that equate the two versions of the
checker, the global checks and one interval of type E, and nanoda also accepted an interval of type H, whose check is
assembled from piece theorems. The complete export, about 5.7 million constants, was not checked by a second kernel.

### Details that version 13 removed from the paper

- Table 1 of version 12 also had the rows "Jobs (subtrees): 5,033,964", "LP rows (no squares); columns: 17,085; 3,158" (Section 4.1 of the paper
  states these numbers) and "Search logs (the certificate): 5,033,964 job files, 1,880,311,858,658 bytes, in 178 tar
  files".
- Table 4 of version 12 also had the row "Archive of the 2,048 parts: `one_sided_tau1_4_parts.tar`, 25,152,471,040
  bytes".
- Appendix A of version 12 gave the solver versions: both checkers of Theorem 2.2 use HiGHS through highspy 1.15.1, and
  the search program in `search/sdp` calls Clarabel 0.11.1. It also said that `INDEP_SAMPLE.txt` gives the seed string,
  fixed in advance, and the rule by which a pseudorandom generator drew the parts.
- Section 6 of version 12 described the search programs: "The search programs choose the numbers u, v and y_j from
  linear programs on grids of values of t, solved in floating point with HiGHS. They subdivide intervals, squares and
  tile arcs until a ball-arithmetic check of the same kind as in the first checker succeeds, and they take nu_rep from a
  linear program as well." and "The nested certificate was produced by a further search program, which builds the
  trees: where a witness fails on a tile arc, it tries a child with the new tube condition, with at most two tube
  conditions at a node, and where a child fails, it may split the arc of a tube condition in two, at most 8 times in a
  row. The search ran in pieces, each with a budget of 20,000 nodes, and pieces that exceeded it were divided into 16
  smaller pieces, in up to two rounds. The intervals of the lower half are the mirror images of those of the upper half,
  and an assembly program joins the pieces into the certificate and writes its parts."
- Section 4.1 of version 12: the search solves Shor's semidefinite relaxation at a node that the linear program does not close
  when the value of the linear program is at least lam - 0.008.
- Section 4.2 of version 12: at a leaf without data, the first checker adds square constraints from the 20 pairs of blocks whose
  matrices have the most negative smallest eigenvalues below -10^-6, with the eigenvector scaled to maximum norm 1, multiplied by
  2^20 and rounded to integers, for at most 20 rounds; window, McCormick and square constraints found at earlier leaves of the same
  job stay in the linear program until they have carried no dual weight for more than 40 leaves, and the solver stops as soon as the
  objective exceeds lam + 10^-6; the checker rounds the duals for the rows to multiples of 2^-64 and those for the square
  constraints to multiples of 2^-128.
- Appendix A of version 12: the search program of Theorem 2.2 is in `search/sdp` (the search program of the certificate for
  V_39 >= 267/200 with the semidefinite step added); `signed/FORMAT.md` specifies the format of multi-level certificates;
  `signed/nested` also holds `coverage_subsets2.py` and the list `INDEP_SAMPLE.txt` of the 103 parts of an earlier run of
  `indep_nested.py` on a random sample.
- Table 4 of version 12 is Table 4 of version 13 without its archive row and without the row "Tile arcs: in total; with a child:
  506,448,728; 7,993,894". The certificate format and the checkers of Section 6 of version 12 are Appendix B of version 13, and
  the paragraphs "Formal proofs" of its Section 6 are in Appendix A of version 13. Version 13 names the checkers of
  the nested certificate by their roles: the first is `check_nested.py`, the second `indep_nested.py`, and the program that checks
  the coverage by the parts is `coverage_subsets2.py`; the table at the start of this file says what each second checker shares
  with the first and how it was written.
- Table 3 of version 12 (the further certificates) is a sentence in Section 5 of version 13. Its rows: V_39 >= 267/200,
  527,163,006 leaves, square constraints, both checkers of Theorem 2.2; V_36 >= 133/100, 177,077,986 leaves, square
  constraints, both checkers of Theorem 2.2; V_30 >= 33/25, 24,935,952 leaves, square constraints, the checker for
  certificates that store the dual vector of every leaf; V_28 >= 131/100, 15,250,196 leaves, V_24 >= 13/10, 2,801,076
  leaves, and V_20 >= 32/25, 113,761 leaves, no square constraints, the third checker. Its column "Lean kernel alone"
  (yes for V_36, V_28 and V_20) is a sentence in Appendix A of version 13.
- Counts that version 13 of the paper no longer prints: the kernel-only proofs of 25/19, 30/23 and 4/3 have 41,353,
  15,663 and 212,820 generated modules (table above); the kernel-only proof of Theorem 1.1 checks the jobs in 5,164,010
  generated modules (items above); the certificate for V_39 >= 267/200 has 13,678,676 jobs and that for V_36 >= 133/100
  has 2,419,679.

## The certificate of V_39 >= 1337/1000

- **Node budget of the search.** The budget only decides where jobs are cut. It was 50 nodes for the first six and a
  half minutes, then 500, except for about twelve minutes with 100 and then 20, set after a stall of the coordinator was
  misread as the final phase of the run (12 to 25 minutes after the start); 100 from 48 minutes on, except for four
  minutes with 20; and 20 for the last 17 minutes.
- **CPU-hours of the search.** The figure counts busy worker-hours: the number of running jobs integrated over the run,
  with one worker process per vCPU.
- **Servers.** During the search the coordinator restarted spot servers that had been stopped. The logs and queued jobs
  of the 13 servers in one region were moved, whole, to servers in another region; one of them stopped during the move,
  and its logs and queued jobs were moved from a snapshot of its disk, where one job file that had been copied only in
  part was copied again. Those of two other servers that stopped were moved in the same way from snapshots of their
  disks.
- **Root job.** The log of the root job, written by `init`, has no done marker, so the first count of finished jobs was
  one short of the number of job files; the coverage count with the root job included matched (5,033,964 files, no
  duplicates).
- **First checker.** It ran on each server once that server had no jobs left, with no solver options, then once more to
  combine the 178 summary files. Its worker-hours were not recorded. On one server 376 worker processes checked 69,073
  jobs in 32 minutes, and on another 104 worker processes checked 12,048 jobs in 26 minutes. Extrapolated to all jobs,
  these rates give about 14,800 and 18,700 worker-hours (workers times wall-clock time, which includes idle workers at
  the end of each server's run). One server stopped after its check had finished and before the upload of its tar file;
  it was recreated from a snapshot of its disk, and its job files matched their recorded SHA-256 hashes.
- **Tar files.** A pass after the upload read every tar file and found the listed SHA-256 hash for each of the 5,033,964
  job files, with no file missing or extra.
- **Second checker on the logs of the search.** It ran in place on 177 servers after the first checker. It matched the
  job files of each server against the hash list written there after the first checker, both as it read them and after
  its run. The logs of the remaining server, which had stopped, were checked on another machine from its tar file,
  against the same list. Unlike the run on the logs of the search for 267/200, it did not re-certify a sample of the
  leaves with stored dual vectors by its own linear programs: those programs use square cuts for pairs of blocks only,
  and in a test on 40 jobs, taken from one server during the search, they certified only 2 of 16 randomly chosen leaves
  at 1337/1000; at 376 of the 421 leaves of these jobs the stored dual vector relies most on a cut in 39 blocks. This
  change was accepted on condition that every such cut is rebuilt from its integer key as the square of a linear form;
  must-fail tests on a job with a cut in 39 blocks (a doubled coefficient, a negated constant term, a block out of
  range, a wrong tag) were all rejected. Its own linear programs closed the 2,446 leaves without data.
- **Audit.** A separate, reduced audit ran a copy of the second checker whose own linear programs also receive, at a
  selected leaf, the square cuts that its stored dual vector names (each rebuilt from its key). It read the 178 tar
  files and meta.json from the archive on 19 servers of its own, matched the job files of every tar file against its
  hash list, replayed the records, regions and delegations of every job exactly and confirmed the partition. Of the
  leaves, it certified 6,810,514 listed ones exactly (smallest bound 1.3370000100056194) and re-solved 1,882,155 of
  them, a seeded random 2% of the leaves with stored dual vectors and the 0.1% with the smallest stored margins, with
  its own linear programs; all were certified. It does not certify the other 82,863,196 leaves; the certification of
  every leaf rests on the first and second checkers.

## The certificate of V_39 >= 267/200

- **Node budget of the search.** The budget only decides where jobs are cut. It was one node during a fan-out of
  three minutes at the start of the search, then, after about five minutes with the values 125, 31 and 200, mostly 500
  (200 on servers that joined later), and 100 and then 20 near the end.
- **Solver setting, first checker on the logs of the search.** For the 46,627 jobs on two of the servers where the
  linear program of a leaf without data had stalled, the first checker ran HiGHS with a limit of 100,000 simplex
  iterations (`VT_HIGHS_OPTS='{"simplex_iteration_limit": 100000}'`); this limit affects only the search for a dual
  vector.
- **Solver setting, first checker on the archived certificate.** That run used the same limit of 100,000 simplex
  iterations for every job.
- **Lean fill.** The dump verifier that filled the leaves without data for the Lean proof ran two of its jobs with
  `VT_HIGHS_OPTS='{"simplex_strategy": 4}'`, an option of the solver that searches for a dual vector.
- **Archived copies.** During the run of the first checker on the tree-only copies of the logs, the copies on the
  servers were read-only. Their SHA-256 hashes, recorded during the run and again after it, agree with each other and
  with those of the archive, and the results of the run cover exactly these files. The jobs of one server were checked
  on four other servers, and the copies there, hashed after their runs, gave the same hashes.
- **Second checker on the logs of the search.** It read the logs in place on the 487 servers of the search, with 32,954
  worker processes; on every server the set of job files that it read, with their SHA-256 hashes, equals the manifest of
  the run, and a separate script combined its per-server results. As a cross-check, its own linear programs also
  certified a random 2% of the leaves with stored dual vectors and the 0.1% of them with the smallest stored margins.

## The certificate of V_36 >= 133/100

- **Solver setting.** In 37 of the 791 parts of the run of the first checker, HiGHS with its default options stalled;
  for their 298,364 jobs, listed in `ORACLE_OPTS.txt` of the archive, the checker used the same limit of 100,000
  simplex iterations.
- **Regenerated job logs.** Two job logs that a server interruption had left empty were generated again over the same
  regions (`REPAIR.md` in the archive).
- **Lean check.** The 490,501 modules were generated and compiled on 202 servers in about 2,200 CPU-hours; the top
  module took about 20 minutes on one server.

## The certificate of V_30 >= 33/25

- **Solver revision.** Most of its jobs ran an earlier revision of `bnbopt.py` without the HiGHS iteration limit, which
  was added during the run when eight jobs stalled. The certificate format is the same for both.
- **Duplicate jobs.** After a move between servers, two servers occasionally processed the same job. One job per region
  was kept (`keep.txt` in the archive), and the Python checker confirms that the kept jobs partition the region.

## The nested certificate of C_3 >= C_3' >= 4/3

- **Search.** The second phase worked on 59,342 tasks of the upper half of T1, the hard tile arcs that the first phase
  left, each with a budget of 20,000 nodes. Tasks that exceeded it or stalled were divided into 16 equal pieces, in up
  to two rounds; 333 of the 59,342 tasks enter the certificate as such pieces, which gives 65,702 pieces in all. The
  first version of the second phase wrote 61,410 of them and the second 4,292; the second differs only in skipping,
  inside the subtrees of arc splits, attempts that could not succeed there, and writes the same format. The intervals of
  the lower half are the mirror images of those of the upper half, and an assembly program joined all pieces into the
  certificate file and its 2,048 parts. The coarse pass and the first phase ran with an earlier version of the search
  programs: the coarse pass gave 234 intervals of type E, and the first phase, on the 2,224 finer intervals below the
  others, gave 42 more of type E, closed 590 of type H, and left the hard tile arcs of the remaining 1,592 as the tasks
  of the second phase. All versions, with the commands and settings of every step, are in `signed/nested/search/` (see
  its `RUNS.md`).
- **Checks of record.** `check_nested.py` ran through `check_run2.py`, one part at a time with `--subset --deep`,
  Python 3.12.13, python-flint 0.9.0, NPROC = 7 and one thread per process. Two servers with 384 threads ran 40 to 48
  such runs at a time, under a common memory limit of 360 GiB, and four servers with 96 threads ran 12 each; the checks
  took 3 h 27 min in all, about 2,300 CPU-hours, with at most 8.3 GB of memory per run. Every one of the 2,048 runs
  ended with status 0 and `SUBSET: n of n arcs pass`. `coverage_subsets2.py` then checked the 2,048 hashes, the common
  header and the coverage of [0, 1] (`COVERAGE OK`, 2,458 arcs).
- **Second checker on all parts.** On 2026-10-24 `indep_nested.py` (the file in `signed/nested/`, byte for byte) ran on
  all 2,048 parts, each fetched again and checked against the parts' SHA-256 list before its run, with the loop command
  of the README (NPROC = 7), Python 3.12.13 and python-flint 0.9.0, on three servers with 384 threads, 33 parts at a
  time on each. All 2,048 runs ended with status 0 and `SUBSET OK: n arcs pass`; the n add up to 2,458, every arc of the
  certificate. The run took 8 h 45 min and 6,012 CPU-hours (metered). A first start was stopped after about three
  minutes, before any check had finished, because many simultaneous downloads failed; the run then started again from
  the beginning.
- **Second checker, earlier sample.** `indep_nested.py` ran on the 103 parts of `INDEP_SAMPLE.txt`, each run on one part
  with `--subset --deep`, on four servers with 384 threads, two at a time, with 2, 8, 16 or 32 worker processes per run
  depending on the size of the part: 13 parts in 40 minutes and the other 90 in 59 minutes, 1 h 39 min in all. Every run
  ended with status 0 and the line `SUBSET OK: N arcs pass`, with N equal to the count of the run of record of
  `check_nested.py` for the same part, 121 arcs in all. It used 337 CPU-hours (user and system time), about 3.4 times
  the 100 worker-hours of `check_nested.py` on the same parts; that figure, the elapsed time of the runs of record times
  their seven processes, is an upper bound for their CPU time. The factor was 2.0 to 2.5 on the servers where each
  worker process had about one core, and 4.0 on the server that ran two worker processes per core.
- **Replay.** Before the release, the commands of the README for this certificate were run as written on one server with
  8 threads and 30 GiB of memory (Python 3.12.13, python-flint 0.9.0), from a clean copy of `signed/nested/` and the
  archive file, with NPROC = 7 and the loop restricted to parts 228 (the largest), 1413, 1843 and 1970. A swap file of
  32 GiB was added during the run, so that a lack of memory could not end a run of `indep_nested.py`; it was not used,
  and the commands were not changed. The archive check, the extraction and the coverage check of all 2,048 parts passed,
  `check_nested.py` accepted the four parts, and `indep_nested.py` accepted parts 1413, 1843 and 1970. On that server
  `check_nested.py` took 48 minutes on part 228 and 9 minutes on part 1970, and `indep_nested.py` 31 minutes on part
  1970. The run of `indep_nested.py` on part 228 ended after the release of version 9 of the paper: it accepted the
  part (`SUBSET OK: 2 arcs pass`) in 2 h 26 min.
- **Exit status.** Earlier versions of `check_nested.py` ended with status 0 in the `--subset` mode even when an arc
  failed; the version shipped here ends with status 1, and `check_run2.py` also requires the line
  `SUBSET: n of n arcs pass` with equal numbers.

## The certificate of C_3 >= C_3' >= 25/19

- **Low-memory runner.** `signed/checker/check_three_level_lowmem.py` starts the worker processes of the first checker
  so that they do not copy the parsed certificate, and calls the checker unchanged. The 38 minutes of the first checker
  in the README were measured with this runner; the second checker starts its workers itself.
- **Memory.** In both checkers the main process holds the parsed certificate, about 40 GB, and more while parsing.
  The totals were not measured for this certificate. For the certificate below, each checker needed about twice its
  main process with 360 workers (each worker of the first checker added about 64 MB, and the workers of the second
  checker hold all intervals a second time). The intervals here are about twice as large on average, so expect roughly
  80 GB or more for either checker with a few hundred workers. The chunk files of the second checker take about the
  size of the decompressed JSON on disk.

## The certificate of C_3 >= C_3' >= 30/23

- **Memory.** With 360 worker processes each checker used about 43 GB in total. In both checkers the main process holds
  the parsed certificate, about 20 GB (about 25 GB while parsing); each worker of the first checker adds about 64 MB,
  and the workers of the second checker hold all intervals a second time.
