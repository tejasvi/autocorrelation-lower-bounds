# Search program for the bound V₃₉ ≥ 1337/1000

These files are the search programs of the run behind the bound `V_39 ≥ 1337/1000` (Section 4 of the paper).

- `bnbtree39sdp.py` loads `bnbtree39f_4702b857.py` from this directory and changes one thing, the model that closes a
  node. If the linear program does not close a node and its value is at least λ − 0.008 (`sdp_gap`), the program solves
  Shor's semidefinite relaxation of the region with Clarabel: the equality rows of the linear program and those of its
  inequality rows that are nearly active at its solution, and the condition that the matrix `[[1, pᵀ], [p, Z]]` of the
  bin masses and their products be positive semidefinite. If the value reaches λ, the program combines the multipliers
  of the rows with one square cut for each eigenvector of the dual matrix whose eigenvalue exceeds 10⁻⁷ times the
  largest; the cut is the square of the linear form whose integer coefficients are the eigenvector scaled to maximum
  norm 2²⁰ and rounded. The leaf is written as a D record only if this dual vector passes the floating-point check of
  the base program; otherwise the node is split. These square cuts never enter the linear programs. Their keys
  (`docs/CERT_FORMAT.md`, section 4) can involve all 39 bins.
- `bnbtree39f_4702b857.py` is the search program of the certificate for `V_39 ≥ 267/200`; `search/bnbtree39f.py` is the
  same file. `bnbtree39sdp.py` keeps its command line, files and records.
- `opts_init.json` holds the options of the run, which `init` stores in the run directory; `requirements.txt` lists the
  package versions of the run.

The comments and docstrings differ from the files of the run in a few places, and the code is the same: the Python
syntax trees agree once docstrings are removed. In `bnbtree39sdp.py` one comment and the module docstring changed; in
`bnbtree39f_4702b857.py` three comments and one docstring. The files of the run had these SHA-256 hashes:

    9dd7a266b449de228137be56093ff25fbf14d54edd2a2cdb5887d160a2e300b9  bnbtree39sdp.py
    4702b85723f1c43fdc850c434d8c5511454725662383816f4e08c9b927e9427b  bnbtree39f_4702b857.py

## Running the search

The search needs Python 3 with `numpy`, `scipy`, `highspy` and `clarabel` (versions in `requirements.txt`). From the
root of the repository, on one machine:

    PYTHONPATH=checker python3 search/sdp/bnbtree39sdp.py init run1337 39 1337/1000 --depth 9 \
        --opts "$(cat search/sdp/opts_init.json)"
    PYTHONPATH=checker python3 search/sdp/bnbtree39sdp.py work run1337 --workers 64 --max-nodes 500
    python3 -I checker/verify_tree.py run1337 --workers 64 --expect-n 39 --expect-lam 1337/1000

`init` expands the tree to depth 9 and queues the open nodes as jobs, and `work` processes the queue. A job that reaches
the node budget queues its open nodes as new jobs, and a worker reads its budget from the file `max_nodes.ctl` in the
run directory if that file exists. For the run behind the paper, a coordinator moved the job files between up to 179
servers; it depends on our environment and is not included.

With `16 5/4 --depth 4`, one worker and `--expect-n 16 --expect-lam 5/4` instead, the same commands give a small
certificate in about two minutes, which the first checker accepts (1,259 leaves).
