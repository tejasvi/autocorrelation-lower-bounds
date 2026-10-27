#!/usr/bin/env python3
"""kbuild_raw_v1.py: build the Lean modules of one project with plain `lean -o`, without lake (which needs git to check
packages). Standard library only.
usage: kbuild_raw_v1.py ROOT OUTLIB JOBS LEAN_PATH_EXTRA TARGET...
  ROOT            project root (holds C64/, C64Core/, C64K/, C64KX/, the root .lean files)
  OUTLIB          output dir for oleans/ileans (ROOT/.lake/build/lib/lean)
  JOBS            parallel lean processes
  LEAN_PATH_EXTRA colon list of prebuilt lib dirs (the packages' .lake/build/lib/lean), searched after OUTLIB
  TARGET          module names; every project-local import is built first (local = its file exists under ROOT)
Each module: lean <lake's leanOptions as -D> --root=ROOT -o OUTLIB/<M>.olean -i OUTLIB/<M>.ilean ROOT/<M>.lean, run with
LEAN_PATH=OUTLIB:LEAN_PATH_EXTRA. Prints one line per module (rc, wall s, user s, peak RSS) and exits 1 on the first failure.
"""
import os, re, resource, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor, FIRST_COMPLETED, wait

OPTS = ["-Dpp.unicode.fun=true", "-DrelaxedAutoImplicit=false", "-DautoImplicit=false",
        "-Dweak.linter.style.header=false", "-DElab.async=false"]
IMP = re.compile(r"^\s*import\s+([A-Za-z0-9_.']+)")

def src(root, m):
    return os.path.join(root, *m.split(".")) + ".lean"

def imports(path):
    out, in_block = [], False
    for line in open(path, encoding="utf-8"):
        s = line.strip()
        if in_block:
            if "-/" in s:
                in_block = False
            continue
        if s.startswith("/-"):
            if "-/" not in s[2:]:
                in_block = True
            continue
        if s == "" or s.startswith("--"):
            continue
        mm = IMP.match(line)
        if mm:
            out.append(mm.group(1))
            continue
        if s.startswith("prelude"):
            continue
        break
    return out

def main():
    root, outlib, jobs, extra = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
    targets = sys.argv[5:]
    deps, todo = {}, list(targets)
    while todo:
        m = todo.pop()
        if m in deps:
            continue
        p = src(root, m)
        if not os.path.isfile(p):
            sys.exit(f"no source for target/local module {m}: {p}")
        loc = [i for i in imports(p) if os.path.isfile(src(root, i))]
        deps[m] = loc
        todo.extend(loc)
    lean = os.environ.get("LEAN", "lean")
    env = dict(os.environ, LEAN_PATH=outlib + (":" + extra if extra else ""))
    done, running, failed = set(), {}, None
    pending = sorted(deps)
    print(f"modules to build: {len(deps)}", flush=True)
    def run(m):
        o = os.path.join(outlib, *m.split(".")) + ".olean"
        os.makedirs(os.path.dirname(o), exist_ok=True)
        cmd = [lean] + OPTS + [f"--root={root}", "-o", o, "-i", o[:-6] + ".ilean", src(root, m)]
        t0 = time.time()
        r0 = resource.getrusage(resource.RUSAGE_CHILDREN)
        pr = subprocess.run(cmd, env=env, cwd=root, capture_output=True, text=True)
        r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
        log = os.path.join(outlib, "..", "..", "rawlogs", m + ".log")
        os.makedirs(os.path.dirname(log), exist_ok=True)
        open(log, "w").write(" ".join(cmd) + "\n" + pr.stdout + pr.stderr)
        return m, pr.returncode, time.time() - t0, r1.ru_utime - r0.ru_utime, r1.ru_maxrss, (pr.stdout + pr.stderr)[-1500:]
    with ThreadPoolExecutor(max_workers=jobs) as ex:
        while pending or running:
            ready = [m for m in pending if all(d in done for d in deps[m])] if failed is None else []
            for m in ready:
                if len(running) >= jobs:
                    break
                pending.remove(m)
                running[ex.submit(run, m)] = m
            if not running:
                break
            fin, _ = wait(list(running), return_when=FIRST_COMPLETED)
            for f in fin:
                m = running.pop(f)
                m, rc, wall, user, rss, tail = f.result()
                print(f"{'OK  ' if rc == 0 else 'FAIL'} {m} rc {rc} wall {wall:.1f} s user~{user:.1f} s maxrss {rss} KB", flush=True)
                if rc == 0:
                    done.add(m)
                else:
                    failed = m
                    print(tail, flush=True)
    if failed or pending:
        print(f"BUILD FAILED at {failed}; not built: {len(pending)}", flush=True)
        sys.exit(1)
    print(f"BUILD OK {len(done)} modules", flush=True)

if __name__ == "__main__":
    main()
