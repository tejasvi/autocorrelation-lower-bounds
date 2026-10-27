#!/usr/bin/env python3
"""check_k_vs_n_v3.py KDIR NDIR: the K assembly sources (gen_main_nest_k_v3.py output in KDIR/C64NData) state exactly what
the native assembly sources (gen_main_nest_r2.py output from the same index, NDIR/C64NData) state. An R<arc> import of the
file holding <M>.okK (from KDIR/C64NData/okk_in.json) is mapped back to import C64NData.<M>; the map must send every module
to itself or to a C64NData.KD_<M>_<k> file. Undoes the K substitutions in every K file (Hgn, R*, Main) and requires byte
equality with the native file:
  (C64KChk.checkSubN_of_K X.okK) -> X.ok;  (C64KChk.checkArcN_of_K X.okK) -> X.ok;  (C64KChk.checkGlobN_of_K globOKK) -> globOK;
  Hgn: drops 'import C64K.KNestSim' and the globOKK theorem (its statement is printed for review);
  Main: 'noncomputable def arcs<g> : List ArcN :=' and 'noncomputable def arcs : List ArcN :=' -> 'def ...' (a noncomputable
  prefix anywhere else still differs). Exit 0 only if all match."""
import json, os, re, sys
kd, nd = (os.path.join(x, "C64NData") for x in sys.argv[1:3])
okp = os.path.join(kd, "okk_in.json")
okk_in = json.load(open(okp)) if os.path.exists(okp) else {}
badmap = [m for m, f in okk_in.items() if f != f"C64NData.{m}" and not re.fullmatch(rf"C64NData\.KD_{re.escape(m)}_\d+", f)]
if badmap:
    print("okk_in maps modules to unexpected files:", badmap[:10]); sys.exit(1)
back = {f: f"C64NData.{m}" for m, f in okk_in.items()}
files = sorted(f for f in os.listdir(kd) if re.fullmatch(r"(Hgn|Main|R\d{4})\.lean", f))
bad = []
for f in files:
    k = open(os.path.join(kd, f)).read()
    k = re.sub(r"\(C64KChk\.checkSubN_of_K ([A-Za-z0-9_]+)\.okK\)", r"\1.ok", k)
    k = re.sub(r"\(C64KChk\.checkArcN_of_K ([A-Za-z0-9_]+)\.okK\)", r"\1.ok", k)
    k = k.replace("(C64KChk.checkGlobN_of_K globOKK)", "globOK")
    k = "\n".join((("import " + back[l[7:]]) if l.startswith("import ") and l[7:] in back else l) for l in k.split("\n"))
    if f == "Main.lean":
        k = re.sub(r"^noncomputable def (arcs\d*) : List ArcN :=", r"def \1 : List ArcN :=", k, flags=re.M)
    if f == "Hgn.lean":
        m = re.search(r"\ntheorem globOKK : (.*?) := by decide \+kernel\n", k)
        print("Hgn: globOKK statement:", m.group(1) if m else "MISSING")
        k = k.replace("import C64K.KNestSim\n", "", 1)
        k = re.sub(r"\ntheorem globOKK : .*? := by decide \+kernel\n", "", k, count=1)
    n = open(os.path.join(nd, f)).read() if os.path.exists(os.path.join(nd, f)) else None
    if k != n:
        bad.append(f)
nfiles = len(set(f for f in os.listdir(nd) if re.fullmatch(r"(Hgn|Main|R\d{4})\.lean", f)))
print(f"compared {len(files)} K files with {nfiles} N files: {len(bad)} differ {bad[:10]}")
sys.exit(0 if not bad and len(files) == nfiles else 1)
