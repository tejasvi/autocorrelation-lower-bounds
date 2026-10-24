#!/usr/bin/env python3
"""Two-level assembly for a nested certificate exported in module mode (statements and proofs exactly those of
gen_main_nest.py, moved so that no file holds the subtree theorems of all arcs).
  C64NData/Hgn.lean        imports C64.Check.SoundMirror (with --mirror; else SoundNMain) and C64NData.Glob;
                           theorem hgn : GlobNOK glob (the only copy).
  C64NData/R{i:04d}.lean   one per arc: imports Hgn, the arc module A{i:04d} and all of the arc's subtree modules; the
                           subtree statements {S}.sub (children first, checkSubN_ok + extSub_of), {A}.ext (arcExt_of;
                           E arcs: trivial) and {A}.res : checkArcN glob {A}.arc = true ∧ ArcExt glob {A}.arc.
                           The R modules are independent of each other (compile in parallel).
  C64NData/Main.lean       imports Hgn and all R modules: AllOKN, the groups of 100 (from the {A}.res), arcs, arcs_ok and,
                           unless --no-main, the cover check (decide +kernel), tau_val and the three statements.
Input: OUTDIR/C64NData/index.json, the merged index of the arcs (sorted by "arc"; module names from the exporter).
r2 = r + set_option maxHeartbeats 0 in Hgn, R and Main (the extList rfl of large arcs exceeds 200000).
Usage: gen_main_nest_r2.py OUTDIR [--mirror] [--no-main]"""
import json, os, sys

out = sys.argv[1]; nomain = "--no-main" in sys.argv; mirror = "--mirror" in sys.argv
d = os.path.join(out, "C64NData")
idx = sorted(json.load(open(os.path.join(d, "index.json"))), key=lambda a: a["arc"])
arcnums = [a["arc"] for a in idx]
assert len(arcnums) == len(set(arcnums)), "an arc occurs twice in the index"
names = [a["name"] for a in idx]
subnames = [sb["name"] for a in idx for sb in a["subs"]]
assert len(set(names + subnames)) == len(names) + len(subnames), "a module name occurs twice"
HDR = ["", "set_option maxRecDepth 100000", "set_option maxHeartbeats 0", "", "open C64Chk", "", "namespace C64NData", ""]


def ext_proof(kids):
    """the hypothesis `∀ c ∈ L, SubOK …` of extSub_of / arcExt_of"""
    if not kids:
        return "(by intro c hc; simp at hc)"
    pat = " | ".join(["rfl"] * len(kids))
    alts = "\n".join(f"    · exact {k}.sub" for k in kids)
    return (f"(by\n    intro c hc\n    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc\n"
            f"    rcases hc with {pat}\n{alts})")


open(os.path.join(d, "Hgn.lean"), "w").write(
    ("import C64.Check.SoundMirror" if mirror else "import C64.Check.SoundNMain") + "\nimport C64NData.Glob\n" +
    "\n".join(HDR) + "\ntheorem hgn : GlobNOK glob := (checkGlobN_ok globOK).1\n\nend C64NData\n")
rnames = []
for a in idx:
    A = a["name"]; R = f"R{a['arc']:04d}"; rnames.append(R)
    subs = {sb["name"]: sb for sb in a["subs"]}
    L = ["import C64NData.Hgn", f"import C64NData.{A}"] + [f"import C64NData.{sb['name']}" for sb in a["subs"]] + HDR
    for sb in a["subs"]:                       # children before parents: subs are numbered in creation order
        Lk = "[" + ", ".join(f"({subs[k]['tubes']}, {subs[k]['boxes']})" for k in sb["kids"]) + "]"
        L.append(f"theorem {sb['name']}.sub : SubOK glob {sb['args']} :=\n"
                 f"  checkSubN_ok hgn rfl {sb['name']}.ok (extSub_of (L := {Lk}) rfl {ext_proof(sb['kids'])})\n")
    if a["type"] == "E":
        L.append(f"theorem {A}.ext : ArcExt glob {A}.arc := trivial\n")
    else:
        Lk = "[" + ", ".join(f"({subs[k]['tubes']}, {subs[k]['boxes']})" for k in a["kids"]) + "]"
        L.append(f"theorem {A}.ext : ArcExt glob {A}.arc :=\n  arcExt_of (L := {Lk}) rfl {ext_proof(a['kids'])}\n")
    L.append(f"theorem {A}.res : checkArcN glob {A}.arc = true ∧ ArcExt glob {A}.arc := ⟨{A}.ok, {A}.ext⟩\n")
    L.append("end C64NData")
    open(os.path.join(d, f"{R}.lean"), "w").write("\n".join(L) + "\n")

M = ["import C64NData.Hgn"] + [f"import C64NData.{R}" for R in rnames] + HDR
M += ["/-- Every arc of the list passes the checker, with its ext facts. -/",
      "def AllOKN (gn : GlobN) : List ArcN → Prop", "  | [] => True",
      "  | a :: as => (checkArcN gn a = true ∧ ArcExt gn a) ∧ AllOKN gn as", "",
      "theorem AllOKN.mem {gn : GlobN} : ∀ {l : List ArcN}, AllOKN gn l → ∀ a ∈ l, checkArcN gn a = true ∧ ArcExt gn a",
      "  | [], _, a, ha => by simp at ha",
      "  | b :: l, h, a, ha => by",
      "    simp only [List.mem_cons] at ha",
      "    rcases ha with rfl | ha",
      "    · exact h.1",
      "    · exact AllOKN.mem h.2 a ha", "",
      "theorem AllOKN.append {gn : GlobN} : ∀ {l₁ l₂ : List ArcN}, AllOKN gn l₁ → AllOKN gn l₂ → AllOKN gn (l₁ ++ l₂)",
      "  | [], _, _, h₂ => h₂", "  | _ :: _, _, h₁, h₂ => ⟨h₁.1, AllOKN.append h₁.2 h₂⟩", ""]
G = 100
groups = [names[k:k + G] for k in range(0, len(names), G)]
for gi, grp in enumerate(groups):
    M.append(f"def arcs{gi} : List ArcN := [" + ", ".join(f"{n}.arc" for n in grp) + "]")
    M.append(f"theorem ok{gi} : AllOKN glob arcs{gi} := ⟨" + ", ".join(f"{n}.res" for n in grp) + ", trivial⟩\n")
lst = f"arcs{len(groups) - 1}"
for gi in range(len(groups) - 2, -1, -1):
    lst = f"arcs{gi} ++ ({lst})"
M.append(f"/-- The arcs of the certificate, in order of `s₀`. -/\ndef arcs : List ArcN := {lst}\n")
okterm = f"ok{len(groups) - 1}"
for gi in range(len(groups) - 2, -1, -1):
    okterm = f"AllOKN.append ok{gi} ({okterm})"
M.append(f"theorem arcs_ok : AllOKN glob arcs := {okterm}\n")
if not nomain:
    cover = "coverHalfOK" if mirror else "coverOK"
    stmt = "mainStatementN_mirror_of" if mirror else "mainStatementN_of"
    M += [f"theorem cover_ok : {cover} glob.g 0 (arcs.map fun a => (a.s0, a.s1)) = true := by decide +kernel", "",
          "theorem tau_val : glob.g.tau.val = 1 / 4 := by norm_num [glob, Q.val]", "",
          "/-- The main theorem: `ess sup (f ⋆ f) > (4/3) (∫ f)²`. -/",
          "theorem mainStatement : C64.MainStatement :=",
          f"  {stmt} tau_val globOK cover_ok (AllOKN.mem arcs_ok)", "",
          "theorem mainStatementEss : C64.MainStatementEss := mainStatementEss_of mainStatement", "",
          "/-- `C₃ ≥ C₃' ≥ 4/3`. -/",
          "theorem constStatement : C64.ConstStatement := constStatement_of mainStatement", ""]
M.append("end C64NData")
open(os.path.join(d, "Main.lean"), "w").write("\n".join(M) + "\n")
open(os.path.join(out, "r_modules.txt"), "w").write("\n".join(f"{R} {1 + len(a['subs'])}" for R, a in zip(rnames, idx)) + "\n")
print("wrote Hgn,", len(rnames), "R modules (", len(subnames), "subtree theorems ), Main; groups", len(groups))
