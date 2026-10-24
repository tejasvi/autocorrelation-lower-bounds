"""usage: python3 -I tools/check_axioms.py AXIOMS_OUTPUT INDEX_JSON

Checks the output of Axioms.lean (`#print axioms` for C64NData.mainStatement, mainStatementEss and constStatement): each of the
three theorems must depend on exactly propext, Classical.choice, Quot.sound and one native_decide auxiliary axiom
`C64NData.<T>._native.native_decide.ax_1_1` for T = globOK and for T = <m>.ok, m running over every data module named in
INDEX_JSON (the merged index written by tools/assemble.sh), and on nothing else. Prints the counts; exits 1 on any mismatch."""
import json, re, sys

text = open(sys.argv[1]).read()
idx = json.load(open(sys.argv[2]))
mods = set()
for a in idx:
    mods.add(a["name"])
    for sb in a["subs"]:
        mods.add(sb["name"])
want = {"C64NData.globOK._native.native_decide.ax_1_1"} | {f"C64NData.{m}.ok._native.native_decide.ax_1_1" for m in mods}
std = {"propext", "Classical.choice", "Quot.sound"}
blocks = re.findall(r"'(C64NData\.[A-Za-z]+)' depends on axioms: \[([^\]]*)\]", text)
names = [b[0] for b in blocks]
ok = names == ["C64NData.mainStatement", "C64NData.mainStatementEss", "C64NData.constStatement"]
print("theorems", names)
for name, body in blocks:
    ax = [a.strip() for a in re.sub(r"\s+", " ", body).split(",") if a.strip()]
    s = set(ax)
    good = len(ax) == len(s) and std <= s and s - std == want
    ok = ok and good
    print(f"{name}: {len(ax)} axioms = {len(s & std)} standard + {len(s - std)} native_decide auxiliaries; "
          f"missing {len(want - s)}, other {len(s - std - want)}, duplicates {len(ax) - len(s)}: {'OK' if good else 'MISMATCH'}")
print("data modules in the index:", len(mods))
sys.exit(0 if ok else 1)
