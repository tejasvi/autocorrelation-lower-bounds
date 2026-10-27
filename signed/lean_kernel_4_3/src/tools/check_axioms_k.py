"""usage: python3 -I tools/check_axioms_k.py AXIOMS_OUTPUT

Checks the output of Axioms.lean (`#print axioms` for C64NData.constStatement, mainStatement and mainStatementEss, in this
order): each of the three theorems must depend on exactly propext, Classical.choice and Quot.sound, each once, and on
nothing else (no sorryAx, no native_decide auxiliary axiom, no other axiom). Every theorem the three depend on is covered,
since `#print axioms` follows all dependencies. Prints one line per theorem; exits 1 on any mismatch."""
import re, sys

text = open(sys.argv[1]).read()
want_names = ["C64NData.constStatement", "C64NData.mainStatement", "C64NData.mainStatementEss"]
std = ["Classical.choice", "Quot.sound", "propext"]
blocks = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text)
names = [b[0] for b in blocks]
ok = names == want_names
print("theorems", names, "OK" if ok else f"MISMATCH (expected {want_names})")
for name, body in blocks:
    ax = [a.strip() for a in re.sub(r"\s+", " ", body).split(",") if a.strip()]
    good = sorted(ax) == std
    ok = ok and good
    print(f"{name}: {len(ax)} axioms {ax}: {'OK' if good else 'NOT EXACTLY propext, Classical.choice, Quot.sound'}")
for bad in ("sorryAx", "native_decide", "does not depend on any axioms"):
    if bad in text:
        ok = False
        print("found:", bad)
sys.exit(0 if ok else 1)
