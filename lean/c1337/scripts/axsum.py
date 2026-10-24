"""axsum.py AXIOMS_RAW: summary of `#print axioms` for the three theorems: first line the combined verdict, then one line
per theorem (std = propext, Classical.choice, Quot.sound; native = *._native.native_decide.ax_1_1; other = anything else)."""
import sys, re
s = open(sys.argv[1]).read()
rows = []
for part in s.split("'Autocorr")[1:]:
    name = "Autocorr" + part.split("'")[0]
    body = part.split("[", 1)[1].split("]")[0] if "[" in part else ""
    axs = [a.strip() for a in body.replace("\n", " ").split(",") if a.strip()]
    std = [a for a in axs if a in ("propext", "Classical.choice", "Quot.sound")]
    nat = [a for a in axs if a.endswith("._native.native_decide.ax_1_1")]
    oth = [a for a in axs if a not in std and a not in nat]
    rows.append((name, len(axs), len(std), len(nat), oth, any(a.endswith(".rootOK._native.native_decide.ax_1_1") for a in nat)))
okv = len(rows) == 3 and all(r[2] == 3 and not r[4] and r[5] for r in rows)
print(("AXIOMS OK" if okv else "AXIOMS CHECK") + f": {len(rows)} theorems; " + "; ".join(f"std {r[2]} native {r[3]} other {len(r[4])}" for r in rows))
for r in rows:
    print(r[0], "axioms", r[1], "std", r[2], "native", r[3], "(incl. rootOK)" if r[5] else "(no rootOK)", "other", r[4][:5])
sys.exit(0 if okv else 1)
