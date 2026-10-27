"""usage: python3 -I tools/hints_from_sources_k.py EXPORT_DIR NLOGS_DIR OUT_DIR

Builds the hint-archive entry of one part from the part's export (EXPORT_DIR = the OUT/P<p> written by
gen_nest_data_k_v2.py k: C64NData/*.lean, C64NData/manifest_<p>.json) and the build logs of the part's native data modules
(NLOGS_DIR/<M>.log, ending in "OK <ms>"). Writes into OUT_DIR:
  <M>.hb       for every module with W leaves: one line `HB <path> <step> <hex>` per step of every hinted segment, read
               from the segment's hint literals (`theorem ks<u>_<i>h : ... (C64KChk.segFT C64NData.glob J [C64KChk.hb 0x<h_J>,
               ...]) := by`; <path> from the comment `-- W leaf <path>: ...` before `theorem kh<u>`, without spaces), then one
               line `HBFAIL - - search` per failed hint search counted in the manifest (field hint_fail; positions are not
               recorded). An unhinted segment has no literals and gives no lines; given these files, the generator again makes
               exactly the segments hinted whose hints are all present, so the sources come out the same.
  ntimes.tsv   <module> TAB <ms> for every module of the manifest: the first "OK <digits>" of NLOGS_DIR/<M>.log (what the
               generator's --ntimes reads), or "-" if there is none.
Prints the totals."""
import glob, json, os, re, sys

exp, nlogs, out = sys.argv[1:4]
src = os.path.join(exp, "C64NData")
os.makedirs(out, exist_ok=True)
files = sorted(f for f in os.listdir(src) if f.endswith(".lean") and f != "Glob.lean")
mod_of = lambda f: re.fullmatch(r"KD_(.+)_\d+\.lean", f).group(1) if f.startswith("KD_") else f[:-5]
wl = re.compile(r"^-- W leaf (\[[0-9, ]*\]): ")
kh = re.compile(r"^theorem kh(\d+) : ")
seg = re.compile(r"^theorem ks(\d+)_(\d+)h : ")
lit = re.compile(r"C64KChk\.hb 0x([0-9a-f]+)")
segft = "C64KChk.segFT C64NData.glob "
per = {}
for f in files:
    d = per.setdefault(mod_of(f), {"key": {}, "segs": []})
    pend = None
    for line in open(os.path.join(src, f), encoding="utf-8"):
        w = wl.match(line)
        if w:
            pend = w.group(1).replace(" ", "")
            continue
        k = kh.match(line)
        if k and pend is not None:
            d["key"][int(k.group(1))] = pend
            pend = None
            continue
        s = seg.match(line)
        if s:
            i = line.index(segft) + len(segft)
            J = int(line[i:line.index(" ", i)])
            d["segs"].append((int(s.group(1)), int(s.group(2)), J, lit.findall(line[i:])))
man = glob.glob(os.path.join(src, "manifest_*.json"))
if len(man) != 1:
    sys.exit(f"expected one manifest in {src}, found {len(man)}")
manifest = json.load(open(man[0]))
nh = nf = 0
for m in sorted(set(per) | set(manifest)):
    lines = []
    d = per.get(m, {"key": {}, "segs": []})
    for u, i, J, hs in sorted(d["segs"]):
        lines += [f"HB {d['key'][u]} {J + k} {h}\n" for k, h in enumerate(hs)]
    k = manifest.get(m, {}).get("hint_fail", 0)
    lines += ["HBFAIL - - search\n"] * k
    nh += len(lines) - k
    nf += k
    if lines:
        with open(os.path.join(out, m + ".hb"), "w") as fh:
            fh.write("".join(lines))
rows = []
for m in sorted(manifest):
    p = os.path.join(nlogs, m + ".log")
    mm = re.search(r"OK (\d+)", open(p).read()) if os.path.exists(p) else None
    rows.append(f"{m}\t{mm.group(1) if mm else '-'}\n")
with open(os.path.join(out, "ntimes.tsv"), "w") as fh:
    fh.write("".join(rows))
print(f"modules {len(manifest)}, hint lines {nh}, HBFAIL lines {nf}, ntimes rows {len(rows)}, "
      f"without an OK time {sum(1 for r in rows if r.endswith(chr(9) + '-' + chr(10)))}")
