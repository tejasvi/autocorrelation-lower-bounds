"""ns_rename.py SRC_ROOT DST_ROOT [--reverse]: namespaced copy of the audited v2 K39 library (hedge for the K1337 tail).
Forward: module prefix AutocorrK39 -> AutocorrK39v2 (paths and imports) and namespace AutocorrK -> AutocorrK2 (every
whole-word occurrence), nothing else. --reverse undoes it. The forward copy of audit_v2/src must reverse to byte-identical
sources (checked by the caller with diff -r). Shared Autocorr.* / AutocorrCert.* names are untouched."""
import sys, os, re
src, dst = sys.argv[1], sys.argv[2]
rev = "--reverse" in sys.argv
for root, _, files in os.walk(src):
    for f in files:
        if not f.endswith(".lean"):
            continue
        p = os.path.join(root, f)
        rel = os.path.relpath(p, src)
        t = open(p).read()
        if rev:
            t2 = re.sub(r"\bAutocorrK39v2\b", "AutocorrK39", t)
            t2 = re.sub(r"\bAutocorrK2\b", "AutocorrK", t2)
            rel2 = re.sub(r"^AutocorrK39v2(?=/|$)", "AutocorrK39", rel)
        else:
            assert not re.search(r"\bAutocorrK2\b|\bAutocorrK39v2\b", t), f"{rel} already contains a renamed token"
            t2 = re.sub(r"\bAutocorrK39\b", "AutocorrK39v2", t)
            t2 = re.sub(r"\bAutocorrK\b", "AutocorrK2", t2)
            rel2 = re.sub(r"^AutocorrK39(?=/|$)", "AutocorrK39v2", rel)
        q = os.path.join(dst, rel2)
        os.makedirs(os.path.dirname(q), exist_ok=True)
        open(q, "w").write(t2)
print("done")
