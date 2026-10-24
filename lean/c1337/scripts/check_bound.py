"""check_bound.py MAIN FORMS EXPECTED: the theorem part that tools/merge_top.py would build from the generated Main.lean and
Forms.lean must equal EXPECTED (the reviewed statement proposal, C1337_bound_expected.lean) byte for byte."""
import sys
ns = "Autocorr.C1337"
main, forms, exp = (open(p).read() for p in sys.argv[1:4])
mb = main.split(f"namespace {ns}\n", 1)[1].rsplit(f"end {ns}", 1)[0]
fb = forms.split(f"namespace {ns}\n", 1)[1].rsplit(f"end {ns}", 1)[0]
tail = (f"/-! The bound (generated as {ns}.Main and {ns}.Forms; merged here so that the import closure is loaded once). -/\n\n"
        f"open MeasureTheory ENNReal Set\n\nnamespace {ns}\n" + mb + fb + f"end {ns}\n")
print("equal" if tail == exp else "DIFFERENT")
sys.exit(0 if tail == exp else 1)
