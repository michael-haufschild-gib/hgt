"""
STEP 8 — minimal edit of the NODE test (matched control / paired difference) to run for HT,
NON-HT-blind. The node principle: to attribute a probe's verdict to the MECHANISM (here
hypertranscendence) and not to an artifact, run the SAME probe on a MATCHED control under
IDENTICAL conditions and require SEPARATION.
HT-detection probe: differential-polynomial relation residual (smallest singular value of the
feature matrix [1,x,f,f',...,products]) using EXACT mpmath derivatives. DA => residual ~0
(finite relation); HT => residual stays high.
MATCHED CONTROLS (same grid/precision as the HT function): exp, rational, AND a polynomial fit
to Gamma's own values (matches Gamma's VALUES but is DA). Non-blind iff Gamma separates from all.
"""
import mpmath as mp
import numpy as np
mp.mp.dps = 30

xs = [mp.mpf(x)/10 for x in range(7, 26)]   # 0.7 .. 2.5, 19 pts (common grid)
ORDER = 4

def derivs(f, order):
    return [[mp.diff(f, x, n) for x in xs] for n in range(order+1)]

def relation_residual(dmat, degree=2):
    # feature matrix: 1, x, each f^(n), and degree-2 products of the f^(n)
    cols = [[mp.mpf(1) for _ in xs], list(xs)]
    nd = len(dmat)
    for n in range(nd): cols.append(dmat[n])
    if degree>=2:
        for i in range(nd):
            for j in range(i, nd):
                cols.append([a*b for a,b in zip(dmat[i], dmat[j])])
    A = np.array([[float(c) for c in col] for col in cols]).T   # rows=points, cols=features
    sc = np.linalg.norm(A,axis=0); sc[sc==0]=1; A=A/sc
    s = np.linalg.svd(A, compute_uv=False)
    return float(s[-1]/s[0])

# HT target
gamma_d = derivs(mp.gamma, ORDER)
# matched DA controls on the SAME grid:
exp_d  = derivs(mp.exp, ORDER)
rat_d  = derivs(lambda x: 1/(1+x), ORDER)
# polynomial fit to GAMMA's values (matches Gamma's VALUES; DA): degree-10 interpolation
gvals = [float(mp.gamma(x)) for x in xs]
coef = np.polyfit([float(x) for x in xs], gvals, 10)
poly = np.poly1d(coef)
def poly_f(x): return mp.mpf(float(poly(float(x))))
polyfit_d = derivs(poly_f, ORDER)

print("="*74)
print(" STEP8: HT-detection probe WITH MATCHED CONTROLS (identical grid/precision)")
print("="*74)
cases = {
  "Gamma (HT target)":              gamma_d,
  "  control: exp (DA)":            exp_d,
  "  control: 1/(1+x) (DA)":        rat_d,
  "  control: poly fit to Gamma's VALUES (DA)": polyfit_d,
}
res = {}
for name, dmat in cases.items():
    r = relation_residual(dmat)
    res[name]=r
    tag = "FINITE relation (DA)" if r<1e-6 else "no finite relation (HT-like)"
    print(f"  {name:46s} residual={r:.2e}  -> {tag}")
gr = res["Gamma (HT target)"]
ctrl_max = max(v for k,v in res.items() if "control" in k)
print(f"\n SEPARATION: Gamma residual / worst DA-control residual = {gr/ctrl_max:.1f}x")
print(" Non-blind iff Gamma's residual >> every matched DA control's. The poly-fit control")
print(" (matches Gamma's VALUES) is the key: it catches probes that only see value-asymptotics.")
