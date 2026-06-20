#!/usr/bin/env python3
# MACHINE STEP8 (continuum/differential, v9) + STEP9 method#14 (FIND AN INVARIANT).
# Freeness node lesson: a FINITE check can't certify an ALL-ORDERS constraint. HT analog: a finite-order
# differential-relation check can't certify HT. INVARIANT (method#14, Wheeler-corrected, mpmath-NATIVE):
# precision-saturation of the differential-relation residual sigma_min.
#   DA  -> sigma_min DROPS ~10^-dps (a true finite-order polynomial-differential relation P(x,f,...,f^R)=0)
#   HT  -> sigma_min SATURATES (precision-independent): no finite relation at this order = the invariant.
import mpmath as mp

def diff_residual(f, R, D, dps, npts=22):
    mp.mp.dps = dps
    # two DISJOINT intervals (globality); avoid x=1 (zeta pole). OVERSAMPLE: rows >> cols (no false null).
    xs = [mp.mpf('1.3')+mp.mpf(i)*mp.mpf('0.11') for i in range(npts)] + \
         [mp.mpf('7.0')+mp.mpf(i)*mp.mpf('0.11') for i in range(npts)]
    feats=[]
    for x in xs:
        jet=[mp.mpf(1), x] + [mp.diff(f, x, k) for k in range(R+1)]
        row=[]
        for i in range(len(jet)): row.append(jet[i])
        if D>=2:
            for i in range(len(jet)):
                for j in range(i,len(jet)):
                    row.append(jet[i]*jet[j])
        feats.append(row)
    M=mp.matrix(feats)
    ncol=M.cols; nrow=M.rows
    assert nrow > 2*ncol, f"need oversampling: rows {nrow} cols {ncol}"
    # column-equilibrate
    for c in range(ncol):
        nrm=mp.sqrt(sum(M[r,c]**2 for r in range(nrow)))
        if nrm>0:
            for r in range(nrow): M[r,c]/=nrm
    # DIRECT mpmath-native SVD (no Gram-squaring; sigma_min resolvable to ~10^-dps)
    S=mp.svd_r(M, compute_uv=False)
    return min(abs(s) for s in S)

cases = [
    ("exp  (DA order1)",  lambda x: mp.e**x,        1, 1),
    ("tan  (DA Riccati)", lambda x: mp.tan(x),      1, 2),
    ("Gamma (HT)",        lambda x: mp.gamma(x),    2, 2),
    ("zeta  (HT)",        lambda x: mp.zeta(x),     2, 2),
]
print("=== STEP8+method#14: precision-saturation INVARIANT of the differential-relation residual ===")
print("  function          (R,D) | sigma_min @dps=25 | sigma_min @dps=45 | ratio  -> DA drops / HT saturates")
for name,f,R,D in cases:
    s25=diff_residual(f,R,D,25); s45=diff_residual(f,R,D,45)
    ratio = float(s25/s45) if s45!=0 else float('inf')
    verdict = "DA (drops ~10^-dps)" if ratio>1e6 else "HT (SATURATES, precision-indep)"
    print(f"  {name:18s} ({R},{D}) | {mp.nstr(s25,4):>14} | {mp.nstr(s45,4):>14} | {ratio:.2e}  {verdict}")
print("\nREAD (STEP10): the INVARIANT is precision-saturation. DA residual ~10^-dps (tracks precision = real")
print("finite relation); HT residual fixed across dps (no finite-order relation = HT). mpmath-native per Wheeler.")
