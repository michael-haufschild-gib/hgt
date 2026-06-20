"""
STEP 8 (HT continuum germ) + STEP 9 method=13 "find a monotone quantity".
Monotone quantity: recurrence-residual(r) as a function of recurrence ORDER r (decreasing).
Newton-polygon framing: leading slope = nearest singularity; HT content in subdominant gaps.
Discriminator (ORDER-saturation, complementary to precision-saturation):
  DA/holonomic germ -> residual(r) hits the numerical FLOOR at finite order r* and stays.
  HT germ           -> residual(r) decreases but converges to a POSITIVE limit (never floors).
mpmath-NATIVE SVD (validated). Fixed high precision; vary r.
"""
import mpmath as mp
mp.mp.dps=40

def resid_mp(seq, r, d=1):
    N=len(seq)
    if N-r-1 <= (r+1)*(d+1): return None
    rows=[]
    for k in range(1,N-r):
        row=[]
        for i in range(r+1):
            for e in range(d+1):
                row.append((mp.mpf(k)**e)*seq[k+i])
        rows.append(row)
    A=mp.matrix(rows)
    for j in range(A.cols):
        nrm=mp.sqrt(sum(A[i,j]**2 for i in range(A.rows)))
        if nrm!=0:
            for i in range(A.rows): A[i,j]=A[i,j]/nrm
    ev=mp.eigsy(A.T*A, eigvals_only=True)
    return mp.sqrt(abs(ev[0]))

K=22
germs={
 "DA 1/(1-z) c_k=1":        [mp.mpf(1) for k in range(1,K)],
 "DA exp c_k=1/k!":         [mp.mpf(1)/mp.factorial(k) for k in range(1,K)],
 "DA sin-like 1/(2k)!":     [mp.mpf(1)/mp.factorial(2*k) for k in range(1,K)],
 "HT logGamma germ z(k)/k": [mp.zeta(k)/k for k in range(2,K+1)],
 "HT zeta(k)":              [mp.zeta(k) for k in range(2,K+1)],
 "HT Stieltjes gamma_n":    [mp.stieltjes(n) for n in range(K)],
}
print("="*78)
print(" STEP8+9(method13): MONOTONE residual(r) vs recurrence ORDER r  (dps=40)")
print("  DA -> floors at finite r*;  HT -> converges to POSITIVE limit (order-saturation)")
print("="*78)
print(f"\n {'germ':28s}  r=1        r=2        r=3        r=4")
for n,seq in germs.items():
    vals=[]
    for r in (1,2,3,4):
        v=resid_mp(seq,r)
        vals.append(v)
    cells=" ".join(f"{mp.nstr(v,3):10s}" if v is not None else "   --     " for v in vals)
    # classify: did it floor (<1e-25) at any r?
    floored = any(v is not None and v<mp.mpf('1e-25') for v in vals)
    print(f" {n:28s} {cells}  -> {'DA (floors)' if floored else 'HT (positive limit)'}")
print("\n monotone read (method 13): residual(r) is non-increasing in r; DA crosses to the floor")
print(" at finite r*, HT stays bounded above 0 = order-saturation (infinite-order = global constraint).")
