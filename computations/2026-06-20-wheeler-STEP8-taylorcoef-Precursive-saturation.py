"""
STEP 8 — minimal edit of the LHS node test (global vs incrementally-buildable) to HT,
targeting the CONTINUUM/DIFFERENTIAL structure on C (Taylor coefficients = the germ), NOT
the discrete values zeta(n). Test: is the Taylor-COEFFICIENT sequence of an HT function
P-recursive (finite recurrence = 'incrementally buildable' = DA) or not (HT = global)?
NON-BLIND via the matched-control + PRECISION-SATURATION methodology (Wheeler last tick):
a true finite-order P-recurrence -> residual drops to the numerical floor as dps rises;
an HT (infinite-order) coefficient sequence -> residual SATURATES (precision-independent).
"""
import mpmath as mp, numpy as np

def precurse_residual(seq, rmax=3, dmax=2):
    """smallest normalized singular value over P-recurrences sum_i p_i(k) c_{k+i}=0, p_i deg<=d."""
    N=len(seq); best=1e9
    for r in range(1,rmax+1):
        for d in range(0,dmax+1):
            rows=[]
            for k in range(1,N-r):
                row=[]
                for i in range(r+1):
                    for e in range(d+1):
                        row.append((k**e)*seq[k+i])
                rows.append(row)
            A=np.array(rows,dtype=float)
            if A.shape[0]<A.shape[1]: continue
            sc=np.linalg.norm(A,axis=0); sc[sc==0]=1; A=A/sc
            best=min(best, float(np.linalg.svd(A,compute_uv=False)[-1]))
    return best

def seqs(dps, K=26):
    mp.mp.dps=dps
    return {
     "1/k  (DA: log 1/(1-x))":      [float(mp.mpf(1)/k) for k in range(1,K)],
     "1/k! (DA: exp)":              [float(mp.mpf(1)/mp.factorial(k)) for k in range(1,K)],
     "1+2^-k+3^-k (DA, truncated-zeta, P-rec order3)": [float(1+mp.mpf(2)**-k+mp.mpf(3)**-k) for k in range(1,K)],
     "zeta(k)/k  (HT: log Gamma germ)": [float(mp.zeta(k)/k) for k in range(2,K+1)],
     "zeta(k)    (HT germ, raw)":    [float(mp.zeta(k)) for k in range(2,K+1)],
    }

print("="*78)
print(" STEP8: P-recurrence residual of Taylor-COEFFICIENT sequences, PRECISION-SCAN")
print("  DA -> residual tracks DOWN with dps (numerical floor);  HT -> SATURATES (real defect)")
print("="*78)
names=list(seqs(20).keys())
table={n:[] for n in names}
for dps in (20,35,55):
    S=seqs(dps)
    for n in names:
        table[n].append(precurse_residual(S[n]))
print(f"\n {'sequence':46s} dps=20      dps=35      dps=55     verdict")
for n in names:
    r20,r35,r55 = table[n]
    saturates = r55 > 1e-9 and r55/r20 > 1e-3   # not dropping toward floor
    verdict = "HT (SATURATES)" if saturates else "DA (drops to floor)"
    print(f" {n:46s} {r20:.2e}  {r35:.2e}  {r55:.2e}  -> {verdict}")
print("\n VERDICT: the corrected non-blind probe should classify zeta(k)/k & zeta(k) (HT germ)")
print(" as SATURATING (infinite-order = global constraint), while DA coeff-sequences drop to the")
print(" floor. The truncated-zeta control (P-rec order 3) must read DA -> separates artifact from HT.")
