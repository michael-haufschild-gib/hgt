"""
STEP 8 (HT continuum germ, hidden-state) + STEP 9 method=10 "test extreme cases".
Probe: P-recurrence residual of a function's Taylor/Laurent COEFFICIENT germ, with
PRECISION-SATURATION via mpmath-NATIVE SVD (validated last tick). DA germ -> residual DROPS
with dps; HT (infinite hidden state) -> SATURATES.
Extreme cases (method 10): degenerate (Stieltjes germ at zeta's POLE), symmetric (germ at
s=1/2), pathological (lacunary natural-boundary series), vs DA controls + regular HT baseline.
"""
import mpmath as mp

def resid_mp(seq, r=2, d=1):
    N=len(seq); rows=[]
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

def germs(dps, K=14):
    mp.mp.dps=dps
    out={}
    out["DA 1/(1-z): c_k=1"]            = [mp.mpf(1) for k in range(1,K)]
    out["DA exp: c_k=1/k!"]            = [mp.mpf(1)/mp.factorial(k) for k in range(1,K)]
    out["HT regular: logGamma germ zeta(k)/k"] = [mp.zeta(k)/k for k in range(2,K+1)]
    out["HT degenerate: Stieltjes gamma_n (pole germ)"] = [mp.stieltjes(n) for n in range(K)]
    # symmetric extreme: Taylor coeffs of zeta at s=1/2
    tc = mp.taylor(lambda x: mp.zeta(x), mp.mpf('0.5'), K+2)
    out["HT symmetric: zeta germ at s=1/2"] = [tc[k] for k in range(2,K+1)]
    # pathological: lacunary natural-boundary series sum z^(2^n): c_k = 1 if k a power of 2
    pw={2**n for n in range(0,20)}
    out["pathological: lacunary c_k=[k is 2^n]"] = [mp.mpf(1 if k in pw else 0) for k in range(1,K)]
    return out

print("="*78)
print(" STEP8+9(method10): germ hidden-state probe at EXTREME cases, precision-saturation")
print("="*78)
names=list(germs(25).keys())
res={n:[] for n in names}
for dps in (25,50):
    G=germs(dps)
    for n in names:
        try: res[n].append(resid_mp(G[n]))
        except Exception as e: res[n].append(None)
print(f"\n {'germ':46s} dps=25        dps=50        verdict")
for n in names:
    a,b=res[n]
    if a is None or b is None:
        print(f" {n:46s} (error)"); continue
    drop = b < a*mp.mpf('1e-3')   # residual fell substantially with precision
    verdict = "DA (drops -> finite hidden state)" if drop else "HT (SATURATES -> infinite hidden state)"
    print(f" {n:46s} {mp.nstr(a,4):12s} {mp.nstr(b,4):12s} -> {verdict}")
print("\n method-10 read: do the EXTREME germs (pole/symmetric/pathological) saturate like the")
print(" regular HT baseline, or does an extreme case behave differently (a boundary of the probe)?")
