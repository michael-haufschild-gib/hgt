import mpmath as mp, numpy as np
mp.mp.dps = 40
M = 26  # coeff index up to
def coeffs(f):
    t = mp.taylor(f, 0, M)   # c_0..c_M
    return [mp.mpf(x.real) if isinstance(x, mp.mpc) else mp.mpf(x) for x in t]

funcs = {
 "e^x [holo]":      lambda x: mp.e**x,
 "1/(1-x) [holo]":  lambda x: 1/(1-x),
 "Airy-like Bessel J0 [holo]": lambda x: mp.besselj(0, x),
 "logGamma(1+x) [HT]": lambda x: mp.loggamma(1+x),
 "psi(1+x) [HT]":   lambda x: mp.psi(0, 1+x),
 "logBarnesG-ish digamma2 [HT]": lambda x: mp.psi(1, 1+x),
}
# random control
rng = np.random.default_rng(12345)
randc = [mp.mpf(float(rng.standard_normal())) for _ in range(M+1)]

def residue(c, w, d, nstart):
    # P-finite test: sum_{k=0..w} sum_{j=0..d} a_{k,j} n^j c_{n-k} = 0
    rows=[]
    for n in range(nstart, M+1):
        row=[]
        for k in range(w+1):
            for j in range(d+1):
                row.append(float(mp.mpf(n)**j * c[n-k]))
        rows.append(row)
    A=np.array(rows,dtype=float)
    # column-normalize
    norms=np.linalg.norm(A,axis=0); norms[norms==0]=1
    A=A/norms
    s=np.linalg.svd(A, compute_uv=False)
    return s[-1]/s[0]   # normalized smallest singular value

grid=[(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)]
print(f"{'function':32s} " + " ".join(f"(w{w}d{d})" for w,d in grid))
allc = {name: coeffs(f) for name,f in funcs.items()}
allc["random [ctrl]"]=randc
for name,c in allc.items():
    vals=[]
    for w,d in grid:
        nstart=max(w+1,2)
        vals.append(residue(c,w,d,nstart))
    print(f"{name:32s} " + " ".join(f"{v:7.1e}" for v in vals))
