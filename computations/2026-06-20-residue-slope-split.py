import mpmath as mp, numpy as np
mp.mp.dps = 40
M = 40
def taylor_coeffs(f): 
    t = mp.taylor(f, 0, M); 
    return [mp.mpf(x.real) if isinstance(x,mp.mpc) else mp.mpf(x) for x in t]
def prod_partition():
    # coeffs of prod_{k>=1} 1/(1-x^k) up to M
    c=[mp.mpf(0)]*(M+1); c[0]=mp.mpf(1)
    for k in range(1,M+1):
        for n in range(k, M+1): c[n]+=c[n-k]
    return c
def mahler():
    c=[mp.mpf(0)]*(M+1); k=0
    while 2**k<=M: c[2**k]=mp.mpf(1); k+=1
    return c
def thuemorse():
    c=[mp.mpf(0)]*(M+1); c[0]=mp.mpf(1)
    k=0
    while 2**k<=M:
        nc=c[:]; 
        for n in range(2**k, M+1): nc[n]-=c[n-2**k]
        c=nc; k+=1
    return c
objs={
 "e^x [holo]": taylor_coeffs(lambda x: mp.e**x),
 "BesselJ0 [holo]": taylor_coeffs(lambda x: mp.besselj(0,x)),
 "logGamma [ζ-HT]": taylor_coeffs(lambda x: mp.loggamma(1+x)),
 "psi [ζ-HT]": taylor_coeffs(lambda x: mp.psi(0,1+x)),
 "Mahler Σx^2^k [non-ζ]": mahler(),
 "Thue-Morse [non-ζ]": thuemorse(),
 "partition Π1/(1-x^k) [non-ζ/modular]": prod_partition(),
}
rng=np.random.default_rng(7); objs["random"]=[mp.mpf(float(v)) for v in rng.standard_normal(M+1)]
def residue(c,w,d=1,nstart=None):
    nstart=nstart or max(w+1,2); rows=[]
    for n in range(nstart,M+1):
        row=[]
        for k in range(w+1):
            for j in range(d+1): row.append(float(mp.mpf(n)**j*c[n-k]))
        rows.append(row)
    A=np.array(rows); nm=np.linalg.norm(A,axis=0); nm[nm==0]=1; A=A/nm
    s=np.linalg.svd(A,compute_uv=False); return s[-1]/s[0]
print(f"{'object':38s} " + " ".join(f"w{w}" for w in range(1,8)) + "   slope(dec/step)")
for name,c in objs.items():
    vals=[residue(c,w) for w in range(1,8)]
    ly=[np.log10(max(v,1e-300)) for v in vals]
    # slope over the gradual region (skip if it hit ~0)
    xs=np.arange(1,8); slope=np.polyfit(xs,ly,1)[0]
    print(f"{name:38s} " + " ".join(f"{v:6.0e}" for v in vals) + f"   {-slope:5.2f}")
