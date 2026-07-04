#!/usr/bin/env python3
"""HARD refutation search for (S-mono): does ANY single-connected-range one-sided
LP carrier x pair give Z_c(J^d_{Pg}) >= 4 (a spurious pair)? A hit REFUTES (S-mono)."""
import numpy as np
from math import factorial

def jensen_section(cj, d):
    coeffs=[factorial(d)//factorial(d-j)*cj[j] if (j<=d and j<len(cj)) else 0 for j in range(min(d,len(cj)-1)+1)]
    return np.array(coeffs[::-1], dtype=float)
def zc(p):
    r=np.roots(p); return int(np.sum(np.abs(r.imag)>1e-6))
def carrier_coeffs(roots):
    p=np.poly(roots); c=p[::-1].astype(float); return list(c/c[0])
def Zc_Pg(cj,d,a,b):
    Ad=jensen_section(cj,d); Ad1=jensen_section(cj,d-1); Ad2=jensen_section(cj,d-2)
    def padmul(p,shift): return np.concatenate([p, np.zeros(shift)])
    t1=(a*a+b*b)*Ad; t2=-2*a*d*padmul(Ad1,1); t3=d*(d-1)*padmul(Ad2,2)
    L=max(len(t1),len(t2),len(t3))
    def padL(p): return np.concatenate([np.zeros(L-len(p)),p])
    return zc(padL(t1)+padL(t2)+padL(t3))

rng=np.random.default_rng(20260705)
worst=0; worst_case=None; ntested=0; spurious=[]
# single-connected-range one-sided carriers: zeros in [L,R] all same sign, various densities
shapes=[]
# uniform negative
shapes.append(("uniform-neg", lambda K: [-1.0*(i+1) for i in range(K)]))
# clustered near 0 (dense) then sparse (one-sided, single range)
shapes.append(("geom-neg", lambda K: [-1.2**i for i in range(K)]))
# equally spaced far from 0 (one-sided, offset)
shapes.append(("offset-neg", lambda K: [-(5.0+0.7*i) for i in range(K)]))
# recentered INTO field risk: zeros straddle but we shift so pole 0 is at edge -> use positive one-sided
shapes.append(("uniform-pos", lambda K: [1.0*(i+1) for i in range(K)]))
# random one-sided monotone gaps (nondecreasing) 
def randmono(K):
    gaps=np.sort(rng.uniform(0.3,2.0,K)); pts=-np.cumsum(gaps); return list(pts)
shapes.append(("rand-mono-neg", randmono))
# random one-sided NON-monotone gaps (violates F2 - should this break it?)
def randnonmono(K):
    gaps=rng.uniform(0.2,3.0,K); pts=-np.cumsum(gaps); return list(pts)
shapes.append(("rand-nonmono-neg", randnonmono))

taus=[(0.0,1.0),(0.0,0.3),(0.0,0.1),(0.5,1.0),(2.0,0.8),(5.0,0.5),(-1.5,1.3),
      (0.3,0.2),(1.0,0.15),(0.0,2.0),(3.0,0.3),(-3.0,0.4)]
ds=[6,8,10,12,16,20,26,32,40,50,64]

for name,gen in shapes:
    for K in [6,8,10,12,15]:
        try: roots=gen(K)
        except Exception: continue
        cj=carrier_coeffs(roots)
        for (a,b) in taus:
            for d in ds:
                if d> len(cj)+30: continue
                try: z=Zc_Pg(cj,d,a,b)
                except Exception: continue
                ntested+=1
                if z>worst: worst=z; worst_case=(name,K,a,b,d,z)
                if z>=4: spurious.append((name,K,a,b,d,z))
print(f"tested {ntested} configs. worst Z_c = {worst}  at {worst_case}")
print(f"spurious (Z_c>=4) count = {len(spurious)}")
if spurious:
    for s in spurious[:20]: print("  SPURIOUS:", s)
    print(">>> (S-mono) REFUTED: single-range one-sided carrier gives a spurious pair")
else:
    print(">>> NO spurious pair found on any single-range one-sided carrier (incl. F2-violating nonmono gaps)")
    print(">>> (S-mono)/reader-exactness robustly corroborated -> proceed to PROVE")
