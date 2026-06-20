#!/usr/bin/env python3
# Corrected DISCRETE ADE instrument: MULTI-POINT null vector (must hold at all pts) + RATIONALIZE to
# bounded integer height + VERIFY against M. Confound signature: HT null vector has IRRATIONAL
# components (no low-height integer structure); a true ADE null vector is RATIONAL (clears to integers).
# Height = the discrete invariant (S67). HMAX: heights above it = "not low-height" = HT-like.
import mpmath as mp, itertools
from math import gcd
mp.mp.dps=120
HMAX=10**6; TOLV=mp.mpf(10)**-60
def jet_exp(x,R):  e=mp.e**x; return [e]*(R+1)
def jet_tan(x,R):  t=mp.tan(x); f1=1+t*t; f2=2*t*f1; return [t,f1,f2][:R+1]
def jet_sn(x,R,m=mp.mpf('0.37')):
    s=mp.ellipfun('sn',x,m); c=mp.ellipfun('cn',x,m); d=mp.ellipfun('dn',x,m)
    return [s, c*d, -s*(d*d+m*c*c)][:R+1]
def jet_bes(x,R): j0=mp.besselj(0,x); j1=mp.besselj(1,x); return [j0,-j1,-j0+j1/x][:R+1]
def jet_gam(x,R): g=mp.gamma(x); p0=mp.digamma(x); p1=mp.polygamma(1,x); return [g,g*p0,g*(p0*p0+p1)][:R+1]
def jet_zet(x,R): return [mp.zeta(x),mp.zeta(x,derivative=1),mp.zeta(x,derivative=2)][:R+1]
def monos(nv,D):
    out=[]
    for tot in range(D+1):
        for cc in itertools.combinations_with_replacement(range(nv),tot):
            e=[0]*nv
            for i in cc: e[i]+=1
            out.append(tuple(e))
    return out
def row(jet,x,R,ms):
    v=[x]+jet(x,R); return [mp.fprod([v[k]**e[k] for k in range(R+2)]) for e in ms]
def Mmat(jet,A,B,R,D,K=24):   # K per interval; need 2K > #monomials (overdetermined)
    ms=monos(R+2,D); xs=[]
    for (lo,hi) in (A,B):
        xs+=[mp.mpf(lo)+(mp.mpf(hi)-mp.mpf(lo))*mp.mpf(i+1)/mp.mpf(K+1) for i in range(K)]
    return mp.matrix([row(jet,x,R,ms) for x in xs]), ms
def nullvec(M):
    U,S,V=mp.svd_r(M, compute_uv=True)     # direct SVD (no Gram condition-squaring)
    return [V[V.rows-1,j] for j in range(V.cols)]   # smallest right singular vector
def rationalize(v):
    # normalize by max-magnitude component, rationalize each to height<=HMAX -> integer vector c
    k=max(range(len(v)), key=lambda i: abs(v[i]))
    vn=[vi/v[k] for vi in v]
    nums=[]; dens=[]
    for vi in vn:
        if abs(vi) < mp.mpf(10)**-35: nums.append(0); dens.append(1); continue
        r=mp.pslq([vi, mp.mpf(1)], maxcoeff=HMAX, maxsteps=10000)
        if r is None or r[0]==0: return None         # not low-height rational
        a,b=r                                         # a*vi + b = 0 -> vi = -b/a
        nums.append(-b); dens.append(a)
    L=1
    for d in dens: L=L*d//gcd(L, d) if d!=0 else L
    c=[ (nums[i]*(L//dens[i])) for i in range(len(v)) ]
    g=0
    for ci in c: g=gcd(g, ci)
    if g>1: c=[ci//g for ci in c]
    return c
def test(jet,A,B,R,D):
    M,ms=Mmat(jet,A,B,R,D)
    v=nullvec(M)
    c=rationalize(v)
    if c is None: return ('resist', None)
    h=max(abs(ci) for ci in c)
    # verify integer relation against ALL rows of M
    cc=mp.matrix(c); res=M*cc
    r=mp.sqrt(mp.fsum(res[i]**2 for i in range(M.rows)))
    cn=mp.sqrt(mp.fsum(ci**2 for ci in c))
    rownorm=max(mp.sqrt(mp.fsum(M[i,j]**2 for j in range(M.cols))) for i in range(M.rows))
    rel=r/(cn*rownorm+mp.mpf(10)**-50)
    return ('GLOBAL' if rel<TOLV else 'spurious', h)
funcs={
 'exp':(jet_exp,(0.4,1.2),(2.0,2.8)),'tan':(jet_tan,(0.1,0.6),(0.9,1.4)),
 'sn_m.37':(jet_sn,(0.2,0.8),(2.5,3.1)),'besselJ0':(jet_bes,(0.5,1.5),(3.0,4.0)),
 'Gamma':(jet_gam,(1.2,2.0),(3.5,4.5)),'zeta':(jet_zet,(2.2,3.0),(4.0,5.0)),
}
grid=[(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)]
print(f"dps={mp.mp.dps} HMAX={HMAX}  multi-point null-vec rationalized to integer height:")
print("func        "+"".join(f"({R},{D})        " for (R,D) in grid))
res={}
for name,(jet,A,B) in funcs.items():
    row_=[]; res[name]={}
    for (R,D) in grid:
        try: st,h=test(jet,A,B,R,D)
        except Exception as e: st,h='ERR',str(e)[:8]
        res[name][(R,D)]=(st,h); row_.append((st,h))
    print(f"{name:11s} "+"".join((f"{(('G h='+str(h)) if st=='GLOBAL' else st):<15s} ") for (st,h) in row_))
print("\n-- MINIMAL (R,D) with GLOBAL low-height integer ADE / else RESISTS (HT) --")
for name in funcs:
    hit=[((R,D),res[name][(R,D)][1]) for (R,D) in grid if res[name][(R,D)][0]=='GLOBAL']
    if hit:
        mn=min(hit,key=lambda t:(t[0][0],t[0][1])); print(f"{name:11s} ADE at {mn[0]} height={mn[1]}")
    else: print(f"{name:11s} RESISTS  <-- HT signature")
