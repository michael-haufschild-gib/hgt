#!/usr/bin/env python3
# JOINT differential-algebraic (in)dependence of two functions, via the validated height-instrument.
# Variables: (x, f,f',...,f^R, g,g',...,g^R). A GLOBAL low-height integer relation that involves BOTH
# an f-derivative AND a g-derivative = a genuine COUPLING (joint DA-dependence). Since Gamma & zeta are
# each individually HT (resist alone), ANY relation in the joint system couples them.
# reverse-validate (rng move): confirm the instrument CATCHES known couplings before trusting a resist.
import mpmath as mp, itertools
from math import gcd
mp.mp.dps=120
HMAX=10**6; TOLV=mp.mpf(10)**-55
def J(R, *vals):  # not used; placeholder
    pass
# jet providers (return [f,f',...,f^R])
def j_exp(x,R): e=mp.e**x; return [e]*(R+1)
def j_gam(x,R): g=mp.gamma(x); p0=mp.digamma(x); p1=mp.polygamma(1,x); return [g,g*p0,g*(p0*p0+p1)][:R+1]
def j_psi(x,R): return [mp.digamma(x), mp.polygamma(1,x), mp.polygamma(2,x)][:R+1]
def j_zet(x,R): return [mp.zeta(x),mp.zeta(x,derivative=1),mp.zeta(x,derivative=2)][:R+1]
def j_J0(x,R): j0=mp.besselj(0,x); j1=mp.besselj(1,x); return [j0,-j1,-j0+j1/x][:R+1]
def j_J1(x,R):
    j0=mp.besselj(0,x); j1=mp.besselj(1,x); j1p=j0-j1/x
    j1pp=-j0+ (j1/x - (j0 - j1/x))/x  # not needed beyond R=1; keep [j1,j1']
    return [j1, j1p, j1pp][:R+1]
def monos(nv,D):
    out=[]
    for tot in range(D+1):
        for cc in itertools.combinations_with_replacement(range(nv),tot):
            e=[0]*nv
            for i in cc: e[i]+=1
            out.append(tuple(e))
    return out
def rowvals(jf,jg,x,R,ms):
    v=[x]+jf(x,R)+jg(x,R)
    return [mp.fprod([v[k]**e[k] for k in range(len(v))]) for e in ms]
def Mmat(jf,jg,A,B,R,D,K=34):
    nv=1+2*(R+1); ms=monos(nv,D); xs=[]
    for (lo,hi) in (A,B):
        xs+=[mp.mpf(lo)+(mp.mpf(hi)-mp.mpf(lo))*mp.mpf(i+1)/mp.mpf(K+1) for i in range(K)]
    M=mp.matrix([rowvals(jf,jg,x,R,ms) for x in xs])
    return M, ms, nv
def nullvec(M):
    U,S,V=mp.svd_r(M,compute_uv=True); return [V[V.rows-1,j] for j in range(V.cols)]
def rationalize(v):
    k=max(range(len(v)), key=lambda i: abs(v[i])); vn=[vi/v[k] for vi in v]
    nums=[]; dens=[]
    for vi in vn:
        if abs(vi)<mp.mpf(10)**-35: nums.append(0); dens.append(1); continue
        r=mp.pslq([vi,mp.mpf(1)],maxcoeff=HMAX,maxsteps=10000)
        if r is None or r[0]==0: return None
        a,b=r; nums.append(-b); dens.append(a)
    L=1
    for d in dens: L=L*d//gcd(L,d) if d!=0 else L
    c=[nums[i]*(L//dens[i]) for i in range(len(v))]; g=0
    for ci in c: g=gcd(g,ci)
    if g>1: c=[ci//g for ci in c]
    return c
def classify(c, ms, R):
    f_idx=set(range(1,R+2)); g_idx=set(range(R+2,2*R+3))
    invf=invg=False
    for k,e in enumerate(ms):
        if c[k]==0: continue
        if any(e[i]>0 for i in f_idx): invf=True
        if any(e[i]>0 for i in g_idx): invg=True
    return 'COUPLING' if (invf and invg) else ('f-only' if invf else ('g-only' if invg else 'const'))
def test(jf,jg,A,B,R,D):
    M,ms,nv=Mmat(jf,jg,A,B,R,D); v=nullvec(M); c=rationalize(v)
    if c is None: return ('resist',None,None)
    h=max(abs(ci) for ci in c)
    res=M*mp.matrix(c); r=mp.sqrt(mp.fsum(res[i]**2 for i in range(M.rows)))
    cn=mp.sqrt(mp.fsum(ci**2 for ci in c))
    rn=max(mp.sqrt(mp.fsum(M[i,j]**2 for j in range(M.cols))) for i in range(M.rows))
    if r/(cn*rn+mp.mpf(10)**-50) >= TOLV: return ('spurious',h,None)
    return ('GLOBAL', h, classify(c,ms,R))
# pairs: (name, jf, jg, A, B)
pairs=[
 ('J0,J1 [dep:J0+J1?]', j_J0,j_J1,(0.5,1.5),(2.6,3.4)),
 ('Gam,psi [dep:psi=G/G]', j_gam,j_psi,(1.2,2.0),(3.5,4.5)),
 ('exp,Gam [exp self-DA]', j_exp,j_gam,(1.2,2.0),(3.5,4.5)),
 ('Gam,zeta [TARGET]', j_gam,j_zet,(1.6,2.4),(3.2,4.0)),
]
grid=[(1,1),(1,2),(1,3),(2,2)]
print(f"dps={mp.mp.dps} HMAX={HMAX}  JOINT relation: status / height / kind per (R,D)")
print("pair                       "+"".join(f"({R},{D})            " for (R,D) in grid))
res={}
for (nm,jf,jg,A,B) in pairs:
    row=[]; res[nm]={}
    for (R,D) in grid:
        try: st,h,kind=test(jf,jg,A,B,R,D)
        except Exception as e: st,h,kind='ERR',str(e)[:10],None
        res[nm][(R,D)]=(st,h,kind)
        cell = f"{st}" if st!='GLOBAL' else f"h{h}:{kind}"
        row.append(cell)
    print(f"{nm:26s} "+"".join(f"{c:<17s}" for c in row))
print("\n-- minimal (R,D) with a GLOBAL COUPLING (joint DA-dependence) / else no coupling --")
for (nm,*_) in pairs:
    cpl=[((R,D),res[nm][(R,D)][1]) for (R,D) in grid if res[nm][(R,D)][0]=='GLOBAL' and res[nm][(R,D)][2]=='COUPLING']
    if cpl:
        mn=min(cpl,key=lambda t:(t[0][0],t[0][1])); print(f"{nm:26s} COUPLING at {mn[0]} height={mn[1]}")
    else: print(f"{nm:26s} NO coupling found (jointly DA-independent up to grid)")
