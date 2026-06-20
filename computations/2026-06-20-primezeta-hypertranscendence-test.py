#!/usr/bin/env python3
# Is the PRIME ZETA function P(s)=sum_p p^-s differentially algebraic, or hypertranscendental?
# Native-weld object (summed sigma_p generators); natural boundary at Re(s)=0. Constructed via wild
# collision renormalization x tide-tables (renormalized prime-tide). Test with the validated height
# instrument. High-prec jet via P(s)=sum_k mu(k)/k log zeta(ks) (direct prime sum can't reach dps).
import mpmath as mp, itertools
from math import gcd
mp.mp.dps=80
HMAX=10**6; TOLV=mp.mpf(10)**-45
# Mobius sieve
def mobius_upto(N):
    mu=[1]*(N+1); mu[0]=0; primes=[]; is_c=[False]*(N+1)
    for i in range(2,N+1):
        if not is_c[i]: primes.append(i); mu[i]=-1
        for p in primes:
            if i*p>N: break
            is_c[i*p]=True
            if i%p==0: mu[i*p]=0; break
            else: mu[i*p]=-mu[i]
    return mu
KMAX=160
MU=mobius_upto(KMAX)
def primezeta_jet(s,R):
    # P=sum mu(k)/k log z(ks); P'=sum mu(k) z'(ks)/z(ks); P''=sum mu(k) k (z''/z-(z'/z)^2)(ks)
    P=mp.mpf(0); P1=mp.mpf(0); P2=mp.mpf(0)
    for k in range(1,KMAX+1):
        if MU[k]==0: continue
        ks=k*s
        z=mp.zeta(ks); z1=mp.zeta(ks,derivative=1); z2=mp.zeta(ks,derivative=2)
        lr=z1/z
        P  += MU[k]/mp.mpf(k)*mp.log(z)
        P1 += MU[k]*lr
        P2 += MU[k]*k*(z2/z - lr*lr)
    return [P,P1,P2][:R+1]
# controls
def jet_tan(x,R): t=mp.tan(x); f1=1+t*t; f2=2*t*f1; return [t,f1,f2][:R+1]
def jet_gam(x,R): g=mp.gamma(x); p0=mp.digamma(x); p1=mp.polygamma(1,x); return [g,g*p0,g*(p0*p0+p1)][:R+1]
# sanity: formula vs mp.primezeta
for sv in ['2.3','3.1','4.0']:
    s=mp.mpf(sv); err=abs(primezeta_jet(s,0)[0]-mp.primezeta(s))
    print(f"primezeta check s={sv}: |formula-mp.primezeta|={mp.nstr(err,3)}")
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
def Mmat(jet,A,B,R,D,K=22):
    ms=monos(R+2,D); xs=[]
    for (lo,hi) in (A,B): xs+=[mp.mpf(lo)+(mp.mpf(hi)-mp.mpf(lo))*mp.mpf(i+1)/mp.mpf(K+1) for i in range(K)]
    return mp.matrix([row(jet,x,R,ms) for x in xs]), ms
def nullvec(M):
    U,S,V=mp.svd_r(M,compute_uv=True); return [V[V.rows-1,j] for j in range(V.cols)]
def rationalize(v):
    k=max(range(len(v)),key=lambda i:abs(v[i])); vn=[vi/v[k] for vi in v]; nums=[]; dens=[]
    for vi in vn:
        if abs(vi)<mp.mpf(10)**-30: nums.append(0); dens.append(1); continue
        r=mp.pslq([vi,mp.mpf(1)],maxcoeff=HMAX,maxsteps=10000)
        if r is None or r[0]==0: return None
        a,b=r; nums.append(-b); dens.append(a)
    L=1
    for d in dens: L=L*d//gcd(L,d) if d!=0 else L
    c=[nums[i]*(L//dens[i]) for i in range(len(v))]; g=0
    for ci in c: g=gcd(g,ci)
    if g>1: c=[ci//g for ci in c]
    return c
def test(jet,A,B,R,D):
    M,ms=Mmat(jet,A,B,R,D); v=nullvec(M); c=rationalize(v)
    if c is None: return ('resist',None)
    h=max(abs(ci) for ci in c); res=M*mp.matrix(c)
    r=mp.sqrt(mp.fsum(res[i]**2 for i in range(M.rows))); cn=mp.sqrt(mp.fsum(ci**2 for ci in c))
    rn=max(mp.sqrt(mp.fsum(M[i,j]**2 for j in range(M.cols))) for i in range(M.rows))
    return ('GLOBAL' if r/(cn*rn+mp.mpf(10)**-50)<TOLV else 'spurious', h)
funcs={'tan[ctrl-DA]':(jet_tan,(0.1,0.6),(0.9,1.4)),
       'Gamma[ctrl-HT]':(jet_gam,(1.2,2.0),(3.5,4.5)),
       'primeZeta':(primezeta_jet,(2.2,3.0),(3.8,4.6))}
grid=[(1,1),(1,2),(1,3),(1,4),(2,2)]
print(f"\ndps={mp.mp.dps}  ADE height-test (G h=height = relation found; else resist):")
print("func           "+"".join(f"({R},{D})     " for (R,D) in grid))
res={}
for nm,(jet,A,B) in funcs.items():
    row_=[]; res[nm]={}
    for (R,D) in grid:
        try: st,h=test(jet,A,B,R,D)
        except Exception as e: st,h='ERR',str(e)[:8]
        res[nm][(R,D)]=(st,h); row_.append(f"G h{h}" if st=='GLOBAL' else st)
    print(f"{nm:14s} "+"".join(f"{c:<11s}" for c in row_))
print("\n-- VERDICT --")
for nm in funcs:
    hit=[((R,D),res[nm][(R,D)][1]) for (R,D) in grid if res[nm][(R,D)][0]=='GLOBAL']
    if hit:
        mn=min(hit,key=lambda t:(t[0][0],t[0][1])); print(f"{nm:14s} ADE at {mn[0]} height={mn[1]}")
    else: print(f"{nm:14s} RESISTS (no low-height ADE) -> hypertranscendental signature")
