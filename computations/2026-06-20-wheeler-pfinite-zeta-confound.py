# Decisive ζ-confound test of Popper's P-finite residue signature (Wheeler, 2nd pipeline, 2026-06-20).
# Pre-registered: do NON-ζ HT (Mahler, partition, Thue-Morse) share the gradual P-finite-residue decay?
# VERDICT: qualitative three-way (HT gradual vs holonomic abrupt) genuine but = known binary (HT⟺no finite ODE);
# parallel slopes = ζ-family artifact (slope tracks analytic structure = conformal confound, not HT-class).
import mpmath as mp
mp.mp.dps=35
xs=[mp.mpf(3)/10 + mp.mpf(i)*mp.mpf(4)/(10*45) for i in range(46)]
N=260
def popcount(n):
    c=0
    while n: c+=n&1; n>>=1
    return c
pow2=set(2**k for k in range(0,9))
mahler=[1 if n in pow2 else 0 for n in range(N+1)]
thue=[(-1)**popcount(n) for n in range(N+1)]
p=[0]*(N+1); p[0]=1
for n in range(1,N+1):
    s=0;k=1
    while True:
        g1=k*(3*k-1)//2; g2=k*(3*k+1)//2
        if g1>n and g2>n: break
        sg=(-1)**(k+1)
        if g1<=n: s+=sg*p[n-g1]
        if g2<=n: s+=sg*p[n-g2]
        k+=1
    p[n]=s
def series_jet(c,x,w):
    out=[]
    for j in range(w+1):
        s=mp.mpf(0)
        for n in range(j,N+1):
            if c[n]==0: continue
            ff=1
            for t in range(j): ff*=(n-t)
            s+=c[n]*ff*x**(n-j)
        out.append(s)
    return out
def poly_jet(fn,x,w): return [mp.diff(fn,x,j) for j in range(w+1)]
def cond_at(jets,w,d):
    cols=[[(x**a)*jets[i][j] for i,x in enumerate(xs)] for j in range(w+1) for a in range(d+1)]
    nc=len(cols); M=mp.matrix(len(xs),nc)
    for r in range(len(xs)):
        for cc in range(nc): M[r,cc]=cols[cc][r]
    for cc in range(nc):
        nrm=mp.sqrt(sum(M[r,cc]**2 for r in range(M.rows)))
        if nrm==0: continue
        for r in range(M.rows): M[r,cc]=M[r,cc]/nrm
    ev=mp.eigsy(M.T*M, eigvals_only=True); evl=[ev[i] for i in range(nc)]
    return mp.sqrt(max(mp.mpf(0),min(evl))/max(evl))
funcs={"e^x[HOL1]":("poly",lambda x:mp.e**x),"BesselJ0[HOL2]":("poly",lambda x:mp.besselj(0,x)),
 "logGamma[zHT]":("poly",lambda x:mp.loggamma(x)),"psi[zHT]":("poly",lambda x:mp.polygamma(0,x)),
 "Mahler[nzHT]":("ser",mahler),"Partition[nzHT]":("ser",p),"ThueMorse[nzHT]":("ser",thue)}
for name,(kind,fn) in funcs.items():
    jets=[(series_jet(fn,x,7) if kind=="ser" else poly_jet(fn,x,7)) for x in xs]
    print(name, [f"{float(cond_at(jets,w,1)):.1e}" for w in range(1,8)])
