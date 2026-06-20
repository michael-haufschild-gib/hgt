# Object-selection per DeWitt's bottleneck: nonlinear ADE probe on Lambert series Σσ_k(n)x^n (θ-jets).
# RESULT (dps-stable 80 vs 120): Σσ1 (=E2) CAUGHT (3,2)=2.6e-42 [Chazy, DA]; Σσ0 (divisor count) RESISTS to
# (5,2) [9.6e-20,1.2e-29,1.2e-40, dps-stable, tracks logΓ=HT]. ⟹ Lambert DA-status is k-dependent:
# σ_odd modular/DA, σ0 NOT low-order-DA (HT-evidence to order 5 deg 2). EVIDENCE not proof; novelty needs lit-check.
import mpmath as mp
from itertools import product
N=200
def divcount(n):
    c=0
    for d in range(1,int(n**0.5)+1):
        if n%d==0: c+= 1 if d*d==n else 2
    return c
def sigma1(n):
    s=0
    for d in range(1,n+1):
        if n%d==0: s+=d
    return s
def run(DPS):
    mp.mp.dps=DPS
    s0=[0]+[divcount(n) for n in range(1,N+1)]; s1=[0]+[sigma1(n) for n in range(1,N+1)]
    qs=[mp.mpf(5)/100+mp.mpf(i)*mp.mpf(12)/(100*32) for i in range(33)]
    def Dj(c,w): return [[sum(c[n]*(n**j)*q**n for n in range(1,N+1)) for j in range(w+1)] for q in qs]
    def lg(w): return [[mp.loggamma(q)]+[mp.polygamma(j-1,q) for j in range(1,w+1)] for q in qs]
    def ex(w,d): return [t for t in product(range(d+1),repeat=w+1) if sum(t)<=d]
    def smm(J,w,d):
        E=ex(w,d); R=[[ (lambda e: __import__('functools').reduce(lambda a,b:a*b,[J[i][j]**e[j] for j in range(w+1)],mp.mpf(1)))(e) for e in E] for i in range(len(qs))]
        nc=len(R[0]); M=mp.matrix(len(qs),nc)
        for r in range(len(qs)):
            for c in range(nc): M[r,c]=R[r][c]
        for c in range(nc):
            nr=mp.sqrt(sum(M[r,c]**2 for r in range(M.rows)))
            if nr!=0:
                for r in range(M.rows): M[r,c]=M[r,c]/nr
        ev=mp.eigsy(M.T*M,eigvals_only=True); evl=[ev[i] for i in range(nc)]
        return mp.sqrt(max(mp.mpf(0),min(evl))/max(evl))
    D0=Dj(s0,5); D1=Dj(s1,5); LG=lg(5)
    print(f"dps={DPS}: Σσ0 (3,2)={float(smm(D0,3,2)):.1e} (5,2)={float(smm(D0,5,2)):.1e} | Σσ1 (3,2)={float(smm(D1,3,2)):.1e} | logΓ (3,2)={float(smm(LG,3,2)):.1e}")
run(80); run(120)
