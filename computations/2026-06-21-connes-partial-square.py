"""
Partial square identity:  Q_0[p] = int|p|^2 dmu_triv + R^P[p].
  mu_triv = sum_{j>=1} (2j+1/2)^{-2} delta_{y_j},  y_j=-(2j+1/2)^{-2}   (trivial-zero divisor, POSITIVE)
  M^A[i,j] = int y^{i+j} dmu_triv = (-1)^{i+j} sum_{l>=1}(2l+1/2)^{-2(i+j+1)}   (Hurwitz-exact)
  R^P = H^0 - M^A   (prime residual; H^0=[T_{i+j+1}] from the zero divisor)
Reports, per d: inertia(H^0) [PD under RH], inertia(M^A) [PD, positive measure], inertia(R^P) [the
obstruction's SHAPE: is the negative part low-rank or high-rank?]. Also the form values on the
most-dangerous residual direction (lambda_min of H^0|u^perp) to see how mu_triv-square vs R^P balance.
args: N d dps
"""
import sys, mpmath as mp
N=int(sys.argv[1]) if len(sys.argv)>1 else 200
d=int(sys.argv[2]) if len(sys.argv)>2 else 6
mp.mp.dps=int(sys.argv[3]) if len(sys.argv)>3 else 120
KMAX=2*d+1; q1=mp.mpf(1)/4
with open("/root/gam_cache.txt") as f:
    hdr=f.readline().split(); gam=[mp.mpf(f.readline().strip()) for _ in range(N)]
TN=gam[-1]
def tail(k):
    p=2*k-1; return (1/mp.pi)*TN**(-p)/p*(mp.log(TN/(2*mp.pi))+mp.mpf(1)/p)
T={k:2*mp.fsum(g**(-2*k) for g in gam)+tail(k) for k in range(1,KMAX+1)}
H0=mp.matrix(d+1,d+1)
for i in range(d+1):
    for j in range(d+1): H0[i,j]=T[i+j+1]
# M^A[i,j] = (-1)^{i+j} sum_{l>=1}(2l+1/2)^{-2(i+j+1)} = (-1)^{i+j} 2^{-2(i+j+1)}(zeta(2(i+j+1),1/4)-4^{2(i+j+1)})
MA=mp.matrix(d+1,d+1)
for i in range(d+1):
    for j in range(d+1):
        m=i+j; MA[i,j]=(-1)**m*mp.mpf(2)**(-2*(m+1))*(mp.zeta(2*(m+1),q1)-mp.mpf(4)**(2*(m+1)))
RP=H0-MA
def inertia(Hm):
    E=mp.eigsy(Hm,eigvals_only=True); return sum(1 for e in E if e>0),sum(1 for e in E if e<0),min(E),max(E)
p0,n0,mn0,_=inertia(H0); pA,nA,mnA,_=inertia(MA); pP,nP,mnP,mxP=inertia(RP)
print(f"# partial square identity, N={N}, d={d}, dps={mp.mp.dps} (cache {hdr[0]}@{hdr[1]})")
print(f"inertia(H^0)            = ({p0},{n0})  min={mp.nstr(mn0,4)}   (PD under RH)")
print(f"inertia(M^A=mu_triv)    = ({pA},{nA})  min={mp.nstr(mnA,4)}   (PD: positive measure)")
print(f"inertia(R^P prime resid)= ({pP},{nP})  min={mp.nstr(mnP,4)} max={mp.nstr(mxP,4)}   <-- obstruction shape")
# dangerous residual direction (lambda_min of H^0 | u^perp)
u=[mp.mpf(-4)**i for i in range(d+1)]; nu=mp.sqrt(mp.fsum(x*x for x in u))
basis=[[x/nu for x in u]]
for e in range(d+1):
    v=[mp.mpf(1) if i==e else mp.mpf(0) for i in range(d+1)]
    for b in basis:
        dp=mp.fsum(b[i]*v[i] for i in range(d+1)); v=[v[i]-dp*b[i] for i in range(d+1)]
    nv=mp.sqrt(mp.fsum(x*x for x in v))
    if nv>mp.mpf(10)**(-mp.mp.dps//2): basis.append([x/nv for x in v])
    if len(basis)==d+1: break
Bp=basis[1:]
Hr=mp.matrix(d,d)
for a in range(d):
    for b in range(d):
        Hr[a,b]=mp.fsum(Bp[a][i]*H0[i,j]*Bp[b][j] for i in range(d+1) for j in range(d+1))
Er,Vr=mp.eigsy(Hr); cr=[Vr[a,0] for a in range(d)]
pp=[mp.fsum(cr[a]*Bp[a][i] for a in range(d)) for i in range(d+1)]
def form(Hm): return mp.fsum(pp[i]*pp[j]*Hm[i,j] for i in range(d+1) for j in range(d+1))
print(f"# on dangerous residual dir: Q_0={mp.nstr(form(H0),5)}  mu_triv-square={mp.nstr(form(MA),5)}  R^P={mp.nstr(form(RP),5)}")
print(f"#   (Q_0 = mu_triv-square + R^P; R^P nearly cancels the positive trivial-zero square)")
