"""comp81 — does the SIGN of the prime part control the boundary positivity s_d>0?  (NR-2 probe)

Split the seam moments T_k = T_k^A + T_k^P:
  c^A_{2k} = -4^k/k + polygamma(2k-1,1/4)/((2k)! 4^k)      (archimedean: pole + Gamma/trivial zeros)
  c^P_{2k} = g_{2k} = [w^{2k}] log zeta(1/2+w)             (prime / zeta-source part)
  T_k = 2(-1)^{k+1} k (c^A_{2k}+c^P_{2k});  T_k^A from c^A only;  T_k^flip from c^A - c^P.
Build H^0=[T_{i+j+1}] (real zeta), H^A (archimedean only), H^flip (prime sign reversed).
For each: s_d = a_*+1/m_d, m_d=v_*^T (H - a_* v_* v_*^T)^{-1} v_*, y_*=-0.16, a_*=0.16.
DECISIVE: if s_d(zeta)>0 while s_d(flip)<0, the prime SIGN (Euler-product positivity Lambda(n)>=0) is the
load-bearing input for s_d>0.  Also report inertia of H^- in each case.  Outcome unknown a priori."""
import mpmath as mp
A_STAR=mp.mpf('0.16'); Y_STAR=-A_STAR

def cA_cP(kmax):
    "return c^A_{2k} (pole+Gamma) and c^P_{2k}=g_{2k} (prime), k=1..kmax"
    M=2*kmax+1
    a=[mp.zeta(mp.mpf('0.5'),1,m)/mp.factorial(m) for m in range(M+1)]
    g=[mp.mpf(0)]*(M+1); g[0]=mp.log(a[0])
    for m in range(1,M+1):
        s=mp.fsum(n*g[n]*a[m-n] for n in range(1,m))
        g[m]=(m*a[m]-s)/(m*a[0])
    cA=[None]*(kmax+1); cP=[None]*(kmax+1)
    for k in range(1,kmax+1):
        cA[k]=-mp.power(4,k)/k + mp.polygamma(2*k-1,mp.mpf(1)/4)/(mp.factorial(2*k)*mp.power(4,k))
        cP[k]=g[2*k]
    return cA,cP

def Tfrom(c,kmax): return [None]+[2*((-1)**(k+1))*k*c[k] for k in range(1,kmax+1)]
def vy(y,d): return mp.matrix([[y**i] for i in range(d+1)])
def H(T,d): return mp.matrix([[T[i+j+1] for j in range(d+1)] for i in range(d+1)])
def inertia(Asym):
    ev=mp.eigsy((Asym+Asym.T)/2,eigvals_only=True); tol=mp.mpf(10)**(-40)
    return (sum(1 for e in ev if e>tol),sum(1 for e in ev if e<-tol),sum(1 for e in ev if abs(e)<=tol))
def s_d(T,d):
    H0=H(T,d); vs=vy(Y_STAR,d); Hm=H0-A_STAR*(vs*vs.T)
    inr=inertia(Hm)
    m=(vs.T*mp.inverse(Hm)*vs)[0]
    return A_STAR+1/m, inr

print(f"{'d':>3} | {'s_d(zeta)=A+P':>16} {'inertia':>9} | {'s_d(A only)':>14} {'inertia':>9} | {'s_d(flip A-P)':>16} {'inertia':>9}")
for d in (4,6,8,10,12):
    mp.mp.dps=int(6.5*d)+160
    kmax=2*d+1
    cA,cP=cA_cP(kmax)
    cFull=[None]+[cA[k]+cP[k] for k in range(1,kmax+1)]
    cArch=[None]+[cA[k] for k in range(1,kmax+1)]
    cFlip=[None]+[cA[k]-cP[k] for k in range(1,kmax+1)]
    Tf=Tfrom(cFull,kmax); Ta=Tfrom(cArch,kmax); Tfl=Tfrom(cFlip,kmax)
    sf,inf_=s_d(Tf,d); sa,ina=s_d(Ta,d); sfl,infl=s_d(Tfl,d)
    print(f"{d:>3} | {mp.nstr(sf,8):>16} {str(inf_):>9} | {mp.nstr(sa,8):>14} {str(ina):>9} | {mp.nstr(sfl,8):>16} {str(infl):>9}")

print("""
Reading guide:
 - s_d(zeta) > 0 at all d  ->  RH side, as expected.
 - sign of s_d(flip): if < 0, the prime SIGN is load-bearing (Euler-product positivity keeps s_d>0) -> NR-2 evidence.
 - s_d(A only): whether the archimedean budget alone is positive or already defective (whether the prime CREATES the defect).""")
print("DONE")
