"""
The race that localizes RH: on-line margin decay  vs  off-line detection reach.
(1) Margin decay: 1-lambda_max(K_d) for d=2..DMAX, fit log10 slope (the on-line hard-edge rate).
(2) Detection law d*(gamma0): inject a synthetic off-line quartet at height gamma0 (real part beta) into
    the on-line bulk, find the smallest degree d with lambda_min([T_{i+j+1}])<0. Fit d* vs gamma0.
Then: any off-line zero sits above the RH verification height H, so d*(>H) bounds the unconditional range
det H_d>0 for d<d*(H).
args: N DMAX dps beta
"""
import sys, mpmath as mp
N=int(sys.argv[1]) if len(sys.argv)>1 else 200
DMAX=int(sys.argv[2]) if len(sys.argv)>2 else 8
mp.mp.dps=int(sys.argv[3]) if len(sys.argv)>3 else 140
beta=mp.mpf(sys.argv[4]) if len(sys.argv)>4 else mp.mpf('0.1')
q1=mp.mpf(1)/4
with open("/root/gam_cache.txt") as f:
    hdr=f.readline().split(); gam=[mp.mpf(f.readline().strip()) for _ in range(N)]
TN=gam[-1]
def tail(k):
    pp=2*k-1; return (1/mp.pi)*TN**(-pp)/pp*(mp.log(TN/(2*mp.pi))+mp.mpf(1)/pp)
def Tbulk(k): return 2*mp.fsum(g**(-2*k) for g in gam)+tail(k)
KMAX=2*DMAX+1
Tb={k:Tbulk(k) for k in range(1,KMAX+1)}
def maMM(m): return (-1)**m*mp.mpf(2)**(-2*(m+1))*(mp.zeta(2*(m+1),q1)-mp.mpf(4)**(2*(m+1)))
def lmin_H(d,Td):
    H=mp.matrix(d+1,d+1)
    for i in range(d+1):
        for j in range(d+1): H[i,j]=Td[i+j+1]
    return min(mp.eigsy(H,eigvals_only=True))
# (1) margin decay
print(f"# detection law, N={N}, DMAX={DMAX}, dps={mp.mp.dps}, beta={mp.nstr(beta,3)} (cache {hdr[0]}@{hdr[1]})")
print(f"## (1) on-line margin 1-lambda_max(K_d):")
prev=None
for d in range(2,DMAX+1):
    H0=mp.matrix(d+1,d+1); MA=mp.matrix(d+1,d+1)
    for i in range(d+1):
        for j in range(d+1): H0[i,j]=Tb[i+j+1]; MA[i,j]=maMM(i+j)
    L=mp.cholesky(MA); Li=mp.inverse(L); K=Li*(H0-MA)*Li.T   # note: K_d eig of M^{-1/2}(-R^P) ... here use I-(L^-1 Q0 L^-T)
    G=Li*H0*Li.T; G=(G+G.T)/2; gmin=min(mp.eigsy(G,eigvals_only=True))   # gmin = 1-lambda_max(K_d) = gen margin
    sl="" if prev is None else f"  dlog10/dd={mp.nstr((mp.log10(gmin)-mp.log10(prev)),4)}"
    print(f"   d={d}: margin={mp.nstr(gmin,6)}{sl}")
    prev=gmin
# (2) detection law d*(gamma0)
print(f"## (2) detection threshold d*(gamma0)  [inject off-line quartet, find first d with lambda_min<0]:")
import math
for g0v in [20,30,45,60,80,110,150]:
    g0=mp.mpf(g0v); wo=mp.mpc(beta,g0); yo=-1/wo**2; yb=mp.conj(yo)
    Tp={k:Tb[k]+2*(yo**k+yb**k) for k in range(1,KMAX+1)}
    Tp={k:mp.re(Tp[k]) for k in Tp}
    dstar=None
    for d in range(1,DMAX+1):
        if lmin_H(d,Tp)<0: dstar=d; break
    Nt=(g0/(2*mp.pi))*mp.log(g0/(2*mp.pi))-g0/(2*mp.pi)+mp.mpf(7)/8   # Riemann-vM zero count
    rec=f"d*={dstar}" if dstar else f"d*>{DMAX}"
    print(f"   gamma0={g0v:4d}: {rec:8s}  gamma0/3={mp.nstr(g0/3,4)}  N(gamma0)={mp.nstr(Nt,4)}")
