"""
Where in the Christoffel function K_nu'(-0.16,-0.16)=e^T(H^0)^{-1}e does RH content sit?
Split: K_d ~ prefactor * exp(2 d * g),  g = Green's function of C\supp(nu') (endpoint-determined, GENERIC).
Compare zeta vs a synthetic same-support divisor (linear gamma_n = gamma_1 * n: same y_1=gamma_1^{-2}, same
accumulation at 0, DIFFERENT internal density). If the RATE K^{1/(2d)} matches -> rate generic (endpoint).
The PREFACTOR (K_d / rate^{2d}) is then where any zeta signature lives.
Report per d: rate_zeta=K^{1/(2d)}, rate_lin, ratio; and the d-growth of each.
args: N DMAX dps
"""
import sys, mpmath as mp
N=int(sys.argv[1]) if len(sys.argv)>1 else 250
DMAX=int(sys.argv[2]) if len(sys.argv)>2 else 14
mp.mp.dps=int(sys.argv[3]) if len(sys.argv)>3 else 170
KMAX=2*DMAX+1
with open("/root/gam_cache.txt") as f:
    hdr=f.readline().split(); gz=[mp.mpf(f.readline().strip()) for _ in range(N)]
g1=gz[0]
g_lin=[g1*(n+1) for n in range(N)]
TN=gz[-1]
def tail(gam,k):
    t=gam[-1]; pp=2*k-1; return (1/mp.pi)*t**(-pp)/pp*(mp.log(t/(2*mp.pi))+mp.mpf(1)/pp)
def Tk(gam,k,zeta_tail):
    s=2*mp.fsum(g**(-2*k) for g in gam)
    return s+(tail(gam,k) if zeta_tail else 0)
ystar=mp.mpf('-0.16')
def Kdiag(gam,d,zeta_tail):
    H=mp.matrix(d+1,d+1)
    for i in range(d+1):
        for j in range(d+1): H[i,j]=Tk(gam,i+j+1,zeta_tail)
    Hi=mp.inverse(H); e=mp.matrix([ystar**i for i in range(d+1)])
    return (e.T*Hi*e)[0,0]
print(f"# Christoffel prefactor, N={N}, DMAX={DMAX}, dps={mp.mp.dps} (cache {hdr[0]}@{hdr[1]})")
print(f"#  d    rate_zeta=K^(1/2d)   rate_linear        ratio z/lin")
for d in range(2,DMAX+1):
    Kz=Kdiag(gz,d,True); Kl=Kdiag(g_lin,d,False)
    rz=Kz**(mp.mpf(1)/(2*d)); rl=Kl**(mp.mpf(1)/(2*d))
    print(f"  {d:2d}   {mp.nstr(rz,8):>14s}   {mp.nstr(rl,8):>14s}   {mp.nstr(rz/rl,6)}")
