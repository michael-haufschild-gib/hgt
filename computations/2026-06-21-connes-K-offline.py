"""
gpt/33 #7: synthetic off-line zero under the relative operator K_d. M_triv is arch (trivial zeros),
INDEPENDENT of the injection; only H^0 (hence R^P=H^0-M_triv) changes. So
   lambda_max(K_d) = 1 - lambda_min(L^{-1} H^0_perturbed L^{-T}),  M_triv=LL^T.
RH-faithfulness => lambda_max(K_d) crosses 1 exactly when the off-line zero is detected. Scan beta at
fixed (d, gamma0) and watch the crossing; this shows K_d is the clean off-line detector in operator form.
args: N d gamma0 dps
"""
import sys, mpmath as mp
N=int(sys.argv[1]) if len(sys.argv)>1 else 250
d=int(sys.argv[2]) if len(sys.argv)>2 else 10
g0=mp.mpf(sys.argv[3]) if len(sys.argv)>3 else mp.mpf(20)
mp.mp.dps=int(sys.argv[4]) if len(sys.argv)>4 else 160
KMAX=2*d+1; q1=mp.mpf(1)/4
with open("/root/gam_cache.txt") as f:
    hdr=f.readline().split(); gam=[mp.mpf(f.readline().strip()) for _ in range(N)]
TN=gam[-1]
def tail(k):
    pp=2*k-1; return (1/mp.pi)*TN**(-pp)/pp*(mp.log(TN/(2*mp.pi))+mp.mpf(1)/pp)
Tb={k:2*mp.fsum(g**(-2*k) for g in gam)+tail(k) for k in range(1,KMAX+1)}
def maMM(m): return (-1)**m*mp.mpf(2)**(-2*(m+1))*(mp.zeta(2*(m+1),q1)-mp.mpf(4)**(2*(m+1)))
MA=mp.matrix(d+1,d+1)
for i in range(d+1):
    for j in range(d+1): MA[i,j]=maMM(i+j)
L=mp.cholesky(MA); Li=mp.inverse(L)
def lammax_K(Td):
    H0=mp.matrix(d+1,d+1)
    for i in range(d+1):
        for j in range(d+1): H0[i,j]=Td[i+j+1]
    G=Li*H0*Li.T; G=(G+G.T)/2
    return 1-min(mp.eigsy(G,eigvals_only=True))
print(f"# K_d off-line detector, N={N}, d={d}, gamma0={mp.nstr(g0,5)}, dps={mp.mp.dps} (cache {hdr[0]}@{hdr[1]})")
print(f"#  beta      lambda_max(K_d)            detected (lambda_max>1)?")
for bv in ['0.0','0.02','0.05','0.1','0.2','0.4']:
    beta=mp.mpf(bv); wo=mp.mpc(beta,g0); yo=-1/wo**2; yb=mp.conj(yo)
    Tp={k:mp.re(Tb[k]+2*(yo**k+yb**k)) for k in range(1,KMAX+1)}
    lm=lammax_K(Tp)
    print(f"  {bv:>5s}   {mp.nstr(lm,18)}   {'YES (off-line detected)' if lm>1 else 'no'}")
