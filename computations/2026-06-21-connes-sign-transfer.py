"""
gpt/35 #C + #D: the SIGN, not the rate.
G_d := L^{-1} Q_0 L^{-T}  (M_triv=LL^T) = I - K_d. Generalized eigenvalues of (Q_0,M_triv).
margin = lambda_min(G_d). RH <=> lambda_min(G_d)>0 for all d.
#C off-line crossing: inject an off-line quartet at gamma0 (d>d*), scan beta, and count how many
   eigenvalues of G_d go negative. Hypothesis (factor-by-factor): EXACTLY ONE crosses 0 -> lambda_max(K_d)>1.
#D factorization: at beta=0, compare the Cholesky pivots of G_d (the 'factors' whose product = det G_d
   = det Q_0/det M_triv) to the per-step margin ratios ~ gamma_n^{-3.40}.
args: N d gamma0 dps
"""
import sys, mpmath as mp
N=int(sys.argv[1]) if len(sys.argv)>1 else 250
d=int(sys.argv[2]) if len(sys.argv)>2 else 10
g0=mp.mpf(sys.argv[3]) if len(sys.argv)>3 else mp.mpf(20)
mp.mp.dps=int(sys.argv[4]) if len(sys.argv)>4 else 170
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
def Gmat(Td):
    H0=mp.matrix(d+1,d+1)
    for i in range(d+1):
        for j in range(d+1): H0[i,j]=Td[i+j+1]
    G=Li*H0*Li.T; return (G+G.T)/2
print(f"# sign transfer, N={N}, d={d}, gamma0={mp.nstr(g0,5)}, dps={mp.mp.dps} (cache {hdr[0]}@{hdr[1]})")
print(f"## C: off-line crossing -- how many eigenvalues of G_d go negative?")
print(f"#  beta     #neg eig   two smallest eigenvalues of G_d")
for bv in ['0.0','0.02','0.05','0.1','0.2','0.4']:
    beta=mp.mpf(bv); wo=mp.mpc(beta,g0); yo=-1/wo**2; yb=mp.conj(yo)
    Tp={k:mp.re(Tb[k]+2*(yo**k+yb**k)) for k in range(1,KMAX+1)}
    E=mp.eigsy(Gmat(Tp),eigvals_only=True)
    nneg=sum(1 for e in E if e<0)
    print(f"  {bv:>5s}    {nneg:2d}       {mp.nstr(E[0],5)}  ,  {mp.nstr(E[1],5)}")
print(f"## D: Cholesky pivots of G_d (beta=0) vs per-step margin ratios gamma_n^-exp")
G0=Gmat(Tb)
Lg=mp.cholesky(G0)
piv=[Lg[i,i]**2 for i in range(d+1)]   # pivots (product = det G0)
print(f"#  n   pivot              gamma_n     log(pivot)/log(1/gamma_n)")
for n in range(d+1):
    gd=gam[n] if n<N else mp.mpf(0)
    e=mp.log(piv[n])/mp.log(1/gd) if n>=1 else mp.mpf(0)
    print(f"  {n:2d}   {mp.nstr(piv[n],6):>12s}   {mp.nstr(gd,5):>7s}    {mp.nstr(e,4) if n>=1 else '-'}")
