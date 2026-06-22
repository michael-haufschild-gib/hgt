"""
Reframe the margin as an inverse Christoffel (reproducing-kernel) function of the ZERO measure nu',
extrapolated to the trivial-zero points (gpt/36 #3 Markov/Hardy language; the single-point protector).
nu' moment matrix = [int y^{i+j} dnu'] = [T_{i+j+1}] = H^0. Reproducing kernel at exterior point y_*:
   K(y_*,y_*) = e(y_*)^T (H^0)^{-1} e(y_*) = max_p p(y_*)^2 / Q_0[p],   e(y_*)=(y_*^i).
Protector on the dangerous mode = w_1 p(-0.16)^2, w_1=(2.5)^{-2}=0.16. So predict:
   1/margin = lambda_max(M_triv,H^0) =? w_1*K(-0.16,-0.16)   (single coarsest trivial zero)
and compare to the full kernel sum sum_j w_j K(y_j,y_j). Also K(y_j,y_j) across j (the extrapolation profile).
args: N d dps
"""
import sys, mpmath as mp
N=int(sys.argv[1]) if len(sys.argv)>1 else 250
d=int(sys.argv[2]) if len(sys.argv)>2 else 10
mp.mp.dps=int(sys.argv[3]) if len(sys.argv)>3 else 160
KMAX=2*d+1; q1=mp.mpf(1)/4
with open("/root/gam_cache.txt") as f:
    hdr=f.readline().split(); gam=[mp.mpf(f.readline().strip()) for _ in range(N)]
TN=gam[-1]
def tail(k):
    pp=2*k-1; return (1/mp.pi)*TN**(-pp)/pp*(mp.log(TN/(2*mp.pi))+mp.mpf(1)/pp)
T={k:2*mp.fsum(g**(-2*k) for g in gam)+tail(k) for k in range(1,KMAX+1)}
def maMM(m): return (-1)**m*mp.mpf(2)**(-2*(m+1))*(mp.zeta(2*(m+1),q1)-mp.mpf(4)**(2*(m+1)))
H0=mp.matrix(d+1,d+1); MA=mp.matrix(d+1,d+1)
for i in range(d+1):
    for j in range(d+1): H0[i,j]=T[i+j+1]; MA[i,j]=maMM(i+j)
H0inv=mp.inverse(H0)
def Kdiag(ystar):
    e=mp.matrix([ystar**i for i in range(d+1)])
    return (e.T*H0inv*e)[0,0]
# margin = lambda_min(H0,M_triv); 1/margin = lambda_max(M_triv,H0)
L=mp.cholesky(MA); Li=mp.inverse(L); G=Li*H0*Li.T; G=(G+G.T)/2
margin=min(mp.eigsy(G,eigvals_only=True))
w=lambda j:(2*j+mp.mpf(1)/2)**(-2)
y=lambda j:-(2*j+mp.mpf(1)/2)**(-2)
print(f"# Christoffel reframing, N={N}, d={d}, dps={mp.mp.dps} (cache {hdr[0]}@{hdr[1]})")
print(f"# margin = {mp.nstr(margin,6)}   1/margin = {mp.nstr(1/margin,6)}")
K1=Kdiag(mp.mpf('-0.16'))   # coarsest trivial zero y_1=-(2.5)^-2=-0.16
print(f"# single point: K_nu'(-0.16,-0.16) = {mp.nstr(K1,6)}   w_1*K1 = {mp.nstr(w(1)*K1,6)}   (predict ~ 1/margin)")
full=mp.fsum(w(j)*Kdiag(y(j)) for j in range(1,200))
print(f"# full kernel sum  sum_j w_j K(y_j,y_j) = {mp.nstr(full,6)}   (>= 1/margin, an upper bound)")
print(f"# K(y_j,y_j) extrapolation profile (first trivial zeros):")
for j in range(1,7):
    print(f"   j={j}: y_j={mp.nstr(y(j),4):>9s}  K(y_j,y_j)={mp.nstr(Kdiag(y(j)),5)}")
