"""
Derive the no-margin exponent (~3.40) from the hard-edge densities.
margin(d)=lambda_min(Q_0,M_triv). Claim: per-step margin ratio ~ h_d(nu')/h_d(mu_triv), where
h_d(mu)=det H_d(mu)/det H_{d-1}(mu) is the d-th orthogonal-polynomial norm.
nu'  density ~ |log y| y^{-1/2} on (0,y_1]   (the zero measure, dnu'=2y_rho delta)
mu_triv density ~ |y|^{-1/2} on [y_1^triv,0)  (the trivial-zero measure)
Both hard-edge |y|^{-1/2}; the per-step EXPONENTS (in 1/gamma_d) decompose the 3.40.
Reports per d: h_d^Q, h_d^M, ratio; their exponents vs 1/gamma_d; and margin(d)/margin(d-1) for comparison.
args: N DMAX dps
"""
import sys, mpmath as mp
N=int(sys.argv[1]) if len(sys.argv)>1 else 250
DMAX=int(sys.argv[2]) if len(sys.argv)>2 else 16
mp.mp.dps=int(sys.argv[3]) if len(sys.argv)>3 else 240
KMAX=2*DMAX+1; q1=mp.mpf(1)/4
with open("/root/gam_cache.txt") as f:
    hdr=f.readline().split(); gam=[mp.mpf(f.readline().strip()) for _ in range(N)]
TN=gam[-1]
def tail(k):
    pp=2*k-1; return (1/mp.pi)*TN**(-pp)/pp*(mp.log(TN/(2*mp.pi))+mp.mpf(1)/pp)
T={k:2*mp.fsum(g**(-2*k) for g in gam)+tail(k) for k in range(1,KMAX+1)}
def maMM(m): return (-1)**m*mp.mpf(2)**(-2*(m+1))*(mp.zeta(2*(m+1),q1)-mp.mpf(4)**(2*(m+1)))
def detsub(getter,d):
    H=mp.matrix(d+1,d+1)
    for i in range(d+1):
        for j in range(d+1): H[i,j]=getter(i,j)
    return mp.det(H)
def margin(d):
    H0=mp.matrix(d+1,d+1); MA=mp.matrix(d+1,d+1)
    for i in range(d+1):
        for j in range(d+1): H0[i,j]=T[i+j+1]; MA[i,j]=maMM(i+j)
    L=mp.cholesky(MA); Li=mp.inverse(L); G=Li*H0*Li.T; G=(G+G.T)/2
    return min(mp.eigsy(G,eigvals_only=True))
getQ=lambda i,j:T[i+j+1]; getM=lambda i,j:maMM(i+j)
print(f"# exponent derivation, N={N}, DMAX={DMAX}, dps={mp.mp.dps} (cache {hdr[0]}@{hdr[1]})")
print(f"#  d  gamma_d   h_d(nu')exp  h_d(mu)exp  ratio_exp   margin_ratio_exp   (exp = log(.)/log(1/gamma_d))")
dQ=[detsub(getQ,d) for d in range(0,DMAX+1)]
dM=[detsub(getM,d) for d in range(0,DMAX+1)]
mg=[margin(d) for d in range(1,DMAX+1)]   # index d-1
for d in range(2,DMAX+1):
    gd=gam[d-1]; lg=mp.log(1/gd)
    hQ=dQ[d]/dQ[d-1]; hM=dM[d]/dM[d-1]; ratio=hQ/hM
    mr=mg[d-1]/mg[d-2]
    eQ=mp.log(abs(hQ))/lg; eM=mp.log(abs(hM))/lg; er=mp.log(abs(ratio))/lg; emr=mp.log(abs(mr))/lg
    print(f"  {d:2d}  {mp.nstr(gd,5):>7s}  {mp.nstr(eQ,4):>9s}  {mp.nstr(eM,4):>9s}  {mp.nstr(er,4):>8s}  {mp.nstr(emr,4):>8s}")
# overall density-fit: h_d(nu') ~ prod? compare exponents to predictions
print(f"# NB: nu' weight 2y~gamma^-2 (exp 2) x hard-edge resolution; mu_triv hard-edge only.")
print(f"# ratio_exp should match margin_ratio_exp (~3.40) and equals h_d(nu')exp - h_d(mu)exp.")
