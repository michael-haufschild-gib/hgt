"""
gpt/33 #1 + #3.
#1  no-margin law: margin(d)=1-lambda_max(K_d) to high d; per-step ratio r(d)=margin(d)/margin(d-1);
    fit log(r) vs log(gamma_d) to get the exponent (is margin ~ prod gamma_n^{-a}? ~gamma_1^{-4d}?).
#3  kernel structure: K_d = L^{-1}(-R^P)L^{-T} is ALREADY in the mu_triv-orthonormal basis (L=chol(M_triv)).
    Print its entries (d=8) to see if it is near-Jacobi(tridiagonal)/Toeplitz/low-rank/compact.
args: N DMAX dps
"""
import sys, mpmath as mp
N=int(sys.argv[1]) if len(sys.argv)>1 else 250
DMAX=int(sys.argv[2]) if len(sys.argv)>2 else 20
mp.mp.dps=int(sys.argv[3]) if len(sys.argv)>3 else 220
KMAX=2*DMAX+1; q1=mp.mpf(1)/4
with open("/root/gam_cache.txt") as f:
    hdr=f.readline().split(); gam=[mp.mpf(f.readline().strip()) for _ in range(N)]
TN=gam[-1]
def tail(k):
    pp=2*k-1; return (1/mp.pi)*TN**(-pp)/pp*(mp.log(TN/(2*mp.pi))+mp.mpf(1)/pp)
T={k:2*mp.fsum(g**(-2*k) for g in gam)+tail(k) for k in range(1,KMAX+1)}
def maMM(m): return (-1)**m*mp.mpf(2)**(-2*(m+1))*(mp.zeta(2*(m+1),q1)-mp.mpf(4)**(2*(m+1)))
def margin_and_K(d):
    H0=mp.matrix(d+1,d+1); MA=mp.matrix(d+1,d+1)
    for i in range(d+1):
        for j in range(d+1): H0[i,j]=T[i+j+1]; MA[i,j]=maMM(i+j)
    L=mp.cholesky(MA); Li=mp.inverse(L)
    G=Li*H0*Li.T; G=(G+G.T)/2                  # = I - K_d
    gmin=min(mp.eigsy(G,eigvals_only=True))     # = margin = 1-lambda_max(K_d)
    K=mp.eye(d+1)-G
    return gmin,K
print(f"# K asymptotics+structure, N={N}, DMAX={DMAX}, dps={mp.mp.dps} (cache {hdr[0]}@{hdr[1]})")
print(f"## (1) no-margin law")
print(f"#  d   margin            r=margin(d)/margin(d-1)   gamma_d   log(r)/log(1/gamma_d)")
prev=None
logr=[]; loggd=[]
for d in range(2,DMAX+1):
    g,_=margin_and_K(d)
    if prev is not None:
        r=g/prev; gd=gam[d-1]
        expo=mp.log(r)/mp.log(1/gd)
        logr.append(mp.log(r)); loggd.append(mp.log(1/gd))
        print(f"  {d:2d}   {mp.nstr(g,5)}   {mp.nstr(r,5)}   {mp.nstr(gd,5)}   exp~{mp.nstr(expo,4)}")
    prev=g
# overall fit: log(margin_d) vs sum_{n<=d} log(1/gamma_n)  (slope = power 'a' in prod gamma_n^{-a})
S=[]; M=[]; cum=mp.mpf(0); prev=None
for d in range(2,DMAX+1):
    g,_=margin_and_K(d);
    cum=mp.fsum(mp.log(1/gam[n]) for n in range(d))   # sum_{n=0}^{d-1} log(1/gamma_{n+1})
    S.append(cum); M.append(mp.log(g))
# linear fit M ~ a*S + b
ns=len(S); sumS=mp.fsum(S); sumM=mp.fsum(M); sumSS=mp.fsum(s*s for s in S); sumSM=mp.fsum(S[i]*M[i] for i in range(ns))
a=(ns*sumSM-sumS*sumM)/(ns*sumSS-sumS*sumS)
print(f"# FIT: log(margin) ~ a * sum_n log(1/gamma_n) + b  =>  margin ~ prod_n gamma_n^(-a),  a = {mp.nstr(a,6)}")
print(f"##  (3) K_d structure in mu_triv-orthonormal basis (d=8): entries K[i,j]")
_,K=margin_and_K(8)
for i in range(9):
    print("   "+" ".join(f"{mp.nstr(K[i,j],3):>9s}" for j in range(9)))
