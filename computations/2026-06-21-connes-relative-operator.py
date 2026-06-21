"""
gpt/32 section 9: the relative operator K_d = M_triv^{-1/2}(-R^P)M_triv^{-1/2}.
Bridge theorem (one-sided Loewner domination):  -R^P <= M_triv  <=>  lambda_max(K_d) <= 1  for all d.
Since Q_0 = M_triv + R^P, we have L^{-1}Q_0 L^{-T} = I - K_d (M_triv=LL^T Cholesky), so
   lambda_max(K_d) = 1 - lambda_min(Q_0 rel M_triv).
Track lambda_max(K_d) vs d: does it -> 1^- (the no-margin RH wall)? Also the extremizing polynomial's
overlap with the pole vector u and with the dangerous direction p_d.
args: N DMAX dps
"""
import sys, mpmath as mp
N=int(sys.argv[1]) if len(sys.argv)>1 else 200
DMAX=int(sys.argv[2]) if len(sys.argv)>2 else 8
mp.mp.dps=int(sys.argv[3]) if len(sys.argv)>3 else 140
KMAX=2*DMAX+1; q1=mp.mpf(1)/4
with open("/root/gam_cache.txt") as f:
    hdr=f.readline().split(); gam=[mp.mpf(f.readline().strip()) for _ in range(N)]
TN=gam[-1]
def tail(k):
    pp=2*k-1; return (1/mp.pi)*TN**(-pp)/pp*(mp.log(TN/(2*mp.pi))+mp.mpf(1)/pp)
T={k:2*mp.fsum(g**(-2*k) for g in gam)+tail(k) for k in range(1,KMAX+1)}
def maMM(m):  # M^A[i,j] with m=i+j : int y^m dmu_triv (Hurwitz-exact)
    return (-1)**m*mp.mpf(2)**(-2*(m+1))*(mp.zeta(2*(m+1),q1)-mp.mpf(4)**(2*(m+1)))
print(f"# relative operator K_d, N={N}, DMAX={DMAX}, dps={mp.mp.dps} (cache {hdr[0]}@{hdr[1]})")
print(f"#  d   lambda_max(K_d)            1-lambda_max (= gen. margin)     |<argmax,u>|  |<argmax,p_d>|")
for d in range(2,DMAX+1):
    H0=mp.matrix(d+1,d+1); MA=mp.matrix(d+1,d+1)
    for i in range(d+1):
        for j in range(d+1):
            H0[i,j]=T[i+j+1]; MA[i,j]=maMM(i+j)
    RP=H0-MA
    L=mp.cholesky(MA)                      # MA = L L^T
    Linv=mp.inverse(L)
    K=Linv*(-RP)*Linv.T                    # symmetric relative operator
    K=(K+K.T)/2
    E,V=mp.eigsy(K)
    lam=E[d]                               # largest eigenvalue
    # extremizing polynomial: x = argmax of K; p-coeffs c = L^{-T} x
    x=[V[i,d] for i in range(d+1)]
    c=[mp.fsum(Linv.T[i,j]*x[j] for j in range(d+1)) for i in range(d+1)]
    nc=mp.sqrt(mp.fsum(ci*ci for ci in c)); c=[ci/nc for ci in c]
    u=[mp.mpf(-4)**i for i in range(d+1)]; nu=mp.sqrt(mp.fsum(z*z for z in u))
    ovu=abs(mp.fsum(c[i]*u[i]/nu for i in range(d+1)))
    # dangerous direction p_d = lambda_min eigvec of H0
    _,Vh=mp.eigsy(H0); pd=[Vh[i,0] for i in range(d+1)]; npd=mp.sqrt(mp.fsum(z*z for z in pd))
    ovp=abs(mp.fsum(c[i]*pd[i]/npd for i in range(d+1)))
    print(f"  {d}   {mp.nstr(lam,18)}   {mp.nstr(1-lam,10)}   {mp.nstr(ovu,5)}   {mp.nstr(ovp,5)}")
