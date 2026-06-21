"""
Fused four-way split of Q_0[p_d] for the most-dangerous direction p_d (lambda_min eigvec of H_0).
Fused closed form (all-rho normalization, = 2x the orbit seam-note form):
  S_k = POLE_k + ZETA_k + BETA_k + PRIME_k
  POLE_k = 2^{2k+1}                          (the s=1 pole leading term)
  ZETA_k = -1/2 (2^{2k}-1) zeta(2k)          (even-zeta archimedean)
  BETA_k = -2^{2k-1} beta(2k)                (Dirichlet beta / Catalan)
  PRIME_k = (-1)^k T_k - (POLE+ZETA+BETA)_k  (prime side = zero-side minus arch; = -(1/(2k-1)!)(zeta'/zeta)^{(2k-1)}(1/2))
beta(2k) via Hurwitz: 4^{-2k}(zeta(2k,1/4)-zeta(2k,3/4)).
T^X_k=(-1)^k S^X_k; H^X=[T^X_{i+j+1}]; evaluate each on p_d.
Cross-checks: (a) POLE+ZETA+BETA vs polygamma S_k^A; (b) sum of the four Q_X[p_d] vs lambda_min.
Question: in the residual (after the POLE cancellation), which term protects positivity?
args: N d dps
"""
import sys, mpmath as mp
N=int(sys.argv[1]) if len(sys.argv)>1 else 200
d=int(sys.argv[2]) if len(sys.argv)>2 else 6
mp.mp.dps=int(sys.argv[3]) if len(sys.argv)>3 else 120
KMAX=2*d+1
with open("/root/gam_cache.txt") as f:
    hdr=f.readline().split(); gam=[mp.mpf(f.readline().strip()) for _ in range(N)]
TN=gam[-1]
def tail(k):
    p=2*k-1; return (1/mp.pi)*TN**(-p)/p*(mp.log(TN/(2*mp.pi))+mp.mpf(1)/p)
T={k:2*mp.fsum(g**(-2*k) for g in gam)+tail(k) for k in range(1,KMAX+1)}
half=mp.mpf(1)/2; q1=mp.mpf(1)/4; q3=mp.mpf(3)/4
def beta(s): return mp.mpf(4)**(-s)*(mp.zeta(s,q1)-mp.zeta(s,q3))
def SA_poly(k): return 2**(2*k+1)-mp.polygamma(2*k-1,q1)/(2**(2*k)*mp.factorial(2*k-1))
POLE={k:mp.mpf(2)**(2*k+1) for k in range(1,KMAX+1)}
ZETA={k:-half*(2**(2*k)-1)*mp.zeta(2*k) for k in range(1,KMAX+1)}
BETA={k:-mp.mpf(2)**(2*k-1)*beta(2*k) for k in range(1,KMAX+1)}
SA={k:POLE[k]+ZETA[k]+BETA[k] for k in range(1,KMAX+1)}
PRIME={k:(-1)**k*T[k]-SA[k] for k in range(1,KMAX+1)}
# cross-check arch closed form
xcA=max(abs(SA[k]-SA_poly(k))/abs(SA_poly(k)) for k in (1,2,KMAX))
def Hk(S):  # build H^X from S^X (T^X_k=(-1)^k S^X_k)
    H=mp.matrix(d+1,d+1)
    for i in range(d+1):
        for j in range(d+1):
            k=i+j+1; H[i,j]=(-1)**k*S[k]
    return H
HP={k:POLE[k] for k in range(1,KMAX+1)}
H0=Hk({k:(-1)**k*T[k] for k in range(1,KMAX+1)})  # = [T_{i+j+1}]
HPOLE=Hk(POLE); HZETA=Hk(ZETA); HBETA=Hk(BETA); HPRIME=Hk(PRIME)
def formv(H,v): return mp.fsum(v[i]*v[j]*H[i,j] for i in range(d+1) for j in range(d+1))
def report(v,tag):
    Qp=formv(HPOLE,v); Qz=formv(HZETA,v); Qb=formv(HBETA,v); Qr=formv(HPRIME,v); Q0=formv(H0,v)
    print(f"--- {tag} ---")
    print(f"  Q_0          = {mp.nstr(Q0,6)}")
    print(f"  Q_pole       = {mp.nstr(Qp,8)}")
    print(f"  Q_zeta       = {mp.nstr(Qz,8)}")
    print(f"  Q_beta       = {mp.nstr(Qb,8)}")
    print(f"  Q_prime      = {mp.nstr(Qr,8)}")
    print(f"  sum 4        = {mp.nstr(Qp+Qz+Qb+Qr,8)}  (vs Q_0)")
    print(f"  residual Q_0-Q_pole = zeta+beta+prime = {mp.nstr(Qz+Qb+Qr,8)}")
    if abs(Qr)>0:
        print(f"  within residual shares: zeta/|res|={mp.nstr(Qz/(Qz+Qb+Qr),5)} beta={mp.nstr(Qb/(Qz+Qb+Qr),5)} prime={mp.nstr(Qr/(Qz+Qb+Qr),5)}")
    return Qz,Qb,Qr
# (1) full most-dangerous direction p_d
E,V=mp.eigsy(H0); pd=[V[i,0] for i in range(d+1)]
print(f"# fused split of the dangerous directions, N={N}, d={d}, dps={mp.mp.dps} (cache {hdr[0]}@{hdr[1]})")
print(f"# arch cross-check POLE+ZETA+BETA vs polygamma S_k^A: max rel err = {mp.nstr(xcA,3)}")
report(pd,"p_d = lambda_min eigvec of full H_0 (=0.97 u, pole-dominated)")
# (2) most-dangerous direction WITHIN u^perp (pole removed -> the genuine residual / Part B)
u=[mp.mpf(-4)**i for i in range(d+1)]; nu=mp.sqrt(mp.fsum(x*x for x in u)); uh=[x/nu for x in u]
B=[[mp.mpf(1) if i==e else mp.mpf(0) for i in range(d+1)] for e in range(d+1)]  # std basis
# Gram-Schmidt to u^perp
basis=[uh]
for e in range(d+1):
    v=[mp.mpf(1) if i==e else mp.mpf(0) for i in range(d+1)]
    for bb in basis:
        dp=mp.fsum(bb[i]*v[i] for i in range(d+1)); v=[v[i]-dp*bb[i] for i in range(d+1)]
    nv=mp.sqrt(mp.fsum(x*x for x in v))
    if nv>mp.mpf(10)**(-mp.mp.dps//2): basis.append([x/nv for x in v])
    if len(basis)==d+1: break
Bp=basis[1:]  # orthonormal basis of u^perp (d vectors)
# H_0 restricted to u^perp, its lambda_min eigenvector, lifted back
Hr=mp.matrix(d,d)
for a in range(d):
    for b in range(d):
        Hr[a,b]=mp.fsum(Bp[a][i]*H0[i,j]*Bp[b][j] for i in range(d+1) for j in range(d+1))
Er,Vr=mp.eigsy(Hr); cr=[Vr[a,0] for a in range(d)]
pperp=[mp.fsum(cr[a]*Bp[a][i] for a in range(d)) for i in range(d+1)]  # lift to R^{d+1}, in u^perp
report(pperp,"p_d^perp = lambda_min of H_0|u^perp  (p(-4)=0, the genuine residual / Part B)")
print(f"#   check p(-4)=<pperp,u_unnorm> = {mp.nstr(mp.fsum(pperp[i]*(mp.mpf(-4)**i) for i in range(d+1)),4)} (should be ~0)")
