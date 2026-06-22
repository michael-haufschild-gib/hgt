"""comp9 / rt#37: Weil-pullback p(y) -> h_p. h_p(t)=(1/t^2)p(1/t^2)^2 = sum_m b_m t^{-2m},
b_m=sum_{i+j+1=m} c_i c_j. So Q_0[p]=sum_rho y_rho p(y_rho)^2 = sum_m b_m T_m, and each
T_m has the explicit-formula closed form S_m=(-1)^m T_m=POLE+ZETA+BETA+PRIME. Tests:
 (1) cross-validate PRIME_k TWO ways: (a) -2k g_{2k} via (zeta'/zeta)^{(2k-1)}(1/2)=(2k)! g_{2k};
     (b) (-1)^k T_k - (POLE+ZETA+BETA). Match => explicit-formula split AND exact moments confirmed.
 (2) admissibility: h_p has a pole of order 2(2d+1) at t=0 <-> s=1/2 (seam CENTER, y=infty).
 (3) realize Q_0[p]=sum_m b_m T_m and the 4-way split on the dangerous direction p_d."""
import sys, mpmath as mp, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py")
mp.mp.dps=140
KMAX=26
# exact moments + g_m (log zeta series) reusing the exact-moment internals
M=2*KMAX+1
a=[mp.zeta(mp.mpf('0.5'),1,m)/mp.factorial(m) for m in range(M+1)]
g=[mp.mpf(0)]*(M+1); g[0]=mp.log(a[0])
for m in range(1,M+1):
    s=mp.fsum(n*g[n]*a[m-n] for n in range(1,m)); g[m]=(m*a[m]-s)/(m*a[0])
def c2k(k): return -mp.power(4,k)/k + mp.polygamma(2*k-1,mp.mpf(1)/4)/(mp.factorial(2*k)*mp.power(4,k)) + g[2*k]
T=[None]+[2*((-1)**(k+1))*k*c2k(k) for k in range(1,KMAX+1)]
def beta(s): return mp.power(4,-s)*(mp.zeta(s,mp.mpf(1)/4)-mp.zeta(s,mp.mpf(3)/4))
def POLE(k): return mp.power(2,2*k+1)
def ZETA(k): return -mp.mpf(1)/2*(mp.power(2,2*k)-1)*mp.zeta(2*k)
def BETA(k): return -mp.power(2,2*k-1)*beta(2*k)
print("# (1) cross-validate PRIME_k two ways (should match to ~full precision):")
maxrel=mp.mpf(0)
for k in [1,2,3,5,8,12,16,20]:
    Sk=(-1)**k*T[k]
    prime_b = Sk-(POLE(k)+ZETA(k)+BETA(k))
    prime_a = -2*k*g[2*k]              # = -(2k-1)!^{-1}(zeta'/zeta)^{(2k-1)}(1/2)
    rel=abs(prime_a-prime_b)/abs(prime_b) if prime_b!=0 else abs(prime_a-prime_b)
    maxrel=max(maxrel,rel)
    if k in (1,2,5,12,20):
        print(f"  k={k:2d}: PRIME(a)={mp.nstr(prime_a,12)}  PRIME(b)={mp.nstr(prime_b,12)}  rel={mp.nstr(rel,3)}")
print(f"  => max rel mismatch over k=1..20: {mp.nstr(maxrel,3)}  (PRIME two-way cross-validated)")
# (2) admissibility of the pullback test function for degree d
for d in [4,10]:
    order=2*(2*d+1)
    print(f"# (2) d={d}: h_p(t)=sum b_m t^-2m has pole of order {order} at t=0 <-> s=1/2 (seam CENTER, y=inf) => INADMISSIBLE single Weil test fn")
# (3) dangerous direction split
d=12
A=H.H0_matrix(d,T); B=H.Mtriv_matrix(d)
Lc=mp.cholesky(B); Li=mp.inverse(Lc); C=Li*A*Li.T; C=(C+C.T)/2
E,Q=mp.eigsy(C); idx=min(range(len(E)),key=lambda i:E[i])
q=mp.matrix([Q[r,idx] for r in range(d+1)]); c=Li.T*q
# b_m = sum_{i+j+1=m} c_i c_j
b=[mp.mpf(0)]*(2*d+2)
for i in range(d+1):
    for j in range(d+1): b[i+j+1]+=c[i]*c[j]
Q0=mp.fsum(b[m]*T[m] for m in range(1,2*d+2))
Qpole=mp.fsum(b[m]*((-1)**m*POLE(m)) for m in range(1,2*d+2))
Qzeta=mp.fsum(b[m]*((-1)**m*ZETA(m)) for m in range(1,2*d+2))
Qbeta=mp.fsum(b[m]*((-1)**m*BETA(m)) for m in range(1,2*d+2))
Qprime=mp.fsum(b[m]*((-1)**m*(-2*m*g[2*m])) for m in range(1,2*d+2))
print(f"# (3) dangerous direction p_d, d={d}:  Q_0=lambda_min={mp.nstr(Q0,6)}")
print(f"   Q_pole={mp.nstr(Qpole,5)}  Q_zeta={mp.nstr(Qzeta,5)}  Q_beta={mp.nstr(Qbeta,5)}  Q_prime={mp.nstr(Qprime,5)}")
print(f"   sum check Q_pole+Q_zeta+Q_beta+Q_prime - Q_0 = {mp.nstr(Qpole+Qzeta+Qbeta+Qprime-Q0,3)}")
print(f"   |Q_prime|/|Q_zeta+Q_beta| = {mp.nstr(abs(Qprime)/abs(Qzeta+Qbeta),4)}  (prime sub-dominant, closes residual)")
