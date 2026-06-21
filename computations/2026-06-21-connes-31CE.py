"""
gpt/31 section 8, remaining computations.
C. Does the prime correction always close the arch surplus? Test |Q_prime[p]| <= Q_zeta+Q_beta for all p:
   i.e. are H^{zb} - H^prime  AND  H^{zb} + H^prime  both PSD?  (H^{zb}=[(-1)^k(ZETA+BETA)_{i+j+1}],
   H^prime=[T^P_{i+j+1}], T^P_k = T_k - (-1)^k S_k^A.)  Report on full space and on u^perp.
E. Compare to FID (the RH-empty integer divisor): H_FID=[zeta(2(i+j)+3)] (y_n=1/n^2, weight n^{-3}).
   Confirm strictly PD (no negative mode ever) and that it has NO pole direction: Q_FID[u] with u=(-4)^i
   is POSITIVE (FID has no s=1 pole), unlike the zero-divisor arch where Q_arch[u]<0. So the arch/pole/(d,1)
   structure and the beta/chi_4 threat are zero-divisor (completed-zeta) specific, not shared with FID.
args: N d dps
"""
import sys, mpmath as mp
N=int(sys.argv[1]) if len(sys.argv)>1 else 200
d=int(sys.argv[2]) if len(sys.argv)>2 else 6
mp.mp.dps=int(sys.argv[3]) if len(sys.argv)>3 else 120
KMAX=2*d+1; q1=mp.mpf(1)/4; q3=mp.mpf(3)/4
with open("/root/gam_cache.txt") as f:
    hdr=f.readline().split(); gam=[mp.mpf(f.readline().strip()) for _ in range(N)]
TN=gam[-1]
def tail(k):
    pp=2*k-1; return (1/mp.pi)*TN**(-pp)/pp*(mp.log(TN/(2*mp.pi))+mp.mpf(1)/pp)
T={k:2*mp.fsum(g**(-2*k) for g in gam)+tail(k) for k in range(1,KMAX+1)}
def SA(k): return 2**(2*k+1)-mp.polygamma(2*k-1,q1)/(2**(2*k)*mp.factorial(2*k-1))
def beta(s): return mp.mpf(4)**(-s)*(mp.zeta(s,q1)-mp.zeta(s,q3))
ZB={k:(-(mp.mpf(1)/2)*(2**(2*k)-1)*mp.zeta(2*k)) + (-mp.mpf(2)**(2*k-1)*beta(2*k)) for k in range(1,KMAX+1)}
TP={k:T[k]-(-1)**k*SA(k) for k in range(1,KMAX+1)}   # prime moments
def mat(seq_signed):  # seq_signed(k) already includes any (-1)^k
    M=mp.matrix(d+1,d+1)
    for i in range(d+1):
        for j in range(d+1): M[i,j]=seq_signed(i+j+1)
    return M
Hzb=mat(lambda k:(-1)**k*ZB[k])
Hpr=mat(lambda k:TP[k])
def mineig(M): return min(mp.eigsy(M,eigvals_only=True))
def inertia(M):
    E=mp.eigsy(M,eigvals_only=True); return sum(1 for e in E if e>0),sum(1 for e in E if e<0)
print(f"# 31-CE, N={N}, d={d}, dps={mp.mp.dps} (cache {hdr[0]}@{hdr[1]})")
# C: full space
print(f"## C: |Q_prime| <= Q_zeta+Q_beta ?")
print(f"  inertia(H^prime) = {inertia(Hpr)}")
print(f"  min eig (H^zb - H^prime) = {mp.nstr(mineig(Hzb-Hpr),5)}   (>=0 => Q_prime <= Q_zb)")
print(f"  min eig (H^zb + H^prime) = {mp.nstr(mineig(Hzb+Hpr),5)}   (>=0 => Q_prime >= -Q_zb)")
# on u^perp
u=[mp.mpf(-4)**i for i in range(d+1)]; nu=mp.sqrt(mp.fsum(x*x for x in u))
basis=[[x/nu for x in u]]
for e in range(d+1):
    v=[mp.mpf(1) if i==e else mp.mpf(0) for i in range(d+1)]
    for b in basis:
        dp=mp.fsum(b[i]*v[i] for i in range(d+1)); v=[v[i]-dp*b[i] for i in range(d+1)]
    nv=mp.sqrt(mp.fsum(x*x for x in v))
    if nv>mp.mpf(10)**(-mp.mp.dps//2): basis.append([x/nv for x in v])
    if len(basis)==d+1: break
Bp=basis[1:]
def restrict(M):
    R=mp.matrix(d,d)
    for a in range(d):
        for b in range(d):
            R[a,b]=mp.fsum(Bp[a][i]*M[i,j]*Bp[b][j] for i in range(d+1) for j in range(d+1))
    return R
print(f"  on u^perp: min eig(H^zb-H^prime|)={mp.nstr(mineig(restrict(Hzb-Hpr)),5)}  min eig(H^zb+H^prime|)={mp.nstr(mineig(restrict(Hzb+Hpr)),5)}")
# E: FID
print(f"## E: FID (integer divisor, RH-empty)")
HF=mp.matrix(d+1,d+1)
for i in range(d+1):
    for j in range(d+1): HF[i,j]=mp.zeta(2*(i+j)+3)
print(f"  inertia(H_FID=[zeta(2(i+j)+3)]) = {inertia(HF)}   (strictly PD, no negative mode ever)")
QFu=mp.fsum(u[i]*u[j]*HF[i,j] for i in range(d+1) for j in range(d+1))
print(f"  Q_FID[u] (u_i=(-4)^i) = {mp.nstr(QFu,6)}   (POSITIVE: FID has no s=1 pole, no -uu^T direction)")
print(f"  contrast zero-divisor arch: Q_arch[u] < 0 (the (d,1) pole). => arch/pole/beta structure is zero-divisor-specific.")
