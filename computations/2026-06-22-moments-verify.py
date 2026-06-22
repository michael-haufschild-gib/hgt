"""Verify exact zero-moments T_k = 2 sum gamma^{-2k} via log Xi Taylor coeffs.
c_{2k}=[w^{2k}] log Xi(w), Xi(w)=xi(1/2+w). Pieces:
 log Xi = log(1-4w^2) + logGamma(1/4+w/2) + log zeta(1/2+w) + const(+odd).
 [w^{2k}]log(1-4w^2) = -4^k/k
 [w^{2k}]logGamma(1/4+w/2) = polygamma(2k-1,1/4)/((2k)! 4^k)
 [w^{2k}]log zeta(1/2+w) = g_{2k} via log-of-series recurrence from a_m=zeta^{(m)}(1/2)/m!
 T_k = 2(-1)^{k+1} k c_{2k}.   Cross-check vs truncated-zeros sum."""
import time, mpmath as mp
mp.mp.dps=120
KMAX=12
M=2*KMAX+1
t=time.time()
# a_m = zeta^{(m)}(1/2)/m!  -- test mp.zeta derivative speed
a=[]
for m in range(M+1):
    a.append(mp.zeta(mp.mpf('0.5'),1,m)/mp.factorial(m))
t_a=time.time()-t
# g_m = [w^m] log zeta(1/2+w): m a_m = sum_{n=1}^m n g_n a_{m-n}
g=[mp.mpf(0)]*(M+1)
g[0]=mp.log(a[0])
for m in range(1,M+1):
    s=sum(n*g[n]*a[m-n] for n in range(1,m))
    g[m]=(m*a[m]-s)/(m*a[0])
def c2k(k):
    return -mp.power(4,k)/k + mp.polygamma(2*k-1,mp.mpf(1)/4)/(mp.factorial(2*k)*mp.power(4,k)) + g[2*k]
def Tk(k):
    return 2*((-1)**(k+1))*k*c2k(k)
print(f"a_m time {t_a:.1f}s")
# truncated cross-check
g80=[mp.mpf(x.strip()) for x in open('zeros.txt')][:80]
for k in [1,2,3,4,6,8,12]:
    Te=Tk(k)
    Ttr=2*mp.fsum((1/(gm*gm))**k for gm in g80)
    print(f"k={k:2d}  T_k(exact)={mp.nstr(Te,18)}   T_k(80-trunc)={mp.nstr(Ttr,18)}   reldiff={mp.nstr(abs(Te-Ttr)/abs(Te),3)}")
