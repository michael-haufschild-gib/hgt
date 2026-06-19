# Exact decay test for the x=1-centered moment-killing construction for gamma_E.
# P_n = sum_{i=0..n} c_i (x-1)^i,  with  int P_n (x-1)^j e^{-x} dx = [j==0]  for j=0..n.
# Then int P_n e^{-x} = 1 (gamma retained, Cor 6.2), and B_n := int P_n e^{-x}(log x + gamma) is rational
# with  int P_n e^{-x} log x = B_n - gamma_E.  Irrationality criterion: den(B_n)*|B_n - gamma_E| -> 0.
from fractions import Fraction as F
import math, mpmath as mp
mp.mp.dps = 80
GAM = mp.euler
N = 22
# derangements !j  (M_j)
der = [0]*(2*N+4); der[0]=1; der[1]=0
for n in range(2,2*N+4): der[n] = (n-1)*(der[n-1]+der[n-2])
# harmonic numbers exact
H=[F(0)]*(N+2)
for k in range(1,N+2): H[k]=H[k-1]+F(1,k)
from math import comb, factorial
def R(i):  # int (x-1)^i e^{-x}(log x + gamma) dx = sum_k C(i,k)(-1)^{i-k} k! H_k
    s=F(0)
    for k in range(i+1):
        s += F(comb(i,k))*F((-1)**(i-k))*F(factorial(k))*H[k]
    return s
Rc=[R(i) for i in range(N+1)]
def lcm1(n):
    l=1
    for k in range(1,n+1): l=l*k//math.gcd(l,k)
    return l
print(f"{'n':>3} {'err=|B_n-g|':>14} {'err^(1/n)':>10} {'den(B_n)':>10} {'den*err':>14} {'(den*err)^(1/n)':>16}")
prev=None
for n in range(1,N+1):
    size=n+1
    # Hankel system A[j][i]=der[i+j], rhs e_0; exact Gaussian elimination over F
    Mx=[[F(der[i+j]) for i in range(size)]+[F(1 if j==0 else 0)] for j in range(size)]
    for col in range(size):
        p=next(r for r in range(col,size) if Mx[r][col]!=0)
        Mx[col],Mx[p]=Mx[p],Mx[col]
        pv=Mx[col][col]; Mx[col]=[x/pv for x in Mx[col]]
        for r in range(size):
            if r!=col and Mx[r][col]!=0:
                f=Mx[r][col]; Mx[r]=[Mx[r][t]-f*Mx[col][t] for t in range(size+1)]
    c=[Mx[r][size] for r in range(size)]
    Bn=sum(c[i]*Rc[i] for i in range(size))
    den=Bn.denominator
    err=abs(mp.mpf(Bn.numerator)/mp.mpf(Bn.denominator)-GAM)
    de=mp.mpf(den)*err
    er=float(err**(mp.mpf(1)/n)) if err>0 else 0
    der1=float(de**(mp.mpf(1)/n)) if de>0 else 0
    print(f"{n:>3} {mp.nstr(err,4):>14} {er:>10.4f} {den:>10} {mp.nstr(de,4):>14} {der1:>16.4f}")
