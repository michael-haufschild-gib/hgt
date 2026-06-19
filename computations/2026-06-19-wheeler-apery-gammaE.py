from mpmath import mp, mpf, log, exp, factorial, digamma, binomial, laguerre, quad, inf, fabs, nstr, mpmathify
import math
mp.dps = 80
gE=-digamma(1)

def lcm_upto(n):
    from math import gcd
    L=1
    for k in range(1,n+1): L=L*k//gcd(L,k)
    return L

# Classical S=empty: dmu = e^-x dx.  L_j := int x^j log x e^-x dx = j!(H_j - gE).
def H(j): return sum(mpf(1)/k for k in range(1,j+1))
def Lj_classical(j):
    return factorial(j)*(H(j)-gE)

# P_n = n! * Laguerre_n(x): integer coeffs a_k = C(n,k)(-1)^k n!/k!
def laguerre_int_coeffs(n):
    return [ (-1)**k * (math.comb(n,k))*math.factorial(n)//math.factorial(k) for k in range(n+1) ]

print("Classical (S=empty) Laguerre construction for gamma_E:")
print(" n |   |R_n|        | log|R_n|/n | den=lcm(1..n) | E_n=den|R_n| | log E_n / n | B_n(=q_n/den)")
prev=None
for n in range(1,19):
    a=laguerre_int_coeffs(n)
    Rn=sum(mpf(a[j])*Lj_classical(j) for j in range(n+1))   # = A_n - B_n gE
    Bn=sum(mpf(a[j])*factorial(j) for j in range(n+1))       # integer; coeff of -gE is Bn so R=A - Bn gE
    den=lcm_upto(n)
    En=mpf(den)*fabs(Rn)
    lr = (log(fabs(Rn))/n) if Rn!=0 else mpf('nan')
    le = (log(En)/n) if En!=0 else mpf('nan')
    print(f"{n:2d} | {nstr(fabs(Rn),4):>10} | {nstr(lr,4):>8} | {nstr(mpf(den),3):>10} | {nstr(En,4):>9} | {nstr(le,4):>7} | Bn~{nstr(mpf(Bn),3)}")
print()
print("Diagnosis: irrationality of gamma_E would need E_n -> 0 (i.e. log E_n / n -> negative).")
print("If log E_n / n -> positive constant, the construction does NOT beat its denominators (the wall).")
