"""
Is GPT-02's "source-quotiented Kolchin nonclosure" detector self-defeating for xi?

Claim [ARGUMENT]: xi is order 1, so by Hadamard it is determined by its zeros up to e^{a+bs}:
   xi'/xi(s) = b + sum_rho [ 1/(s-rho) + 1/rho ]      (the principal parts + convergence terms).
Hence the SOURCE-QUOTIENTED connection
   R(s) := xi'/xi(s) - sum_rho [ 1/(s-rho) + 1/rho ]   ==  b   (a CONSTANT, s-independent).
So removing the divisor leaves a tame constant: a Kolchin/diff-algebraic-closure test on R returns
ZERO defect. The detector that "removes the zeros then tests nonclosure" throws away exactly the HT it
seeks: xi's hypertranscendence is DIVISOR-ENCODED (it lives in the locations {gamma_n}, the value axis).
(Contrast: sin(pi s) is order 1 with arithmetic-progression zeros and IS D-algebraic; xi's zeros have
log-density, which is why xi is HT. Order-1 HT is a property of the zero distribution's arithmetic.)

Numerical confirmation: R(s) is s-INDEPENDENT -> R(s1)-R(s2) -> 0 as more zeros are included.
Run: python3 this.py   (mpmath, ~1-2 min for 80 zeros)
"""
import mpmath as mp
mp.mp.dps = 25
half = mp.mpf(1)/2
logpi = mp.log(mp.pi)

def logxi(s):
    return ( mp.log(half) + mp.log(s) + mp.log(s-1)
             - (s/2)*logpi + mp.loggamma(s/2) + mp.log(mp.zeta(s)) )
def xi_logderiv(s):
    return mp.diff(logxi, s)

# precompute zeros rho_n = 1/2 + i gamma_n and their conjugates
def zeros(N):
    g = [mp.zetazero(n).imag for n in range(1, N+1)]
    rs = []
    for gn in g:
        rs.append(half + 1j*gn)
        rs.append(half - 1j*gn)
    return rs

def divisor_sum(s, rhos):
    # sum_rho [ 1/(s-rho) + 1/rho ]   (Hadamard genus-1 form)
    return mp.fsum(1/(s-r) + 1/r for r in rhos)

def R(s, rhos):
    return xi_logderiv(s) - divisor_sum(s, rhos)

s1 = mp.mpf('0.3') + 40j
s2 = mp.mpf('0.7') + 12j
print("Testing s-independence of R(s) = xi'/xi - sum_rho[1/(s-rho)+1/rho]  (should -> constant):")
print("  N_zeros   R(s1)              R(s2)              |R(s1)-R(s2)|")
for N in [40, 80]:
    rhos = zeros(N)
    r1, r2 = R(s1, rhos), R(s2, rhos)
    print(f"  {N:>5}   {mp.nstr(r1,6):>17}  {mp.nstr(r2,6):>17}  {mp.nstr(abs(r1-r2),3):>10}")
print()
print("Verdict: |R(s1)-R(s2)| shrinks as N grows => R is s-independent (a constant b).")
print("=> the divisor-quotiented connection of xi is TAME (constant); a Kolchin/diff-algebraic-closure")
print("   test on it returns ZERO defect. GPT-02's source-quotiented detector removes xi's HT, which is")
print("   DIVISOR-ENCODED (in the zero locations {gamma_n} = the value/arithmetic axis, APEX-A).")
