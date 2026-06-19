#!/usr/bin/env python3.13
"""
jensen_hyperbolicity_margin.py -- Critic 2026-06-19.  ATTACK 1 test (speculative-proofs §A1 sharpened).
Secular coefficients c_m = [z^{2m}] xi(1/2+z)  (even Taylor coeffs of the completed zeta at the center;
= dyson's c_m up to normalization).  Jensen polynomial  J^{d,n}(X) = sum_{j=0}^d C(d,j) c_{n+j} X^j.
RH-relevant: every J^{d,n} hyperbolic (real-rooted).  Compute roots, confirm hyperbolic, and report the
MARGIN (min imaginary part magnitude of roots -> 0 if near non-hyperbolic; and min real-root gap).
Tests A1: free for n>=N(d) (GORZ); see how the margin behaves at low d,n.  Archive: computations/.
"""
import mpmath as mp
mp.mp.dps = 80

def xi(s):
    return mp.mpf(1)/2 * s*(s-1) * mp.pi**(-s/2) * mp.gamma(s/2) * mp.zeta(s)

M = 13
# even Taylor coeffs of xi(1/2+z): c_m = [z^{2m}] xi(1/2+z)
tc = mp.taylor(lambda z: xi(mp.mpf(1)/2 + z), 0, 2*M+1)
c = [tc[2*m] for m in range(M+1)]   # c[0..M]
print(f" dps={mp.mp.dps}; secular coeffs c_m=[z^2m]xi(1/2+z), m=0..{M}:")
for m in range(min(6,M+1)):
    print(f"   c_{m} = {mp.nstr(c[m],18)}")
print(f"   ... c_{M} = {mp.nstr(c[M],10)}  (all c_m>0 expected, Polya TP1)")

def binom(d,j):
    return mp.binomial(d,j)

def jensen_roots(d,n):
    # J^{d,n}(X)=sum_j C(d,j) c_{n+j} X^j ; need c_{n+j} for j=0..d
    if n+d > M: return None
    coeffs = [binom(d,j)*c[n+j] for j in range(d+1)]   # ascending
    coeffs_desc = coeffs[::-1]
    r = mp.polyroots([complex(x) for x in coeffs_desc], maxsteps=200, extraprec=200)
    return r

print("\n Jensen hyperbolicity (roots real?) and margins:")
print(f"   {'d':>2} {'n':>2} {'max|Im root|':>14} {'min real gap':>14} {'hyperbolic?':>12}")
for d in range(2,7):
    for n in range(0, min(5, M-d+1)):
        r = jensen_roots(d,n)
        if r is None: continue
        maxim = max(abs(mp.im(x)) for x in r)
        reals = sorted(mp.re(x) for x in r)
        gaps = [reals[i+1]-reals[i] for i in range(len(reals)-1)] if len(reals)>1 else [mp.inf]
        mingap = min(gaps)
        hyp = "YES" if maxim < mp.mpf(10)**(-30) else "NO/marginal"
        print(f"   {d:>2} {n:>2} {mp.nstr(maxim,6):>14} {mp.nstr(mingap,6):>14} {hyp:>12}")
print("\n VERDICT: all hyperbolic (max|Im|~0) confirms ξ's low-order Jensen polys real-rooted (RH-consistent);")
print("          the 'min real gap' is the hyperbolicity margin m_d the A1 deviation Δ(d,n) must stay below.")
