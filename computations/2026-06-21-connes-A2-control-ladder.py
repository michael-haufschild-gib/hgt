#!/usr/bin/env python3
"""
connes A2 — attack the A1 detector as false: the control ladder (gpt/15 win-condition #6).

A1 showed: AP divisor (gamma_n=n) -> S_k = (-1)^k zeta(2k) in Q*pi^{2k} (pi-period, relations collapse),
while zeta's S_k carry no low-height pi-period relation (arithmetically rigid).

Question: does the detector separate zeta from a SAME-DENSITY RANDOM divisor on the seam, or only from
the arithmetically-simple AP one? If random ALSO resists, the detector certifies "pi-period vs generic"
and places zeta with random -> it distinguishes simple-from-complex, NOT zeta-from-generic.

Three families, same seam geometry (all zeros on the line), different arithmetic:
  AP      : gamma_n = n                       -> S_k = (-1)^k zeta(2k)        (pi-period)
  zeta    : actual nontrivial zero ordinates  -> S_k from log Xi Taylor (exact, all zeros)
  random  : gamma_n from the Riemann-von Mangoldt smooth count + jitter (same density, random arithmetic)
Test at k=2,3,4 (truncation negligible): pi-period relation [pi^{2k}, S_k] via PSLQ (height <= 1e6).
"""
import mpmath as mp, numpy as np

mp.mp.dps = 50
half = mp.mpf(1)/2

# --- zeta: S_k from log Xi Taylor (exact, all zeros) ---
def logXi(w):
    s = half + w
    return mp.log(half*s*(s-1)*mp.power(mp.pi,-s/2)*mp.gamma(s/2)*mp.zeta(s))
cL = mp.taylor(logXi, 0, 12)
def S_zeta(k):   return -mp.mpf(k)*cL[2*k]

# --- AP: S_k = (-1)^k zeta(2k) ---
def S_AP(k):     return ((-1)**k)*mp.zeta(2*k)

# --- random same-density divisor: invert N(T)=(T/2pi)(log(T/2pi)-1)+7/8, add jitter ~ local spacing ---
np.random.seed(12345)
def rvm_count(T):
    t = T/(2*mp.pi)
    return t*(mp.log(t)-1) + mp.mpf(7)/8
def gamma_smooth(n):                                   # solve N(T)=n
    return mp.findroot(lambda T: rvm_count(T)-n, mp.mpf(2*n+10))
M = 4000
gam_rand = []
for n in range(1, M+1):
    g = gamma_smooth(n)
    sp = 2*mp.pi/mp.log(g/(2*mp.pi))                    # local mean spacing
    jit = mp.mpf(float(np.random.uniform(-0.5,0.5)))*sp # randomize arithmetic, keep density
    gam_rand.append(g + jit)
def S_rand(k):   return ((-1)**k)*sum(g**(-2*k) for g in gam_rand)   # tail ~ gamma_M^{-2k}, negligible k>=2

def pslq_pi(Sval, k):
    try:
        rel = mp.pslq([mp.power(mp.pi,2*k), Sval], tol=mp.mpf(10)**(-40), maxcoeff=10**6, maxsteps=10000)
    except Exception:
        rel = None
    if rel is None: return None
    h = max(abs(int(c)) for c in rel)
    res = abs(rel[0]*mp.power(mp.pi,2*k)+rel[1]*Sval)
    return rel, h, mp.nstr(res,3)

print(f"[setup] dps={mp.mp.dps}  random M={M} zeros (same density, jittered arithmetic)")
print(f"  sanity: S_2  AP={mp.nstr(S_AP(2),10)}  zeta={mp.nstr(S_zeta(2),10)}  rand={mp.nstr(S_rand(2),10)}")
print("\npi-period relation  c0*pi^{2k} + c1*S_k = 0  (PSLQ, height<=1e6):")
print(f"{'k':>2} | {'AP (expect relation)':>28} | {'zeta (expect none)':>22} | {'random (the test)':>22}")
for k in (2,3,4):
    rA, rZ, rR = pslq_pi(S_AP(k),k), pslq_pi(S_zeta(k),k), pslq_pi(S_rand(k),k)
    print(f"{k:>2} | {str(rA):>28} | {str(rZ):>22} | {str(rR):>22}")
print("\n[reading] AP finds relations; if BOTH zeta and random find NONE, the detector separates")
print("          arithmetically-simple (pi-period) from generic, but NOT zeta from same-density random.")
