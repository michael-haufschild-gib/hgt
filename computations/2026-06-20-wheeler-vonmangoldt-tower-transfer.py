#!/usr/bin/env python3
# THE MACHINE (random-walk workflow). Start node = HT/Gamma/Li/zeta. codex related-list -> rng 2 ->
# Analytic number theory -> codex parts -> rng 9 -> NODE = von Mangoldt function Lambda(n). Seed walk.
# NODE rules (codex Step 5): Lambda(p^k)=log p (EXPONENT-INDEPENDENT), 0 else; Lambda*1=log;
# sum Lambda(n)/n^s = -zeta'/zeta; psi(x)=sum Lambda encodes primes.
# DISTINCTIVE testable rule: EXPONENT-INDEPENDENCE — Lambda flat across a prime tower {p,p^2,p^3,...}.
#
# STEP 6 experiment: does f's log-derivative carry a FLAT TOWER atom-structure? STEP 7 on zeta AND Gamma.
import mpmath as mp
mp.mp.dps=30

def Lambda(n):
    if n<2: return mp.mpf(0)
    m=n; p=2; pr=None
    f=n
    # factor
    d=2; fac={}
    while d*d<=f:
        while f%d==0: fac[d]=fac.get(d,0)+1; f//=d
        d+=1
    if f>1: fac[f]=fac.get(f,0)+1
    return mp.log(list(fac)[0]) if len(fac)==1 else mp.mpf(0)

print("== E (exponent-independence): Lambda(n) on towers — flat across k? breaks where? ==")
for p in (2,3,5):
    vals=[(p**k, float(Lambda(p**k))) for k in range(1,6)]
    print(f"  prime {p}: "+", ".join(f"L({n})={v:.4f}" for n,v in vals)+f"   (log {p}={float(mp.log(p)):.4f}) -> FLAT")
print("  non-prime-powers: "+", ".join(f"L({n})={float(Lambda(n)):.1f}" for n in (6,10,12,15))+"  -> 0 (breaks off prime powers)")

print("\n== STEP 7a on ZETA: tower geometric-sums to the Euler factor; sum over primes = -zeta'/zeta ==")
s=mp.mpf(2)
# direct -zeta'/zeta
lhs = -mp.zeta(s, derivative=1)/mp.zeta(s)
# via Lambda Dirichlet series (truncated)
rhs = mp.fsum(Lambda(n)/mp.power(n,s) for n in range(2,4000))
# via prime towers: sum_p log p * p^-s/(1-p^-s)
from sympy import primerange
rhs2 = mp.fsum(mp.log(p)*mp.power(p,-s)/(1-mp.power(p,-s)) for p in primerange(2,4000))
print(f"  -zeta'/zeta(2)          = {float(lhs):.8f}")
print(f"  sum Lambda(n) n^-2      = {float(rhs):.8f}   (zeta has a PRIME-TOWER atom structure)")
print(f"  sum_p logp*p^-2/(1-p^-2)= {float(rhs2):.8f}   (each prime = one flat geometric tower)")

print("\n== STEP 7b on GAMMA: atoms of -Gamma'/Gamma = -psi(s). Poles at s=0,-1,-2,... — tower or not? ==")
for n in (0,1,2,3):
    s0=mp.mpf(-n)+mp.mpf('1e-12')
    res = (s0-(-n))*(-mp.digamma(s0))   # residue of -psi at s=-n
    print(f"  near s={-n}: (s+{n})*(-psi) = {float(res):+.5f}  (residue ~ +1, SINGLE simple pole — NO tower)")
print("  => Gamma's atoms = ARITHMETIC lattice {0,-1,-2,...}, weight 1, NO geometric tower (additive).")

print("\nREAD: zeta's log-derivative = PRIME-TOWER (multiplicative, geometric, exponent-independent) atom")
print("      structure + a SECOND face (zeros, via -zeta'/zeta poles). Gamma's = a single ARITHMETIC")
print("      lattice of simple poles (additive), ONE face, no tower. Lambda is the bridge: log = Lambda*1")
print("      converts the multiplicative prime-tower into the additive log.")
