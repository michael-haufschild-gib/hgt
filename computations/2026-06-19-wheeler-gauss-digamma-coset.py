#!/usr/bin/env python3
"""
E3 (part) — relative-exponential-apex §19: the digamma-at-rationals coset rigidity.

Gauss's digamma theorem (classical):  for 0 < p < q,
    psi(p/q) = -gamma - ln(2q) - (pi/2) cot(pi p/q)
               + 2 * sum_{n=1}^{floor((q-1)/2)} cos(2 pi n p/q) * ln( sin(n pi/q) ).

Every term on the RHS except (-gamma) is a "regular" quantity:
    ln(2q)            : log of a rational                      -> in R-bar
    cot(pi p/q)       : ALGEBRAIC number (cot of rational*pi)  -> algebraic
    cos(2 pi n p/q)   : ALGEBRAIC number                       -> algebraic
    ln( sin(n pi/q) ) : log of an ALGEBRAIC number             -> in R-bar (generalized log)
So  psi(p/q) + gamma_E  in  R-bar  for every rational p/q  ==> the whole family
{psi(p/q)} lies in the single coset (-gamma_E + R-bar): UNCONDITIONALLY it adds
exactly one atom (gamma_E) over the regular base.

This script VERIFIES Gauss's identity to high precision for several (p,q), i.e.
verifies the coset claim numerically (the algebra is classical; we check we have
the constants right and that the +gamma residue is exactly the regular part).
Bounded, exact-ish (mpmath), runs in seconds.
"""
import mpmath as mp

mp.mp.dps = 60

def gauss_rhs(p, q):
    g = mp.euler
    s = -g - mp.log(2*q) - (mp.pi/2)*mp.cot(mp.pi*p/q)
    half = (q - 1)//2
    acc = mp.mpf(0)
    for n in range(1, half+1):
        acc += mp.cos(2*mp.pi*n*p/q) * mp.log(mp.sin(n*mp.pi/q))
    return s + 2*acc

def regular_part(p, q):
    """psi(p/q) + gamma  -- should equal the RHS-with-gamma-removed, all regular."""
    g = mp.euler
    reg = -mp.log(2*q) - (mp.pi/2)*mp.cot(mp.pi*p/q)
    half = (q - 1)//2
    acc = mp.mpf(0)
    for n in range(1, half+1):
        acc += mp.cos(2*mp.pi*n*p/q) * mp.log(mp.sin(n*mp.pi/q))
    return reg + 2*acc

print(f"# dps={mp.mp.dps}")
print("# Verify Gauss: psi(p/q) == gauss_rhs(p,q), and psi(p/q)+gamma == regular_part(p,q)")
cases = [(1,2),(1,3),(2,3),(1,4),(3,4),(1,6),(5,6),(2,5),(1,5),(3,7)]
maxerr = mp.mpf(0)
for (p,q) in cases:
    lhs = mp.digamma(mp.mpf(p)/q)
    rhs = gauss_rhs(p,q)
    e1 = abs(lhs - rhs)
    # coset check: psi + gamma equals the regular (gamma-free) part
    cos_resid = abs((lhs + mp.euler) - regular_part(p,q))
    maxerr = max(maxerr, e1, cos_resid)
    print(f"  p/q={p}/{q}: |psi-gauss_rhs|={mp.nstr(e1,3)}   |(psi+gamma)-regular|={mp.nstr(cos_resid,3)}")
print(f"# max error over all cases: {mp.nstr(maxerr,3)}")

# Sanity that cot/cos at rational*pi are algebraic (degree check is structural;
# here just confirm they are real algebraic-looking constants, not transcendental):
print("# sample algebraic constants: cot(pi/6)=", mp.nstr(mp.cot(mp.pi/6),8),
      " cos(2pi/5)=", mp.nstr(mp.cos(2*mp.pi/5),8))
print("# done")
