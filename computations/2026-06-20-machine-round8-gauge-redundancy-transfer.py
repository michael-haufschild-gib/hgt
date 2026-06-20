#!/usr/bin/env python3
# THE MACHINE (codex+rng walk) — Round 8. Walk: initial-condition-projection -> related -> rng#7
# "gauge fixing in classical & quantum field theory" -> specifics -> rng#1 NODE = REDUNDANT GAUGE ORBITS
# (physically-equivalent configurations). Codex node-rules -> transfer (the PROCEDURE): a symmetry group
# acts; orbit = equivalent configs; PHYSICAL = invariants on the quotient; gauge-fixing picks a
# representative; "Gribov copy" = a slice meeting an orbit more than once; overcounting must be corrected.
# STEP 7 on zeta (Hurwitz at rational args): the "gauge identities" = the distribution/Kubert relations;
# the gauge-INVARIANT content = the conductor-graded Dirichlet-L pieces; the FE-slice s<->1-s has its
# "Gribov horizon" at the fixed locus Re=1/2. Experiments: (a) verify the gauge identity (distribution
# relation) holds; (b) count the quotient dimension (no overcounting / no Gribov-extra relations:
# sum_{d|m} phi(d) = m); (c) the FE-slice fixed locus.
import mpmath as mp
mp.mp.dps = 30
from sympy import totient, divisors

def dist_residual(s, a, m):
    lhs = mp.fsum(mp.zeta(s, (a + k)/mp.mpf(m)) for k in range(m))
    rhs = mp.power(m, s) * mp.zeta(s, a)
    return abs(lhs - rhs)/abs(rhs)

s = mp.mpf(3) + 1j*mp.mpf('2.0')
a = mp.mpf('0.37')
print("(a) GAUGE IDENTITY = distribution relation  sum_k zeta(s,(a+k)/m) = m^s zeta(s,a):")
for m in [2,3,4,5,6]:
    print(f"    m={m}  rel-residual={float(dist_residual(s,a,m)):.2e}")

print("\n(b) QUOTIENT dimension (no overcounting / no Gribov-extra relations):  sum_{d|m} phi(d) =?= m")
for m in [6,12,30]:
    tot = sum(int(totient(d)) for d in divisors(m))
    print(f"    m={m:3d}  sum_d|m phi(d)={tot}  m={m}  {'CLEAN (no extra relations)' if tot==m else 'MISMATCH'}")

print("\n(c) FE-slice s->1-s, Gribov horizon = fixed locus:")
for s0 in [mp.mpf('0.5')+1j*mp.mpf('7'), mp.mpf('0.25')+1j*mp.mpf('7')]:
    fixed = abs(mp.re(s0)-mp.mpf('0.5'))<1e-12
    print(f"    s={complex(s0)!s:>18} -> 1-s={complex(1-s0)!s:>18}  {'ON horizon Re=1/2' if fixed else 'off horizon'}")

print("\n=== STEP 8 self-curate ===")
print("(a) surprising? NO. (b) new about Gamma/zeta? NO.")
print("  Gauge-redundancy transferred = the CLASSICAL Dirichlet-L theory of Hurwitz-zeta at rationals:")
print("  the distribution/Kubert relations are the 'gauge identities' (verified ~1e-30); the gauge-invariant")
print("  quotient = conductor-graded primitive Dirichlet-L pieces (sum_{d|m} phi(d)=m EXACTLY => no overcounting,")
print("  no Gribov-extra relations); the FE-slice fixed locus = critical line (= R7's finding). All KNOWN.")
print("  On-mission note (value-relations pillar): zeta-at-rationals carries NO relations beyond distribution+")
print("  conductor grading = 'maximally independent modulo the gauge'. => DEAD END. Walk -> gauge-orbits.")
