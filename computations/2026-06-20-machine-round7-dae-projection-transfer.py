#!/usr/bin/env python3
# THE MACHINE (codex+rng walk) — Round 7. Walk: current-node Euler-Maclaurin -> related -> rng#20
# "numerical solutions of ODEs" (out-of-field; re-rolled off the in-field #4 zeta-regularization) ->
# specifics -> rng#16 NODE = INITIAL-CONDITION PROJECTION (DAE consistent initialization).
# Codex node-rules transferred (the PROCEDURE, not the analogy): a DAE = flow(differential) + algebraic
# CONSTRAINT; an arbitrary state is inconsistent and must be PROJECTED onto the constraint manifold before
# any integration; projection FAILS/degenerates where the constraint is singular; higher INDEX = constraint
# must be differentiated more times to close into an ODE.
# STEP 7 on Gamma/zeta: their only handle is the functional-equation CONSTRAINT (Hoelder: no ODE) =>
# they look like an INFINITE-INDEX DAE. Experiments:
#   (a) true completed xi satisfies its constraint manifold xi(s)=xi(1-s) (residual ~0);
#   (b) a truncated Dirichlet approximation gets a measurable PROJECTION DISPLACEMENT (FE residual);
#   (c) the constraint-manifold involution s->1-s : its invariant locus.
import mpmath as mp
mp.mp.dps = 30

def xi(s):  # Riemann xi (completed zeta), entire, satisfies xi(s)=xi(1-s)
    return (s*(s-1)/2) * mp.power(mp.pi, -s/2) * mp.gamma(s/2) * mp.zeta(s)

def xi_trunc(s, N):  # completed, but zeta replaced by truncated Dirichlet sum (breaks the FE constraint)
    zt = mp.fsum(mp.mpf(n)**(-s) for n in range(1, N+1))
    return (s*(s-1)/2) * mp.power(mp.pi, -s/2) * mp.gamma(s/2) * zt

pts = [mp.mpf('2.0')+0j, mp.mpf('0.5')+1j*mp.mpf('14.13'), mp.mpf('0.3')+1j*mp.mpf('5.0'), mp.mpf('0.8')+1j*mp.mpf('10.0')]
print("(a) TRUE xi on its constraint manifold  |xi(s)-xi(1-s)| (should be ~0 = constraint holds):")
for s in pts:
    r = abs(xi(s)-xi(1-s))
    print(f"    s={complex(s)!s:>22}   residual={float(r):.2e}")

print("\n(b) PROJECTION DISPLACEMENT of truncated approx  |xi_N(s)-xi_N(1-s)| (N=50):")
for s in pts:
    r = abs(xi_trunc(s,50)-xi_trunc(1-s,50))
    print(f"    s={complex(s)!s:>22}   displacement={float(r):.3e}")

print("\n(c) constraint-manifold involution sigma: s -> 1-s, invariant locus:")
for s in [mp.mpf('0.5')+1j*mp.mpf('3'), mp.mpf('0.3')+1j*mp.mpf('3'), mp.mpf('0.5')+0j]:
    print(f"    s={complex(s)!s:>20} -> 1-s={complex(1-s)!s:>20}   Re-invariant? {'YES (Re=1/2 axis)' if abs(mp.re(s)-mp.mpf('0.5'))<1e-12 else 'no (moves off)'}")

print("\n=== STEP 8 self-curate ===")
print("(a) surprising? NO. (b) new about Gamma/zeta? NO.")
print("  Transferred projection experiments recover KNOWN structure: (a) FE = the constraint manifold xi(s)=xi(1-s);")
print("  (b) truncation displacement = the approximate-functional-equation error (Riemann-Siegel), truncation-")
print("  dominated; (c) the involution s->1-s has invariant axis Re=1/2 = the critical line. 'Gamma/zeta as")
print("  infinite-index DAE (pure constraint, no flow)' is an on-mission RE-DESCRIPTION of Hoelder/constraint-")
print("  not-flow; uniqueness-under-the-constraint = Hamburger's theorem. All KNOWN.")
print("  => DEAD END. Bank (note the on-mission DAE-index framing). Walk current-node -> initial-condition-projection.")
