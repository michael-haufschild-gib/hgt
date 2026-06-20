#!/usr/bin/env python3
# MACHINE STEP6+STEP8: COCYCLE/multiplier constraint of automorphy factors, transferred to the CONTINUUM/
# DIFFERENTIAL structure on C (per workflow v9: target HT content in the connection on C, NOT discrete values).
import mpmath as mp
mp.mp.dps = 30

# ---------- STEP6: cocycle constraint ON THE NODE (automorphy factor j(gamma,z)=(cz+d)^k) ----------
S = ((0,-1),(1,0)); T = ((1,1),(0,1))
def mul(A,B): return ((A[0][0]*B[0][0]+A[0][1]*B[1][0], A[0][0]*B[0][1]+A[0][1]*B[1][1]),
                       (A[1][0]*B[0][0]+A[1][1]*B[1][0], A[1][0]*B[0][1]+A[1][1]*B[1][1]))
def act(A,z): return (A[0][0]*z+A[0][1])/(A[1][0]*z+A[1][1])
def j(A,z,k): return (A[1][0]*z+A[1][1])**k
z0 = mp.mpc(0.3,1.2)
print("=== STEP6 NODE: automorphy-factor cocycle j(g1g2,z) = j(g1,g2 z) j(g2,z) ===")
for k in [2, mp.mpf('0.5')]:
    g1,g2 = S,T
    lhs = j(mul(g1,g2), z0, k)
    rhs = j(g1, act(g2,z0), k)*j(g2, z0, k)
    ratio = lhs/rhs
    print(f"  weight k={float(k)}: j(g1g2)/[j(g1)j(g2)] = {mp.nstr(ratio,6)}  "
          f"(=1 integer/no multiplier; phase != 1 => multiplier needed)")

# ---------- STEP8: CONTINUUM/DIFFERENTIAL transfer: the automorphy CONNECTION d log j ----------
# Modular/DA automorphy factor -> RATIONAL connection (finite poles). HT reflection factor chi(s) of zeta
# (chi=pi^{s-1/2} Gamma((1-s)/2)/Gamma(s/2)) -> TRANSCENDENTAL connection (digamma). Count poles in a box,
# AND test the cocycle consistency chi(s)chi(1-s)=1 on the CONTINUUM (the Z/2 reflection cocycle).
print("\n=== STEP8 continuum: automorphy CONNECTION dlog j, modular(DA) vs zeta-reflection(HT) ===")
def chi(s): return mp.pi**(s-mp.mpf('0.5')) * mp.gamma((1-s)/2) / mp.gamma(s/2)
def dlogchi(s):  # chi'/chi = log pi - 1/2 psi((1-s)/2) - 1/2 psi(s/2)
    return mp.log(mp.pi) - mp.psi(0,(1-s)/2)/2 - mp.psi(0,s/2)/2
# cocycle consistency on continuum (order-2 reflection): chi(s) chi(1-s) = 1 for ALL s
print("  Z/2 cocycle chi(s)*chi(1-s) (should = 1 on the whole continuum):")
for s in [mp.mpc(2,1), mp.mpc(0.5,14.13), mp.mpc(-3,0.7), mp.mpc(0.25,5)]:
    print(f"    s={mp.nstr(s,5)}: chi(s)chi(1-s) = {mp.nstr(chi(s)*chi(1-s),8)}")
# connection nature: modular log-deriv k*c/(cz+d) is RATIONAL (1 pole); chi'/chi is digamma (infinitely many poles)
print("\n  connection log-derivative pole structure:")
print("   modular j=(cz+d)^k: dlog j = k*c/(cz+d) = RATIONAL, exactly 1 pole (DA/algebraic connection)")
# sample chi'/chi near its poles s=0,-2,-4 (from psi(s/2)) and s=1,3,5 (from psi((1-s)/2))
for s in [mp.mpc(-2,1e-6), mp.mpc(-4,1e-6), mp.mpc(3,1e-6)]:
    print(f"   chi'/chi at s={mp.nstr(s.real,3)}: |val|={mp.nstr(abs(dlogchi(s)),5)} (pole) -> INFINITELY many poles (transcendental)")
print("\nREAD: cocycle consistency chi*chi(1-s)=1 holds on continuum (functional-eq consistency); the HT")
print("connection chi'/chi is TRANSCENDENTAL (digamma, infinitely many poles) vs modular RATIONAL (finite).")
