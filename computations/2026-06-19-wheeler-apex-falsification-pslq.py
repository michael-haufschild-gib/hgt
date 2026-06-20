#!/usr/bin/env python3
# Wheeler 2026-06-19 — apex falsification sweep (sharper than E2 §18):
# include the archimedean constant log(2pi) (= a_inf) and the Stieltjes tower.
# A relation found => apex (relative-exponential-apex) FALSIFIED at that rung. NONE => floor hardened.
import mpmath as mp

mp.mp.dps = 300
one  = mp.mpf(1)
g0   = +mp.euler                 # gamma_E  (= Stieltjes gamma_0)
g1   = mp.stieltjes(1)
g2   = mp.stieltjes(2)
g3   = mp.stieltjes(3)
z2   = mp.zeta(2); z3 = mp.zeta(3); z5 = mp.zeta(5); z7 = mp.zeta(7)
pi2  = mp.pi**2
l2   = mp.log(2); l3 = mp.log(3); l5 = mp.log(5)
l2pi = mp.log(2*mp.pi)           # archimedean local constant a_inf = (1/2)log(2pi) -> 2*a_inf

def search(name, vec, maxcoeff, maxsteps=2*10**5):
    try:
        r = mp.pslq(vec, maxcoeff=maxcoeff, maxsteps=maxsteps)
    except Exception as e:
        r = "ERR:%s" % e
    print("%-46s maxcoeff=%g -> %s" % (name, maxcoeff, r), flush=True)

# CONTROL: known relation 6*zeta(2) - pi^2 = 0  (PSLQ must find [6,-1] or scalar multiple)
search("CONTROL {z2,pi2}=expect[6,-1]", [z2, pi2], 10**6)

# Bottom-rung LOG part + archimedean: is gamma_E in Q-span{1, log p, log 2pi}?
search("RUNG-log {1,g0,l2,l3,l5,l2pi}", [one, g0, l2, l3, l5, l2pi], 10**18)

# Bottom-rung FULL real weight-1 (logs + zeta-odd + archimedean)
search("RUNG-full {1,g0,l2,l3,l5,z3,z5,z7,l2pi}", [one, g0, l2, l3, l5, z3, z5, z7, l2pi], 10**12)

# Tower freeness (linear): {1, g0, g1, g2, g3}
search("TOWER {1,g0,g1,g2,g3}", [one, g0, g1, g2, g3], 10**15)

# Does gamma_E relate to the archimedean constant alone? {1, g0, l2pi}
search("ARCH {1,g0,l2pi}", [one, g0, l2pi], 10**20)

# Everything (broad)
search("ALL {1,g0,g1,g2,g3,z3,z5,z7,l2,l3,l5,l2pi}",
       [one, g0, g1, g2, g3, z3, z5, z7, l2, l3, l5, l2pi], 10**9)

print("DONE", flush=True)
