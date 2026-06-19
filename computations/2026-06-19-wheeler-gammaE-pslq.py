#!/usr/bin/env python3
"""
E2 — relative-exponential-apex: PSLQ falsification of the no-relations (H_2=0) half.

Goal: bound the height of any Q-linear / low-degree algebraic relation between the
exponential atom gamma_E and the regular period base
    R = Q(2pi i, {zeta(2k+1)}, {log p}, MZV...).
A "None" return at coefficient bound M is the unconditional statement:
    no Z-linear relation with |coeffs| <= M exists among the listed constants
    at the working precision.
This is the D=1 (linear) sub-case of the apex and direct evidence for H_2=0.

Bounded: a few constants, ~260 digits, PSLQ. Runs in seconds. No runpod needed.
"""
import mpmath as mp

mp.mp.dps = 260

g  = +mp.euler            # gamma_E = gamma_0
z2 = +mp.zeta(2)
z3 = +mp.zeta(3)
z5 = +mp.zeta(5)
z7 = +mp.zeta(7)
pi = +mp.pi
pi2 = pi**2
l2 = +mp.log(2)
l3 = +mp.log(3)
g1 = +mp.stieltjes(1)    # gamma_1 (first Stieltjes constant)
g2 = +mp.stieltjes(2)

MC = 10**12              # max |coefficient| searched
STEPS = 10**6

def show(tag, basis, names):
    rel = mp.pslq(basis, maxcoeff=MC, maxsteps=STEPS)
    if rel is None:
        print(f"{tag}: NONE  (no Z-relation with |coeff|<= {MC} among {names})")
    else:
        terms = " + ".join(f"{c}*{nm}" for c, nm in zip(rel, names) if c != 0)
        print(f"{tag}: FOUND {rel}")
        print(f"        => {terms} = 0")
    return rel

print(f"# precision dps={mp.mp.dps}, maxcoeff={MC}")

# --- Control: harness sanity, must FIND zeta(2)=pi^2/6 i.e. 6*z2 - pi2 = 0 ---
show("CTRL", [z2, pi2], ["zeta2", "pi^2"])

# --- E2a: linear independence of gamma_E from the bottom regular base ---
show("E2a", [mp.mpf(1), g, z3, z5, pi2, l2, l3],
     ["1", "gammaE", "zeta3", "zeta5", "pi^2", "log2", "log3"])

# --- E2b: add gamma_1 (next Stieltjes rung) ---
show("E2b", [mp.mpf(1), g, g1, z3, z5, pi2, l2, l3],
     ["1", "gammaE", "gamma1", "zeta3", "zeta5", "pi^2", "log2", "log3"])

# --- E2c: gamma_E against the pure-zeta (no-log) period subset ---
show("E2c", [mp.mpf(1), g, z2, z3, z5, z7],
     ["1", "gammaE", "zeta2", "zeta3", "zeta5", "zeta7"])

# --- E2d: the two Stieltjes rungs against each other + base (joint H_2) ---
show("E2d", [mp.mpf(1), g, g1, g2, z3, z5, pi2],
     ["1", "gammaE", "gamma1", "gamma2", "zeta3", "zeta5", "pi^2"])

# --- E2e: degree-2 probe -- include products to catch a quadratic relation ---
show("E2e", [mp.mpf(1), g, g*g, z3, pi2, g*pi2, g*z3],
     ["1", "gammaE", "gammaE^2", "zeta3", "pi^2", "gammaE*pi^2", "gammaE*zeta3"])

print("# done")
