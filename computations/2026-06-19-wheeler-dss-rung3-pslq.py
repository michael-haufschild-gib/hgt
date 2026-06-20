#!/usr/bin/env python3
# Wheeler 2026-06-19 — DSS apex falsification, RUNG 3 (degree-3): extends DeWitt's rung-2 (degree-2).
# Search for an integer relation among ALL degree-<=3 monomials in {1, gamma_0, gamma_1, log2, log3}
# (= alg. dependence of the core DSS-cross atoms at degree 3). NONE => apex hardened at rung 3.
import mpmath as mp
from itertools import combinations_with_replacement

mp.mp.dps = 400
g0 = +mp.euler            # gamma_0
g1 = mp.stieltjes(1)      # gamma_1
l2 = mp.log(2); l3 = mp.log(3)
base = {'1': mp.mpf(1), 'g0': g0, 'g1': g1, 'l2': l2, 'l3': l3}
names = ['g0', 'g1', 'l2', 'l3']   # '1' handled by degree padding

# all monomials of total degree <= 3 in the 4 nontrivial atoms (constant 1 included as the empty product)
monos = []
for d in range(0, 4):
    for combo in combinations_with_replacement(names, d):
        monos.append(combo)
vals = []
labels = []
for combo in monos:
    v = mp.mpf(1)
    for x in combo:
        v *= base[x]
    vals.append(v)
    labels.append('*'.join(combo) if combo else '1')
print("rung-3: %d monomials (deg<=3 in {g0,g1,l2,l3}), dps=%d" % (len(vals), mp.mp.dps), flush=True)

# CONTROL: confirm PSLQ is live on a known relation 6*zeta(2) - pi^2 = 0
ctrl = mp.pslq([mp.zeta(2), mp.pi**2], maxcoeff=10**6, maxsteps=10**5)
print("CONTROL 6z2-pi2 ->", ctrl, flush=True)

# main search
rel = mp.pslq(vals, maxcoeff=10**5, maxsteps=4*10**5)
if rel is None:
    print("RUNG-3 RESULT: NONE (no degree-<=3 integer relation, maxcoeff 1e5) -> apex hardened at rung 3", flush=True)
else:
    nz = [(labels[i], rel[i]) for i in range(len(rel)) if rel[i] != 0]
    print("RUNG-3 RESULT: RELATION FOUND ->", nz, flush=True)
    # verify residual
    s = sum(rel[i]*vals[i] for i in range(len(rel)))
    print("residual =", mp.nstr(s, 10), " (compare to 10^-%d floor)" % mp.mp.dps, flush=True)
print("DONE", flush=True)
