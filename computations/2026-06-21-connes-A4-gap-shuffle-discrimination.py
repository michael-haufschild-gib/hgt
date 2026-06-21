#!/usr/bin/env python3
"""
connes A4 — strongest same-geometry/different-arithmetic control: GAP-SHUFFLE.

Build a control from zeta's OWN gaps, randomly permuted and re-accumulated. It has the EXACT spacing
distribution of zeta (matches the one-level gap statistics / unfolded density) but destroyed long-range
arithmetic order. Question (genuinely open): does the prime-log resonance survive shuffling, and how
does the zeta-vs-shuffle discrimination scale with the number of zeros N?

This is a much stronger control than "same density random": it matches the gap histogram exactly.
Methods mangled: #15 strengthen the control, #13 monotone (vs N), #10 extreme (small-N onset), #3 reverse.

Resonance:  F(u) = sum_{n<=N} hann(n) cos(gamma_n * u),  evaluated at u = log(prime power) and controls.
Report, for a ladder of N, the zeta peak vs the shuffle-ensemble RMS (discrimination), per frequency.
DO NOT predict the scaling -- measure it.
"""
import mpmath as mp, numpy as np
from math import log, cos, pi

mp.mp.dps = 15
Nmax = 400
print(f"[setup] computing {Nmax} zeta zeros ...", flush=True)
gam = [float(mp.im(mp.zetazero(n))) for n in range(1, Nmax+1)]
gaps = np.diff(gam)
g0 = gam[0]

def hann(N):
    return np.array([0.5-0.5*cos(2*pi*i/(N-1)) for i in range(N)])

def resonance(gammas, N, u):
    w = hann(N)
    return float(np.sum(w*np.cos(np.array(gammas[:N])*u)))

def shuffled_divisor(rng):
    p = rng.permutation(gaps)
    return np.concatenate([[g0], g0+np.cumsum(p)])

freqs = [("log2",log(2)),("log3",log(3)),("log5",log(5)),("log7",log(7)),("log11",log(11)),
         ("log4",log(4)),("log9",log(9)),
         ("log6(comp)",log(6)),("log10(comp)",log(10)),("log15(comp)",log(15))]
Ns = [50,100,200,400]
rng = np.random.default_rng(2024)
SH = 40
shuffles = [shuffled_divisor(rng) for _ in range(SH)]

print(f"\n{'freq':>12} |"+ "".join(f" N={N:<4}: zeta / sh.rms (disc) |" for N in Ns))
for nm,u in freqs:
    row=f"{nm:>12} |"
    for N in Ns:
        z = abs(resonance(gam, N, u))
        sh = np.array([abs(resonance(s, N, u)) for s in shuffles])
        rms = float(np.sqrt(np.mean(sh**2)))
        disc = z/rms if rms>0 else float('inf')
        row += f" {z:5.2f}/{rms:4.2f} ({disc:4.1f}) |"
    print(row)
print("\n[reading] prime-power rows: zeta peak vs shuffle RMS = discrimination; composite rows are controls.")
print("  Track how discrimination scales with N (monotone? saturating?) and the smallest-N onset per prime.")
