#!/usr/bin/env python3
"""Doc 80 SS5 decider: twin-pair census of the mixed set
SP := {N : N = A*c, A 313-smooth, c = 1 or prime <= 691150}
in sampled windows near B0 = 3.3e10 and 3.3e11 (the delta-onset scales).
Measures: SP density, twin-pair counts (q <= 32), weighted per-octave
contribution sum for the mixed cross term (coef 1 upper spirit),
where weight(pair) = 1.5^{Om_sm(N)+Om_sm(M)} / (prodfacts * sqrt(N*M)).
Seeded from session seed 1327387142575317405.
"""
import numpy as np, json
from math import sqrt, log

rng = np.random.default_rng(1327387142575317405 % 2**63)
XREST = 691150

def primes_upto(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n**0.5) + 1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]

P1 = primes_upto(313)
Psmall = primes_upto(int(XREST**0.5) + 1)  # for primality of cofactor

def is_prime(n):
    if n < 2: return False
    for p in Psmall:
        if p*p > n: return True
        if n % p == 0: return n == p
    return True

def sp_data(N):
    """return (in_SP, Om_smooth, prodfact) for N."""
    m = N; om = 0; pf = 1.0
    for p in P1:
        k = 0
        while m % p == 0:
            m //= p; k += 1
        if k:
            om += k
            for j in range(2, k + 1): pf *= j
    if m == 1: return True, om, pf
    if m <= XREST and is_prime(int(m)): return True, om, pf
    return False, om, pf

OUT = {}
U15 = 1.5  # (u/2) at u=3 for the smooth part
for B0 in (33_000_000_000, 330_000_000_000):
    W = 200_000; NWIN = 3; QMAX = 32
    dens_n = 0; tot_n = 0; pair_cnt = 0; wsum = 0.0
    for w in range(NWIN):
        start = int(B0*(1 + 0.3*w)) + int(rng.integers(0, 10**6))
        flags = np.zeros(W, dtype=bool); oms = np.zeros(W); pfs = np.ones(W)
        for i in range(W):
            f, om, pf = sp_data(start + i)
            flags[i] = f; oms[i] = om; pfs[i] = pf
        idx = np.nonzero(flags)[0]
        dens_n += len(idx); tot_n += W
        for ii in range(len(idx)):
            jj = ii + 1
            while jj < len(idx) and idx[jj] - idx[ii] <= QMAX:
                a = start + idx[ii]; b = start + idx[jj]
                wgt = (U15**(oms[idx[ii]] + oms[idx[jj]])
                       / (pfs[idx[ii]]*pfs[idx[jj]]*sqrt(float(a)*float(b))))
                wsum += wgt; pair_cnt += 1
                jj += 1
    dens = dens_n/tot_n
    # per-octave extrapolation: octave has ~B0 numbers -> pairs ~ (B0/W/NWIN)*pair_cnt scaled
    scale = B0/(W*NWIN)
    OUT[str(B0)] = dict(
        density=dens, pairs_in_sample=pair_cnt,
        weighted_sum_sample=wsum,
        est_octave_weighted=wsum*scale,
        est_octave_pairs=pair_cnt*scale)
print(json.dumps(OUT, indent=1))
