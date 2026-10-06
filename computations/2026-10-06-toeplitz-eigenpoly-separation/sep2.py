#!/usr/bin/env python3
"""Which feature makes nested-order zero separation hold? Variants of the zeta-like measure."""
import numpy as np, json
from multiprocessing import Pool
from sep import moments_atomic, moments_density, toeplitz, zero_args, separated

def atoms_from_density(rho, t0, rng, jitter=0.002):
    g = []; t = t0
    while t < np.pi:
        g.append(t); t += 1.0 / rho(t)
    g = np.array(g) + rng.normal(0, jitter, len(g))
    return g

def build(kind, rng, N):
    if kind == 'zeta_gap':         # baseline: gap at 0, increasing density, symmetric, unit weights
        g = atoms_from_density(lambda t: 2 * (1 + 6 * t), 0.3, rng); w = np.ones(2 * len(g))
        th = np.concatenate([g, -g])
    elif kind == 'zeta_nogap':     # no gap
        g = atoms_from_density(lambda t: 2 * (1 + 6 * t), 0.02, rng); w = np.ones(2 * len(g))
        th = np.concatenate([g, -g])
    elif kind == 'decreasing':     # decreasing density
        g = atoms_from_density(lambda t: 2 * (1 + 6 * (np.pi - t)), 0.3, rng); w = np.ones(2 * len(g))
        th = np.concatenate([g, -g])
    elif kind == 'uniform':        # equally spaced (constant density)
        g = atoms_from_density(lambda t: 8.0, 0.3, rng); w = np.ones(2 * len(g))
        th = np.concatenate([g, -g])
    elif kind == 'randweights':    # zeta_gap positions, random weights (symmetric)
        g = atoms_from_density(lambda t: 2 * (1 + 6 * t), 0.3, rng); ww = rng.uniform(0.1, 2, len(g))
        th = np.concatenate([g, -g]); w = np.concatenate([ww, ww])
    elif kind == 'asym':           # zeta_gap density but not symmetric (only +theta, shifted copy)
        g = atoms_from_density(lambda t: 2 * (1 + 6 * t), 0.3, rng)
        g2 = atoms_from_density(lambda t: 2 * (1 + 6 * t), 0.31, rng)
        th = np.concatenate([g, -g2]); w = np.ones(len(th))
    elif kind == 'sym_random':     # symmetric random atoms
        g = rng.uniform(0.05, np.pi, 60); ww = rng.uniform(0.1, 1, 60)
        th = np.concatenate([g, -g]); w = np.concatenate([ww, ww])
    elif kind == 'mono_smooth':    # smooth even density increasing in |theta|: 1 + a(1-cos theta)
        a = rng.uniform(0.5, 5); c = moments_density(np.array([-a / (1 + a)]), N) ; return c
    if kind != 'mono_smooth':
        return moments_atomic(np.mod(th, 2 * np.pi), w, N)

def trial(args):
    kind, seed = args
    rng = np.random.default_rng(seed); N = 41
    c = build(kind, rng, N)
    res = {'kind': kind, 'seed': seed, 'pairs': 0, 'viol': 0, 'degenerate': 0}
    zs = {}
    for n in range(4, N + 1, 3):
        z, lam = zero_args(c, n)
        if z is None: res['degenerate'] += 1
        else: zs[n] = z
    ks = sorted(zs)
    for i in range(len(ks)):
        for j in range(i + 1, len(ks)):
            res['pairs'] += 1
            if not separated(zs[ks[i]], zs[ks[j]]): res['viol'] += 1
    return res

if __name__ == '__main__':
    kinds = ['zeta_gap', 'zeta_nogap', 'decreasing', 'uniform', 'randweights', 'asym', 'sym_random', 'mono_smooth']
    jobs = [(k, s) for k in kinds for s in range(30)]
    with Pool(8) as p: out = p.map(trial, jobs)
    json.dump(out, open('sep2.json', 'w'), indent=1)
    for k in kinds:
        rs = [r for r in out if r['kind'] == k]
        print('%-12s pairs %5d violations %4d trials_with_viol %2d degenerate %d' % (k, sum(r['pairs'] for r in rs),
              sum(r['viol'] for r in rs), sum(1 for r in rs if r['viol']), sum(r['degenerate'] for r in rs)))
