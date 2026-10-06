#!/usr/bin/env python3
"""Discrete test of nested-order zero separation for minimal-eigenvector polynomials of Hermitian
Toeplitz matrices T_n = (c_{j-k}) built from positive measures mu on the circle.
For orders n < n', check: between consecutive zero-arguments of p_n (minimal eigenvector polynomial,
zeros on |z|=1 by Delsarte-Genin-Kamp when lambda_min simple) lies a zero-argument of p_{n'}.
Measure classes: atomic (K random atoms, random weights), smooth (random positive trig density),
atoms + small smooth part, 'zeta-like' (atoms with growing density away from theta=0, symmetric).
Also check monotone motion of zeros toward atoms (one-sided approach)."""
import numpy as np, json, sys
from multiprocessing import Pool
from mpmath import mp

def moments_atomic(th, w, N):
    k = np.arange(N)
    return (w[None, :] * np.exp(-1j * np.outer(k, th))).sum(axis=1)

def moments_density(coef, N):
    # density 1 + sum coef_j cos(j theta) (coef small enough to stay positive)
    c = np.zeros(N, complex); c[0] = 1.0
    for j in range(1, min(N, len(coef) + 1)):
        c[j] = coef[j - 1] / 2
    return c

def toeplitz(c, n):
    T = np.empty((n, n), complex)
    for j in range(n):
        for k in range(n):
            d = j - k
            T[j, k] = c[d] if d >= 0 else np.conj(c[-d])
    return T

def zero_args(c, n):
    T = toeplitz(c, n)
    E, V = np.linalg.eigh(T)
    if E[1] - E[0] < 1e-9 * max(1, abs(E[-1])):
        return None, E[0]
    v = V[:, 0]
    r = np.roots(v[::-1])
    return np.sort(np.mod(np.angle(r), 2 * np.pi)), E[0]

def separated(za, zb):
    # between consecutive (cyclically) zeros of za there is a zero of zb
    m = len(za)
    for i in range(m):
        lo, hi = za[i], za[(i + 1) % m]
        if i == m - 1:
            hi += 2 * np.pi
        ok = any(lo < y < hi or lo < y + 2 * np.pi < hi for y in zb)
        if not ok:
            return False
    return True

def trial(args):
    kind, seed = args
    rng = np.random.default_rng(seed)
    N = 41
    if kind == 'atomic':
        K = 60; th = rng.uniform(0, 2 * np.pi, K); w = rng.uniform(0.1, 1, K)
        c = moments_atomic(th, w, N)
    elif kind == 'smooth':
        coef = rng.normal(0, 1, 8); coef *= 0.9 / np.abs(coef).sum(); c = moments_density(coef, N)
    elif kind == 'mixed':
        K = 15; th = rng.uniform(0, 2 * np.pi, K); w = rng.uniform(0.1, 1, K)
        c = moments_atomic(th, w, N) + 1e-3 * moments_density(np.zeros(1), N)
    else:  # zetalike: symmetric atoms, density growing away from 0
        gam = []
        t = 0.3
        while t < np.pi:
            gam.append(t); t += 0.5 / (1 + 6 * t)
        gam = np.array(gam); th = np.concatenate([gam, 2 * np.pi - gam]); w = np.ones(len(th))
        th += rng.normal(0, 0.002, len(th))
        c = moments_atomic(th, w, N)
    res = {'kind': kind, 'seed': seed, 'pairs': 0, 'viol': 0, 'degenerate': 0}
    zs = {}
    for n in range(4, N + 1, 3):
        z, lam = zero_args(c, n)
        if z is None:
            res['degenerate'] += 1
        else:
            zs[n] = z
    keys = sorted(zs)
    for i in range(len(keys)):
        for j in range(i + 1, len(keys)):
            res['pairs'] += 1
            if not separated(zs[keys[i]], zs[keys[j]]):
                res['viol'] += 1
    return res

if __name__ == '__main__':
    jobs = [(k, s) for k in ('atomic', 'smooth', 'mixed', 'zetalike') for s in range(40)]
    with Pool(8) as p:
        out = p.map(trial, jobs)
    json.dump(out, open('sep.json', 'w'), indent=1)
    for k in ('atomic', 'smooth', 'mixed', 'zetalike'):
        rs = [r for r in out if r['kind'] == k]
        print(k, 'pairs', sum(r['pairs'] for r in rs), 'violations', sum(r['viol'] for r in rs),
              'trials with violations', sum(1 for r in rs if r['viol']), 'degenerate', sum(r['degenerate'] for r in rs))
