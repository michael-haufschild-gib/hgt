#!/usr/bin/env python3
"""Discrete model of not-RH: zeta-like gapped atomic measure plus one off-line pair, i.e. moments
c_k += A*(e^{-ik(t0+i d)} + e^{-ik(t0-i d)}) + mirror at -t0 (Hermitian, indefinite for large k).
Track the minimal eigenvalue sign (first contact order n_c), whether eigenpolynomial zeros stay on the
unit circle, and nested-order separation for pairs below / across / above n_c."""
import numpy as np, json
from multiprocessing import Pool
from sep import moments_atomic, toeplitz, separated

def gapped_atoms(rng):
    g = []; t = 0.3
    while t < np.pi:
        g.append(t); t += 1.0 / (2 * (1 + 6 * t))
    g = np.array(g) + rng.normal(0, 0.002, len(g))
    return np.concatenate([g, -g]), np.ones(2 * len(g))

def trial(args):
    seed, d, t0 = args
    rng = np.random.default_rng(seed); N = 61
    th, w = gapped_atoms(rng)
    c = moments_atomic(np.mod(th, 2 * np.pi), w, N)
    k = np.arange(N)
    # off-line pair at t0 +- i d and its mirror -t0 -+ i d (keeps Hermitian Toeplitz real-symmetric)
    off = 0.0
    for s in (t0, -t0):
        off = off + 0.5 * (np.exp(-1j * k * (s + 1j * d)) + np.exp(-1j * k * (s - 1j * d)))
    c = c + off
    info = {'seed': seed, 'd': d, 't0': t0, 'lam': {}, 'oncircle': {}, 'zeros': {}}
    for n in range(4, N + 1, 2):
        T = toeplitz(c, n)
        T = (T + T.conj().T) / 2
        E, V = np.linalg.eigh(T)
        info['lam'][n] = float(E[0])
        if E[1] - E[0] < 1e-9 * max(1, abs(E[-1])):
            continue
        r = np.roots(V[:, 0][::-1])
        info['oncircle'][n] = float(np.max(np.abs(np.abs(r) - 1)))
        info['zeros'][n] = np.sort(np.mod(np.angle(r), 2 * np.pi)).tolist()
    neg = [n for n in sorted(info['lam']) if info['lam'][n] < 0]
    nc = neg[0] if neg else None
    ks = sorted(info['zeros'])
    stats = {'below': [0, 0], 'across': [0, 0], 'above': [0, 0]}
    for i in range(len(ks)):
        for j in range(i + 1, len(ks)):
            a, b = ks[i], ks[j]
            cls = 'below' if (nc is None or b < nc) else ('above' if a >= nc else 'across')
            stats[cls][0] += 1
            if not separated(np.array(info['zeros'][a]), np.array(info['zeros'][b])):
                stats[cls][1] += 1
    return {'seed': seed, 'd': d, 't0': t0, 'n_contact': nc, 'stats': stats,
            'max_offcircle': max(info['oncircle'].values()) if info['oncircle'] else None}

if __name__ == '__main__':
    jobs = [(s, d, t0) for s in range(6) for d in (0.02, 0.05, 0.1) for t0 in (1.5, 2.5)]
    with Pool(8) as p: out = p.map(trial, jobs)
    json.dump(out, open('sep3.json', 'w'), indent=1)
    for r in out:
        print('d=%.2f t0=%.1f seed=%d n_c=%s offcircle=%.1e below %s across %s above %s' % (
            r['d'], r['t0'], r['seed'], r['n_contact'], r['max_offcircle'] or -1,
            r['stats']['below'], r['stats']['across'], r['stats']['above']))
