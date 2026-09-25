"""Spectral test of the damped Ingham conjecture.

G_jk = int_0^ell exp(-(nu_j+nu_k) s) exp(i (mu_j - mu_k) s) ds  (Gram matrix of damped exponentials).
Conjecture: lambda_min(G) >= c0 (ell - 2 pi/g) exp(-2 K ell)  [e^{i mu s} normalisation: Ingham length 2 pi/g] for mu-gaps >= g, 0 <= nu <= K.
Test: for many (mu, nu) patterns and an adversarial local search (small n), compute
  r(K) = log lambda_min(G) + 2 K ell   (should stay bounded below if the conjecture holds)
and the slope d log lambda_min / dK at the largest K (conjecture allows slope >= -2 ell).
High precision with mpmath (60 digits) since lambda_min can be ~ e^{-2 K ell}.
"""
import sys, json, math, itertools
import numpy as np
import mpmath as mp
from multiprocessing import Pool
mp.mp.dps = 60

G_GAP = 1.0

def gram(mu, nu, ell):
    n = len(mu)
    G = mp.matrix(n, n)
    for j in range(n):
        for k in range(n):
            z = mp.mpf(nu[j] + nu[k]) + 1j * mp.mpf(mu[j] - mu[k])
            if abs(z) < mp.mpf('1e-40'):
                G[j, k] = mp.mpf(ell)
            else:
                G[j, k] = (1 - mp.exp(-z * ell)) / z
    return G

def lam_min(mu, nu, ell):
    G = gram(mu, nu, ell)
    E = mp.eigh(G, eigvals_only=True)
    return float(min(E))

def patterns(n, K, rng):
    pats = {}
    ap = np.arange(n) * G_GAP
    rnd = np.concatenate([[0.0], np.cumsum(G_GAP + rng.exponential(0.5, n - 1))])
    pats['ap_allK'] = (ap, np.full(n, K))
    pats['ap_half'] = (ap, np.where(np.arange(n) % 2 == 0, 0.0, K))
    pats['ap_ladder'] = (ap, np.linspace(0, K, n))
    pats['ap_ladder_rev'] = (ap, np.linspace(K, 0, n))
    pats['rnd_allK'] = (rnd, np.full(n, K))
    pats['rnd_unif'] = (rnd, rng.uniform(0, K, n))
    pats['ap_topone'] = (ap, np.concatenate([[0.0], np.full(n - 1, K)]))
    return pats

def adversarial(n, K, ell, rng, iters=300):
    # local random search over gaps (>= g) and nus in [0,K] minimising log lambda_min
    best = None
    for restart in range(6):
        gaps = G_GAP + rng.exponential(0.3, n - 1)
        nu = rng.uniform(0, K, n)
        cur = lam_min(np.concatenate([[0.0], np.cumsum(gaps)]), nu, ell)
        for it in range(iters):
            g2 = np.maximum(G_GAP, gaps + rng.normal(0, 0.1, n - 1))
            nu2 = np.clip(nu + rng.normal(0, 0.1 * K + 1e-9, n), 0, K)
            val = lam_min(np.concatenate([[0.0], np.cumsum(g2)]), nu2, ell)
            if val < cur:
                cur, gaps, nu = val, g2, nu2
        if best is None or cur < best[0]:
            best = (cur, gaps.tolist(), nu.tolist())
    return best

def run_config(args):
    n, ell, seed = args
    rng = np.random.default_rng(seed)
    Ks = [0.0, 0.5, 1.0, 1.5, 2.0, 3.0]
    out = {'n': n, 'ell': ell, 'pattern_r': {}, 'adv': {}}
    for name in ['ap_allK', 'ap_half', 'ap_ladder', 'ap_ladder_rev', 'rnd_allK', 'rnd_unif', 'ap_topone']:
        rs = []
        for K in Ks:
            mu, nu = patterns(n, K, np.random.default_rng(seed))[name]
            lm = lam_min(mu, nu, ell)
            rs.append(math.log(max(lm, 1e-300)) + 2 * K * ell)
        out['pattern_r'][name] = rs
    # adversarial at K = 2, 4, 6 for small n
    if n <= 8:
        for K in [1.0, 2.0, 3.0]:
            cur, gaps, nu = adversarial(n, K, ell, rng)
            out['adv'][str(K)] = {'r': math.log(max(cur, 1e-300)) + 2 * K * ell, 'log_lam': math.log(max(cur, 1e-300)),
                                  'gaps': gaps, 'nu': nu}
    return out

if __name__ == '__main__':
    configs = [(n, ell, 7) for n in [2, 3, 4, 6, 8, 12, 20] for ell in [8.0, 12.0]]
    with Pool(min(len(configs), 16)) as pool:
        res = pool.map(run_config, configs)
    json.dump(res, open('damped_ingham_results.json', 'w'), indent=1)
    for r in res:
        n, ell = r['n'], r['ell']
        worst = min(min(v) for v in r['pattern_r'].values())
        worst_name = min(r['pattern_r'].items(), key=lambda kv: min(kv[1]))[0]
        adv = {K: round(v['r'], 2) for K, v in r['adv'].items()}
        print('n=%2d ell=%.0f  min r over patterns/K = %7.2f (%s)  adversarial r = %s' % (n, ell, worst, worst_name, adv), flush=True)
