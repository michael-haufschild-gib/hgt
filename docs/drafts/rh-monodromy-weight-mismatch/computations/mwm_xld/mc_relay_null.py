#!/usr/bin/env python3
"""Doc 77 SS2 null checks P-R1..P-R3: 3-step recross rate of the signed walk.
(a) iid uniform phases; (b) frozen lattice cos(beta+m*theta); (c) growing envelope.
Statistic: at each down-crossing of 0, does the walk recross within <=3 steps?
Also one-step rate vs E[arccos(v/a_next)/pi] from the run's own overshoot sample.
Walks are 0-started row segments (crossing-local statistics; dense sample).
"""
import numpy as np, json

rng = np.random.default_rng(2441578962024311353 % 2**63)

def stats_2d(steps, amps=None):
    """steps: (S, L). Down-cross at column j+1: D[j] > 0 >= D[j+1], j <= L-5."""
    D = np.cumsum(steps, axis=1)
    A = np.ones_like(steps) if amps is None else amps
    dn = (D[:, :-4] > 0) & (D[:, 1:-3] <= 0)
    r, c = np.nonzero(dn)                     # crossing: D[r, c+1] <= 0
    V = -D[r, c+1]
    a_next = A[r, c+2] if A.ndim == 2 else np.ones(r.size)
    r1 = D[r, c+2] > 0
    r2 = r1 | (D[r, c+3] > 0)
    r3 = r2 | (D[r, c+4] > 0)
    x = np.clip(V/a_next, 0, 1)
    return dict(n_cross=int(r.size),
                one_step=float(r1.mean()), two_step=float(r2.mean()),
                three_step=float(r3.mean()),
                pred_one_step=float((np.arccos(x)/np.pi).mean()),
                overshoot_mean=float(V.mean()))

S, L = 60_000, 1000
# (a) iid uniform phases, unit envelope
out = stats_2d(np.cos(rng.uniform(0, 2*np.pi, (S, L))))
out['model'] = 'iid'
print(json.dumps(out), flush=True)

# (b) frozen lattice: per-row (beta, p)
beta = rng.uniform(0, 2*np.pi, (20_000, 1))
p = rng.uniform(0, 1, (20_000, 1))
th = np.pi*(1 + 4*p)
m = np.arange(4000)[None, :]
out = stats_2d(np.cos(beta + m*th))
out['model'] = 'lattice'
print(json.dumps(out), flush=True)

# (c) iid phases, growing envelope a_m = (1 - m/(3L))^{-1/2} within each row
env = (1 - np.arange(L)/(3*L))**-0.5
amps = np.broadcast_to(env, (S, L)).copy()
out = stats_2d(amps*np.cos(rng.uniform(0, 2*np.pi, (S, L))), amps)
out['model'] = 'envelope'
print(json.dumps(out), flush=True)
