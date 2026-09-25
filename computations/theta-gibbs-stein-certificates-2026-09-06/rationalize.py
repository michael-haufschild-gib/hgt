"""Runpod coefficient discovery and exact rational check, independent of Lean.

This emits candidate proof data, not a proof of any real integral inequality.
"""
from search import solve
from fractions import Fraction as F
from math import comb
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor
import json

POLYS = {'mass': [1], 'ward1': [0, 4, -1],
         'ward2': [0, 0, 0, 8, -1], 'ward3': [0, 0, 0, 0, 0, 12, -1]}


def certify(job):
    raw = solve(job)
    if not raw['success']:
        return raw
    name, n, side, target = job
    q = [[F(round(c * 10**16), 10**16) for c in row] for row in raw['coefficients']]
    q[0][0] += F(target) - sum(q[0])
    p = POLYS[name]
    sig = 1 if side == 'lower' else -1
    residues = []
    for pi in (F(314159, 100000), F(3927, 1250)):
        mono = [[F(0)] * (n + 1) for k in p]
        for k, pk in enumerate(p):
            mono[k][0] = F(pk, 4**k)
        for k, row in enumerate(q):
            for j0, a in enumerate(row):
                j = j0 + 1
                mono[k][j-1] -= 2*pi*a
                mono[k][j] += (F(5,2) - 2*j)*a
                if k:
                    mono[k-1][j] += 4*k*a
        bern = [[sig * sum(F(comb(i, j), comb(n, j)) * mono[k][j]
                           for j in range(i+1))
                 for i in range(n+1)] for k in range(len(p))]
        residues.append(bern)
    mn = min(c for b in residues for row in b for c in row)
    return dict(which=name, degree=n, direction=side, target=target,
                exact_residuals_nonnegative=mn >= 0, exact_min_slack=str(mn),
                floating_min_slack=raw['min_slack'],
                coefficients=[[str(c) for c in row] for row in q],
                residuals=[[[str(c) for c in row] for row in b] for b in residues])


if __name__ == '__main__':
    jobs = [('mass', 4, 'lower', '0.1697'),
            ('ward1', 8, 'lower', '0.0846'),
            ('ward2', 8, 'upper', '0.010914'),
            ('ward3', 8, 'lower', '0.002205')]
    with ProcessPoolExecutor(max_workers=4) as pool:
        result = list(pool.map(certify, jobs))
    Path('rational-certificates.json').write_text(json.dumps(result, indent=2) + '\n')
    for r in result:
        print(r['which'], r.get('exact_residuals_nonnegative'),
              r.get('floating_min_slack'), r.get('exact_min_slack'), flush=True)
    c = F(3005, 2997)
    adjacent = 9 * F('0.0846') * F('0.002205') - 14*c*c*F('0.010914')**2
    relaxed = 45*F('0.0846')**2 - 16*c*c*(2-F('0.1697'))*F('0.010914')
    print('EXACT RATIO MARGINS', adjacent, relaxed, flush=True)
    assert adjacent > 0 and relaxed > 0
