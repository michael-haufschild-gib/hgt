"""Run on Runpod only. Discover Stein residuals; no quadrature or proof oracle.

Each independent linear program uses one native thread. Output coefficients
require separate exact verification before any mathematical claim.
"""
import os
for name in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[name] = '1'
import json
import math
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
import numpy as np
from scipy.optimize import linprog


def solve(job):
    which, degree, direction = job[:3]
    target = job[3] if len(job) > 3 else None
    polys = {
        'mass': [1],
        'ward1': [0, 4, -1],
        'ward2': [0, 0, 0, 8, -1],
        'ward3': [0, 0, 0, 0, 0, 12, -1],
    }
    p = polys[which]
    kmax = len(p) - 1
    shape = (kmax + 1, degree)
    variables = list(np.ndindex(shape))
    scale = 4.
    bern = np.zeros((degree + 1, degree + 1))
    for i in range(degree + 1):
        for j in range(i + 1):
            bern[i, j] = math.comb(i, j) / math.comb(degree, j)
    matrices = []
    rhs = np.repeat([c / scale**k for k, c in enumerate(p)], degree + 1)
    for pi in (3.14159, 3.14160):
        matrix = np.zeros(((kmax + 1) * (degree + 1), len(variables)))
        for col, (k, j0) in enumerate(variables):
            j = j0 + 1
            mono = np.zeros((kmax + 1, degree + 1))
            mono[k, j - 1] += 2 * pi
            mono[k, j] -= 2.5 - 2 * j
            if k:
                mono[k - 1, j] -= scale * k
            matrix[:, col] = (mono @ bern.T).ravel()
        matrices.append(matrix)
    matrix = np.vstack(matrices)
    rhs = np.tile(rhs, 2)
    objective = np.array([float(k == 0) for k, j in variables])
    sign = 1 if direction == 'lower' else -1
    if target is None:
        cost, aub, bub, aeq, beq = -sign * objective, sign * matrix, sign * rhs, None, None
    else:
        cost = np.r_[np.zeros(len(variables)), -1.]
        aub = np.c_[sign * matrix, np.ones(len(rhs))]
        bub = sign * rhs
        aeq = np.array([np.r_[objective, 0.]])
        beq = [float(target)]
    result = linprog(cost, A_ub=aub, b_ub=bub, A_eq=aeq, b_eq=beq,
                     bounds=[(None, None)] * len(cost),
                     method='highs', options={'dual_feasibility_tolerance': 1e-9,
                                              'primal_feasibility_tolerance': 1e-9})
    output = dict(which=which, degree=degree, direction=direction,
                  status=result.message, success=result.success, scale=scale)
    if result.success:
        sol = result.x[:len(variables)]
        output.update(bound=float(objective @ sol),
                      min_slack=float(np.min(sign * (rhs - matrix @ sol))),
                      coefficients=sol.reshape(shape).tolist())
    return output


if __name__ == '__main__':
    jobs = [(p, j, side) for j in (4, 8, 12, 20)
            for p in ('mass', 'ward1', 'ward2', 'ward3')
            for side in ('lower', 'upper')]
    with ProcessPoolExecutor(max_workers=min(16, os.cpu_count() or 1)) as pool:
        results = list(pool.map(solve, jobs))
    Path('search-results.json').write_text(json.dumps(results, indent=2) + '\n')
    for r in results:
        print(r['which'], r['degree'], r['direction'],
              r.get('bound'), r.get('min_slack'), r['status'], flush=True)
