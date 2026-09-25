"""Numerical leads for the six-endpoint reversal form; never a proof certificate.
Run on the authorized Runpod host. Fix the first gap's sign using global sign symmetry.
Search all 16 remaining sign chambers, both output signs, and enclosure depths 0..6.
"""
import os
for key in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS', 'NUMEXPR_NUM_THREADS'):
    os.environ[key] = '1'
import itertools
import json
import time
from concurrent.futures import ProcessPoolExecutor
import numpy as np
import scipy
from scipy.optimize import minimize


def value_gradient(g, depth):
    a, b, c, d, e = g
    S = a+b+c+d+e
    M = b+c+d
    P = c*(27*a*e-S*M)
    grad = np.array([c*(27*e-M), c*(-M-S), 27*a*e-S*M+c*(-M-S),
                     c*(-M-S), c*(27*a-M)])
    if depth:
        return S**depth*P, S**depth*grad+depth*S**(depth-1)*P
    return P, grad


def search_task(task):
    depth, chamber, output_sign = task
    signs = np.array([1]+[1 if (chamber >> j) & 1 else -1 for j in range(4)])
    rng = np.random.default_rng(20260905+1000*depth+10*chamber+(output_sign+1))
    boundary = []
    for bits in itertools.product([0., 1.], repeat=5):
        row = np.array(bits)
        if row.sum():
            boundary.append(row/row.sum())
    candidates = np.vstack([np.array(boundary), rng.dirichlet(np.full(5, .45), 512)])
    scores = np.array([output_sign*value_gradient(w*signs, depth)[0] for w in candidates])
    selected = candidates[np.argsort(scores)[-8:]]
    best_index = int(np.argmax(scores))
    best_value = float(scores[best_index])
    best_weights = candidates[best_index]
    failed = 0
    for start in selected:
        def objective(w):
            value, gradient = value_gradient(w*signs, depth)
            return -output_sign*value, -output_sign*gradient*signs
        result = minimize(objective, start, jac=True, method='SLSQP', bounds=[(0., 1.)]*5,
                          constraints=[{'type': 'eq', 'fun': lambda w: w.sum()-1.,
                                        'jac': lambda w: np.ones(5)}],
                          options={'ftol': 1e-13, 'maxiter': 600})
        failed += int(not result.success)
        # Project small floating-point constraint residuals before reporting a probe.
        weights = np.maximum(result.x, 0.)
        weights /= weights.sum()
        score = output_sign*value_gradient(weights*signs, depth)[0]
        if score > best_value:
            best_value, best_weights = float(score), weights
    g = best_weights*signs
    return {'depth': depth, 'chamber': chamber, 'output_sign': output_sign,
            'signed_objective': best_value, 'gaps': g.tolist(), 'variation': float(np.abs(g).sum()),
            'displacement': float(g.sum()), 'value': float(value_gradient(g, depth)[0]),
            'failed_local_runs': failed, 'local_runs': 8}


if __name__ == '__main__':
    started = time.time()
    workers = min(24, os.cpu_count() or 1)
    tasks = list(itertools.product(range(7), range(16), [-1, 1]))
    with ProcessPoolExecutor(max_workers=workers) as pool:
        results = list(pool.map(search_task, tasks))
    best = [max((r for r in results if r['depth'] == k), key=lambda r: r['signed_objective'])
            for k in range(7)]
    report = {'scope': 'numerical leads only; no global optimality certificate',
              'workers': workers, 'numpy': np.__version__, 'scipy': scipy.__version__,
              'seconds': time.time()-started, 'tasks': len(tasks), 'best_by_depth': best,
              'failed_local_runs': sum(r['failed_local_runs'] for r in results),
              'chamber_results': results}
    with open('enclosure-results.json', 'w') as stream:
        json.dump(report, stream, indent=2)
    print(json.dumps({k: v for k, v in report.items() if k != 'chamber_results'}, indent=2))
