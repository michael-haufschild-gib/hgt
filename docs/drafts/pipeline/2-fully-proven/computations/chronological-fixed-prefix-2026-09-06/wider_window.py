"""Frozen D3: vary repair-window width, keeping C=1 and N=4096 fixed.
Run on Runpod with two workers and four BLAS threads each. No proof inputs.
"""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '4'
os.environ['OMP_NUM_THREADS'] = '4'
import pathlib, json, time, concurrent.futures
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import eye, hstack, vstack
import kernel_reference as ex

OUT = pathlib.Path(__file__).resolve().parent


def case(m):
    started = time.time()
    n, C = 4096, 1
    nf = n-m
    mu = ex.mobius(n)[1:].astype(float)
    A, e, _, _ = ex.design(n, 24)
    V, v, _, _ = ex.design(n, 60, True)
    B, f = A[:, m:], e+A[:, :m]@mu[:m]
    u, s, vh = np.linalg.svd(B, full_matrices=False)
    projection = u.T@f
    ub = vstack([hstack([eye(nf), -np.ones((nf, 1))]),
                 hstack([-eye(nf), -np.ones((nf, 1))])], format='csr')
    previous = np.loadtxt(OUT/('coeff_N512_m%d_C1.csv' % m), delimiter=',', skiprows=1)[:, 2]
    pool = [('padded_N512', np.pad(previous, (0, n-512)))]
    costs, balanced = [], []
    hi = min(55, int(np.sum(s > 2e-15*s[0])))
    best_rank = 1
    options = {'primal_feasibility_tolerance': 1e-10, 'dual_feasibility_tolerance': 1e-10,
               'ipm_optimality_tolerance': 1e-10, 'time_limit': 60}
    for rank in range(1, hi+1):
        target = -projection[:rank]/s[:rank]
        fit = linprog(np.r_[np.zeros(nf), 1.], A_ub=ub, b_ub=np.zeros(2*nf),
                      A_eq=np.column_stack([vh[:rank], np.zeros(rank)]), b_eq=target,
                      bounds=[(None, None)]*nf+[(0, None)], method='highs-ipm', options=options)
        if not fit.success:
            costs.append({'rank': rank, 'status': int(fit.status), 'message': fit.message})
            break
        a = fit.x[:nf]
        a += vh[:rank].T@(target-vh[:rank]@a)
        actual = float(np.max(np.abs(a)))
        costs.append({'rank': rank, 'lp_box': float(fit.x[-1]), 'corrected_box': actual})
        print(json.dumps({'event': 'rank_done', 'm': m, 'rank': rank, 'cost': actual}), flush=True)
        if actual <= 1+1e-10:
            pool.append(('exact_modes_%d' % rank, np.r_[mu[:m], np.clip(a, -1, 1)]))
            best_rank = rank
        if fit.x[-1] > 1.0001:
            break
    for lo in sorted(set(max(1, best_rank-d) for d in [6, 4, 2])):
        scale = s[lo]
        tail = (s[lo:hi]/scale)[:, None]*vh[lo:hi]
        target = projection[lo:hi]/scale
        fit = linprog(np.r_[np.zeros(nf), 1.],
                      A_ub=np.vstack([np.column_stack([tail, -np.ones(hi-lo)]),
                                      np.column_stack([-tail, -np.ones(hi-lo)])]),
                      b_ub=np.r_[-target, target],
                      A_eq=np.column_stack([vh[:lo], np.zeros(lo)]),
                      b_eq=-projection[:lo]/s[:lo],
                      bounds=[(-1+1e-8, 1-1e-8)]*nf+[(0, None)], method='highs-ipm', options=options)
        diag = {'lo': lo, 'hi': hi, 'status': int(fit.status), 'message': fit.message}
        if fit.success:
            a = fit.x[:nf]
            a += vh[:lo].T@(-projection[:lo]/s[:lo]-vh[:lo]@a)
            full = np.r_[mu[:m], np.clip(a, -1, 1)]
            pool.append(('balanced_%d_to_%d' % (lo, hi), full))
            diag['training_norm'] = float(np.linalg.norm(A@full+e))
            diag['preclip_tail_bound'] = float(np.max(np.abs(a)))
        balanced.append(diag)
    label, a = min(pool, key=lambda z: float(np.linalg.norm(A@z[1]+e)))
    assert np.array_equal(a[:m], mu[:m]) and np.max(np.abs(a)) <= 1
    r, vr = A@a+e, V@a+v
    np.savetxt(OUT/('wider_coeff_N%d_m%d_C1.csv' % (n, m)),
               np.column_stack([np.arange(1, n+1), mu, a]), delimiter=',',
               header='k,mu_k,a_k', comments='', fmt=['%d', '%d', '%.17g'])
    row = {'N': n, 'm': m, 'C': 1, 'origin': label, 'l2_norm': float(np.linalg.norm(vr)),
           'training_energy': float(r@r), 'validation_energy': float(vr@vr),
           'mesh_difference': float(abs(r@r-vr@vr)), 'fixed_prefix_exact': True,
           'max_abs_coefficient': float(np.max(np.abs(a))), 'rank_limit': hi,
           'costs': costs, 'balanced_diagnostics': balanced, 'seconds': time.time()-started}
    print(json.dumps(row), flush=True)
    return row


if __name__ == '__main__':
    with concurrent.futures.ProcessPoolExecutor(max_workers=2) as pool:
        rows = list(pool.map(case, [16, 128]))
    (OUT/'wider_window.json').write_text(json.dumps(rows, indent=2))
