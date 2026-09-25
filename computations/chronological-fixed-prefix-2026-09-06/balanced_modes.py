"""D2 solver falsification: trade residual modes instead of exact prefix cancellation.

Run on Runpod. Four BLAS threads, two independent N workers. Preserve the
well-conditioned singular modes exactly, minimize the largest remaining modal
residual by LP, then check the complete residual and original coefficient box.
"""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '4'
os.environ['OMP_NUM_THREADS'] = '4'
import pathlib, json, time, concurrent.futures
import numpy as np
from scipy.optimize import linprog
import kernel_reference as ex

OUT = pathlib.Path(__file__).resolve().parent


def case(n):
    started = time.time()
    m, nf = n//4, n-n//4
    mu = ex.mobius(n)[1:].astype(float)
    A, e, _, _ = ex.design(n, 24)
    V, v, _, _ = ex.design(n, 52, True)
    B, f = A[:, m:], e+A[:, :m]@mu[:m]
    u, s, vh = np.linalg.svd(B, full_matrices=False)
    projection = u.T@f
    hi = min(24, int(np.sum(s > 2e-16*s[0])))
    diags, rows, truncation = [], [], []
    for rank in [14, 16, 18, 20]:
        q = f-u[:, :rank]@projection[:rank]
        # Approximate exact-SVD lower bound. Floating point, NOT a certificate.
        truncation.append({'rank': rank, 'orthogonal_target_norm': float(np.linalg.norm(q)),
                           'next_singular_value': float(s[rank]),
                           'C1_tail_capacity_bound': float(np.sqrt(nf)*s[rank]),
                           'approx_C1_lower_bound': float(np.linalg.norm(q)-np.sqrt(nf)*s[rank])})
    selected = {}
    for C in [1, 2]:
        old = np.loadtxt(OUT/('coeff_N%d_m%d_C%d.csv' % (n, m, C)), delimiter=',', skiprows=1)[:, 2]
        pool = [('exact_modes_baseline', old)]
        for lo in [8, 10, 12]:
            scale = s[lo]
            tail = (s[lo:hi]/scale)[:, None]*vh[lo:hi]
            target = projection[lo:hi]/scale
            fit = linprog(np.r_[np.zeros(nf), 1.],
                          A_ub=np.vstack([np.column_stack([tail, -np.ones(hi-lo)]),
                                          np.column_stack([-tail, -np.ones(hi-lo)])]),
                          b_ub=np.r_[-target, target],
                          A_eq=np.column_stack([vh[:lo], np.zeros(lo)]),
                          b_eq=-projection[:lo]/s[:lo],
                          bounds=[(-C*(1-1e-8), C*(1-1e-8))]*nf+[(0, None)],
                          method='highs', options={'primal_feasibility_tolerance': 1e-10,
                                                   'dual_feasibility_tolerance': 1e-10})
            diag = {'C': C, 'lo': lo, 'hi': hi, 'status': int(fit.status), 'message': fit.message}
            if fit.success:
                tail_a = fit.x[:nf]
                tail_a += vh[:lo].T@(-projection[:lo]/s[:lo]-vh[:lo]@tail_a)
                a = np.r_[mu[:m], np.clip(tail_a, -C, C)]
                rr = A@a+e
                diag.update({'lp_scaled_residual': float(fit.x[-1]),
                             'preclip_tail_bound': float(np.max(np.abs(tail_a))),
                             'training_norm': float(np.linalg.norm(rr))})
                pool.append(('balanced_%d_to_%d' % (lo, hi), a))
            diags.append(diag)
        if C == 2:
            pool.append(('included_C1', selected[1]))
        label, a = min(pool, key=lambda z: float(np.linalg.norm(A@z[1]+e)))
        assert np.array_equal(a[:m], mu[:m]) and np.max(np.abs(a)) <= C
        selected[C] = a
        r, vr = A@a+e, V@a+v
        row = {'N': n, 'm': m, 'C': C, 'origin': label,
               'l2_norm': float(np.linalg.norm(vr)), 'training_energy': float(r@r),
               'validation_energy': float(vr@vr), 'mesh_difference': float(abs(r@r-vr@vr)),
               'max_abs_coefficient': float(np.max(np.abs(a))), 'fixed_prefix_exact': True}
        rows.append(row)
        np.savetxt(OUT/('balanced_coeff_N%d_m%d_C%d.csv' % (n, m, C)),
                   np.column_stack([np.arange(1, n+1), mu, a]), delimiter=',',
                   header='k,mu_k,a_k', comments='', fmt=['%d', '%d', '%.17g'])
    result = {'N': n, 'seconds': time.time()-started, 'results': rows,
              'solver_diagnostics': diags, 'approximate_projection_bounds': truncation}
    (OUT/('balanced_%d.json' % n)).write_text(json.dumps(result, indent=2))
    print(json.dumps(result), flush=True)
    return result


if __name__ == '__main__':
    with concurrent.futures.ProcessPoolExecutor(max_workers=2) as pool:
        results = list(pool.map(case, [512, 1024, 2048, 4096]))
    (OUT/'balanced.json').write_text(json.dumps(results, indent=2))
