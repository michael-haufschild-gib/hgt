"""Frozen D2: quarter-prefix fits near the theoretical error floor.

Run on Runpod. Two workers, eight BLAS threads each. LP mode cancellation
only; finite feasible vectors, not certified optima. Never Lean proof inputs.
"""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '8'
os.environ['OMP_NUM_THREADS'] = '8'
import pathlib, json, time, concurrent.futures
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import eye, hstack, vstack
import kernel_reference as ex
# kernel_reference's historical default is four BLAS threads before importing
# NumPy; NumPy is already loaded here with eight, so this does not reconfigure it.

OUT = pathlib.Path(__file__).resolve().parent


def case(n):
    started = time.time()
    m = n//4
    mu = ex.mobius(n)[1:].astype(float)
    A, e, _, _ = ex.design(n, 24)
    V, v, tv, _ = ex.design(n, 44, True)
    B, f = A[:, m:], e+A[:, :m]@mu[:m]
    nf = n-m
    u, s, vh = np.linalg.svd(B, full_matrices=False)
    projection = u.T@f
    ub = vstack([hstack([eye(nf), -np.ones((nf, 1))]),
                 hstack([-eye(nf), -np.ones((nf, 1))])], format='csr')
    pools = {1: [('zero_tail', np.r_[mu[:m], np.zeros(nf)])],
             2: [('zero_tail', np.r_[mu[:m], np.zeros(nf)])]}
    costs = []
    rank_limit = min(nf, 45, int(np.sum(s > 2e-15*s[0])))
    for rank in range(1, rank_limit+1):
        target = -projection[:rank]/s[:rank]
        fit = linprog(np.r_[np.zeros(nf), 1.], A_ub=ub, b_ub=np.zeros(2*nf),
                      A_eq=np.column_stack([vh[:rank], np.zeros(rank)]), b_eq=target,
                      bounds=[(None, None)]*nf+[(0, None)], method='highs',
                      options={'primal_feasibility_tolerance': 1e-10,
                               'dual_feasibility_tolerance': 1e-10})
        if not fit.success:
            costs.append({'rank': rank, 'status': int(fit.status), 'message': fit.message})
            break
        a = fit.x[:nf]
        a += vh[:rank].T@(target-vh[:rank]@a)
        actual = float(np.max(np.abs(a)))
        costs.append({'rank': rank, 'lp_box': float(fit.x[-1]), 'corrected_box': actual,
                      'singular_value': float(s[rank-1])})
        for C in [1, 2]:
            if actual <= C*(1+1e-10):
                pools[C].append(('singular_modes_%d' % rank, np.r_[mu[:m], np.clip(a, -C, C)]))
        if fit.x[-1] > 2.0001:
            break
    rows = []
    for C in [1, 2]:
        if C == 2:
            pools[C] += pools[1]
        label, a = min(pools[C], key=lambda z: float(np.linalg.norm(A@z[1]+e)))
        assert np.array_equal(a[:m], mu[:m]) and np.max(np.abs(a)) <= C
        r, vr = A@a+e, V@a+v
        g = B.T@r
        dual = 2*float(f@r)-float(r@r)-2*C*float(np.abs(g).sum())
        row = {'N': n, 'm': m, 'C': C, 'origin': label,
               'l2_norm': float(np.linalg.norm(vr)), 'energy': float(vr@vr),
               'training_energy': float(r@r), 'mesh_difference': float(abs(vr@vr-r@r)),
               'quadrature_dual_lower_bound': dual,
               'quadrature_primal_dual_gap': float(r@r)-dual,
               'harmonic_moment': float(np.sum(a/np.arange(1, n+1))),
               'max_abs_coefficient': float(np.max(np.abs(a))), 'fixed_prefix_exact': True}
        rows.append(row)
        np.savetxt(OUT/('coeff_N%d_m%d_C%d.csv' % (n, m, C)),
                   np.column_stack([np.arange(1, n+1), mu, a]), delimiter=',',
                   header='k,mu_k,a_k', comments='', fmt=['%d','%d','%.17g'])
    result = {'N': n, 'seconds': time.time()-started, 'results': rows, 'mode_costs': costs,
              'rank_limit': rank_limit, 'training_rows': len(e)}
    (OUT/('extension_%d.json' % n)).write_text(json.dumps(result, indent=2))
    print(json.dumps(result), flush=True)
    return result


if __name__ == '__main__':
    import mpmath as mp
    mp.mp.dps = 80
    rho = mp.zetazero(1)
    G = abs(mp.gamma(rho))
    # This is a numerical evaluation, not a certified location or Lean constant.
    floors = [{'N': n, 'C': C, 'illustrative_floor': str(G/(4*mp.sqrt(mp.log(1+8*(1+C*n)/G))))}
              for n in [512, 1024, 2048, 4096] for C in [1, 2]]
    with concurrent.futures.ProcessPoolExecutor(max_workers=2) as pool:
        results = list(pool.map(case, [1024, 2048, 4096]))
    (OUT/'extension.json').write_text(json.dumps({'status': 'exploratory_not_proof',
        'numerical_zero': str(rho), 'numerical_gamma_modulus': str(G),
        'illustrative_floors': floors, 'results': results}, indent=2))
