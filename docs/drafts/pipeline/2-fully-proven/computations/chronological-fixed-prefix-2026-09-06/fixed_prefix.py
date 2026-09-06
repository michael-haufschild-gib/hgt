"""Frozen fixed-prefix diagnostic. Run on Runpod; never a Lean proof input.

Four independent workers, four BLAS threads each. Every selected vector is
exactly feasible after assigning its fixed prefix and clipping its free tail.
"""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '4'
os.environ['OMP_NUM_THREADS'] = '4'
import json, math, pathlib, time, concurrent.futures
import numpy as np
from scipy.optimize import lsq_linear, linprog
from scipy.sparse import eye, hstack, vstack
import kernel_reference as ex

OUT = pathlib.Path(__file__).resolve().parent
OLD = pathlib.Path('/root/chronological-bounded-repair-20260906')
SIZES = [128, 256, 512]


def prefixes(n):
    return sorted(set([4, 8, 16, math.isqrt(n), n//4]))


def solve_case(task):
    n, m = task
    started = time.time()
    A, e, _, _ = ex.design(n, 20)
    mu = ex.mobius(n)[1:].astype(float)
    B, f = A[:, m:], e + A[:, :m] @ mu[:m]
    nf = n-m
    pool = {1: [], 2: []}
    diagnostics = []

    def add(C, label, tail):
        a = np.r_[mu[:m], np.clip(tail, -C, C)]
        pool[C].append((label, a))

    for C in [1, 2]:
        add(C, 'fixed_prefix_zero_tail', np.zeros(nf))
        add(C, 'raw_mobius', mu[m:])
        old = np.loadtxt(OLD/('coeff_box%d_%d.csv' % (C, n)), delimiter=',', skiprows=1)[:, 2]
        add(C, 'old_vector_prefix_reset', old[m:])
        for scale in [1., 1e5]:
            fit = lsq_linear(scale*B, -scale*f, bounds=(-C, C), method='bvls',
                             tol=1e-14, max_iter=1000)
            add(C, 'bvls_scale_%g' % scale, fit.x)
            r = B @ np.clip(fit.x, -C, C) + f
            diagnostics.append({'C': C, 'scale': scale, 'status': int(fit.status),
                                'iterations': int(fit.nit), 'energy': float(r@r)})

    u, s, vh = np.linalg.svd(B, full_matrices=False)
    projection = u.T @ f
    inequalities = vstack([hstack([eye(nf), -np.ones((nf, 1))]),
                           hstack([-eye(nf), -np.ones((nf, 1))])], format='csr')
    costs = []
    rank_limit = min(nf, 45, int(np.sum(s > 1e-13*s[0])))
    for rank in range(1, rank_limit+1):
        target = -projection[:rank]/s[:rank]
        fit = linprog(np.r_[np.zeros(nf), 1.], A_ub=inequalities, b_ub=np.zeros(2*nf),
                      A_eq=np.column_stack([vh[:rank], np.zeros(rank)]), b_eq=target,
                      bounds=[(None, None)]*nf+[(0, None)], method='highs',
                      options={'primal_feasibility_tolerance': 1e-10,
                               'dual_feasibility_tolerance': 1e-10})
        if not fit.success:
            costs.append({'rank': rank, 'status': int(fit.status), 'message': fit.message})
            break
        a = fit.x[:nf]
        a += vh[:rank].T @ (target-vh[:rank]@a)
        actual = float(np.max(np.abs(a)))
        costs.append({'rank': rank, 'lp_minimum_box': float(fit.x[-1]),
                      'corrected_box': actual, 'singular_value': float(s[rank-1])})
        for C in [1, 2]:
            if actual <= C*(1+1e-10):
                add(C, 'singular_modes_%d' % rank, a)
        if fit.x[-1] > 2.0001:
            break
    best = {}
    for C in [1, 2]:
        if C == 2:
            pool[C] += pool[1]
        best[C] = min(pool[C], key=lambda z: float(np.linalg.norm(A@z[1]+e)))
    np.savez_compressed(OUT/('pool_%d_%d.npz' % (n, m)),
                        box1=best[1][1], box2=best[2][1])
    row = {'N': n, 'm': m, 'seconds': time.time()-started,
           'labels': {str(C): best[C][0] for C in [1, 2]},
           'bvls': diagnostics, 'singular_modes': costs, 'rank_limit': rank_limit}
    print(json.dumps({'event': 'case_done', 'N': n, 'm': m, 'seconds': row['seconds']}), flush=True)
    return row


def assess(n, m, C, a, label, A, e, V, v, tv):
    assert np.array_equal(a[:m], ex.mobius(n)[1:m+1])
    assert np.max(np.abs(a)) <= C
    r, vr = A@a+e, V@a+v
    B, f = A[:, m:], e+A[:, :m]@a[:m]
    g = B.T@r
    dual = 2*float(f@r)-float(r@r)-2*C*float(np.abs(g).sum())
    regions = [tv < 1/n, (tv >= 1/n) & (tv < 1), tv >= 1]
    return {'N': n, 'm': m, 'C': C, 'origin': label,
            'l2_norm': float(np.linalg.norm(vr)), 'energy': float(vr@vr),
            'training_energy': float(r@r), 'mesh_energy_difference': float(abs(vr@vr-r@r)),
            'quadrature_dual_lower_bound': dual, 'quadrature_primal_dual_gap': float(r@r)-dual,
            'max_abs_coefficient': float(np.max(np.abs(a))),
            'harmonic_moment': float(np.sum(a/np.arange(1, n+1))),
            'energy_regions': [float(vr[z]@vr[z]) for z in regions],
            'left_tail_energy_bound': 1e-30, 'fixed_prefix_exact': True}


def main():
    started = time.time()
    tasks = [(n, m) for n in SIZES for m in prefixes(n)]
    with concurrent.futures.ProcessPoolExecutor(max_workers=4) as pool:
        diags = list(pool.map(solve_case, tasks))
    diag_map = {(r['N'], r['m']): r for r in diags}
    retained = {}
    rows = []
    for n in SIZES:
        A, e, _, _ = ex.design(n, 20)
        V, v, tv, _ = ex.design(n, 36, True)
        stronger = {1: [], 2: []}
        for m in reversed(prefixes(n)):
            candidates = np.load(OUT/('pool_%d_%d.npz' % (n, m)))
            for C in [1, 2]:
                opts = [(diag_map[n, m]['labels'][str(C)], candidates['box%d' % C])]
                opts += [('stronger_prefix_%d' % mm, aa) for mm, aa in stronger[C]]
                for (nn, mm, cc), aa in retained.items():
                    if nn < n and mm == m and cc == C:
                        opts.append(('padded_N_%d' % nn, np.pad(aa, (0, n-nn))))
                if C == 2:
                    opts.append(('included_C1', retained[n, m, 1]))
                label, a = min(opts, key=lambda z: float(np.linalg.norm(A@z[1]+e)))
                retained[n, m, C] = a
                stronger[C].append((m, a))
                row = assess(n, m, C, a, label, A, e, V, v, tv)
                rows.append(row)
                np.savetxt(OUT/('coeff_N%d_m%d_C%d.csv' % (n, m, C)),
                           np.column_stack([np.arange(1, n+1), ex.mobius(n)[1:], a]),
                           delimiter=',', header='k,mu_k,a_k', comments='', fmt=['%d','%d','%.17g'])
                print(json.dumps(row), flush=True)
    result = {'status': 'exploratory_feasible_vectors_not_proof_or_certified_optima',
              'workers': 4, 'blas_threads_per_worker': 4, 'seconds': time.time()-started,
              'protocol': {'sizes': SIZES, 'prefixes': {str(n): prefixes(n) for n in SIZES},
                           'budgets': [1, 2]}, 'results': rows, 'solver_diagnostics': diags}
    (OUT/'results.json').write_text(json.dumps(result, indent=2))
    print(json.dumps({'event': 'complete', 'seconds': result['seconds']}), flush=True)


if __name__ == '__main__':
    main()
