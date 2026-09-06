"""Test whether the unsquared obstruction persists after squaring. Runpod only."""
import os
for name in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[name] = '1'
import json
from concurrent.futures import ProcessPoolExecutor, as_completed
import numpy as np
import mpmath as mp
from factor_probe import valid, system_np, system_mp, seeds


def one(job):
    m, seed = job
    z = np.array(seed)
    for _ in range(100):
        f, jac = system_np(z)
        err = np.max(np.abs(f))
        if err < 5e-9:
            break
        step = np.linalg.solve(jac, -f)
        rate = 1.
        while rate > 2.**-40:
            nxt = z + rate*step
            if valid(nxt) and np.max(np.abs(system_np(nxt)[0])) < err:
                z = nxt
                break
            rate *= .5
        else:
            return {'m': m, 'error': 'double line search stalled', 'residual': float(err)}
    else:
        return {'m': m, 'error': 'double iteration limit'}
    mp.mp.dps = 140
    zz = mp.matrix([mp.mpf(str(x)) for x in z])
    for _ in range(12):
        f, jac = system_mp(zz)
        if max(abs(x) for x in f) < mp.mpf('1e-112'):
            break
        # Eliminate the diagonal contact block analytically; only an m by m
        # high-precision linear system remains, not a 2m by 2m system.
        diag = [jac[m+i, m+i] for i in range(m)]
        ratio = [jac[i, m+i] / diag[i] for i in range(m)]
        reduced = mp.matrix([[jac[i,j] - ratio[i]*jac[m+i,j]
                              for j in range(m)] for i in range(m)])
        rhs = mp.matrix([-f[i] + ratio[i]*f[m+i] for i in range(m)])
        dr = mp.lu_solve(reduced, rhs)
        dc = [(-f[m+i] - mp.fsum(jac[m+i,j]*dr[j] for j in range(m))) / diag[i]
              for i in range(m)]
        zz += mp.matrix(list(dr) + dc)
    f, _ = system_mp(zz)
    err = max(abs(x) for x in f)
    if not valid(list(zz)) or err > mp.mpf('1e-105'):
        return {'m': m, 'error': 'high precision validation failed', 'residual': str(err)}
    d = list(zz[:m])
    sx = mp.fsum(x*(2-x) for x in d)
    delta = mp.power(4, 1-m)*mp.fprod((1-x)**2 for x in d)/sx
    return {'m': m, 'delta': str(delta), 'root_c': [str(x) for x in d],
            'contacts': [str(x) for x in zz[m:]], 'residual': str(err)}


if __name__ == '__main__':
    results = []
    # Recompute the low degrees too: the new precision is needed in nearly
    # singular moment matrices, and this independently checks block Newton.
    with ProcessPoolExecutor(max_workers=24) as pool:
        for future in as_completed([pool.submit(one, job) for job in seeds(64)]):
            row = future.result()
            results.append(row)
            print('degree', row['m'], row.get('error', 'converged'), flush=True)
    results.sort(key=lambda r: r['m'])
    out = {'results': results, 'complete': all('delta' in r for r in results)}
    json.dump(out, open('extension-results.json', 'w'), indent=2)
    if not out['complete']:
        raise SystemExit('At least one degree failed: no moment analysis.')
    mp.mp.dps = 125
    old = json.load(open('factor-results.json'))
    rho = mp.mpf(old['rho'])
    gaps = [mp.mpf(row['delta']) for row in results]
    a = [g/gaps[0]/rho**n for n, g in enumerate(gaps)]
    out['prior_relative_errors'] = [str(abs(gaps[i]/mp.mpf(old['results'][i]['delta'])-1))
                                    for i in range(32)]
    out['moment_tests'] = []
    for power in (1, 2):
        seq = [x**power for x in a]
        for size in (8, 12, 16, 20, 24, 28, 32):
            for shift in (0, 1):
                mat = mp.matrix([[seq[i+j+shift] for j in range(size)] for i in range(size)])
                eigenvalues = mp.eigsy(mat, eigvals_only=True)
                row = {'power': power, 'size': size, 'shift': shift,
                       'smallest_eigenvalue': str(eigenvalues[0]),
                       'negative_count': sum(v<0 for v in eigenvalues)}
                if shift == 0:
                    b = mat[1:, 1:]
                    v = mat[1:, 0]
                    row['zeroth_moment_schur_complement'] = str(mat[0,0] - (v.T*mp.lu_solve(b,v))[0])
                out['moment_tests'].append(row)
                print('moment', power, size, shift, mp.nstr(eigenvalues[0], 9), flush=True)
    json.dump(out, open('extension-results.json', 'w'), indent=2)
