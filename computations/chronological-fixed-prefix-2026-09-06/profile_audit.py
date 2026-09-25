"""Independent precision audit and blind logarithmic-frequency scan on Runpod.

Zeta zeros are used only AFTER fitting as a diagnostic reference. No values
from this script are proof inputs. Four cases, four BLAS threads per worker.
"""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '4'
os.environ['OMP_NUM_THREADS'] = '4'
import pathlib, json, concurrent.futures
import numpy as np
import mpmath as mp
import kernel_reference as ex

OUT = pathlib.Path(__file__).resolve().parent


def long_h(x):
    out = np.empty_like(x)
    small = x < np.longdouble('0.25')
    y = x[small]
    out[small] = (np.longdouble('.5')-y/12+y**3/720-y**5/30240+y**7/1209600
                  -y**9/47900160+691*y**11/1307674368000)
    y = x[~small]
    out[~small] = 1/y-np.exp(-y)/(-np.expm1(-y))
    return out


def case(task):
    if len(task) == 2:
        n, C = task
        m, prefix = n//4, 'balanced'
    else:
        n, C, m, prefix = task
    a = np.loadtxt(OUT/('%s_coeff_N%d_m%d_C%d.csv' % (prefix, n, m, C)),
                   delimiter=',', skiprows=1)[:, 2]
    V, v, tv, delta = ex.design(n, 60, True)
    vr = V@a+v
    points = np.unique(np.r_[np.geomspace(1e-6/n, 30, 88), tv[np.argsort(np.abs(vr[:-1]))[-24:]]])
    approx = np.exp(-points)+ex.bose_h(points[:, None]*np.arange(1, n+1))@a
    mp.mp.dps = 80
    aa = [mp.mpf(float(b)) for b in a]
    errors = []
    for x, y in zip(points, approx):
        z = mp.mpf(float(x))
        exact = mp.exp(-z)+mp.fsum(b*(1/(k*z)-1/mp.expm1(k*z)) for k, b in enumerate(aa, 1))
        errors.append(float(abs(exact-mp.mpf(float(y)))))
    x = np.linspace(np.log(delta), np.log(ex.T_MAX), 8192)
    t = np.exp(x).astype(np.longdouble)
    al = a.astype(np.longdouble)
    kl = np.arange(1, n+1, dtype=np.longdouble)
    r = np.empty(len(t), dtype=np.longdouble)
    for j in range(0, len(t), 256):
        tt = t[j:j+256]
        r[j:j+256] = np.exp(-tt)+long_h(tt[:, None]*kl)@al
    profile = np.asarray(np.sqrt(t)*r, dtype=float)
    moment = float(np.sum(al/kl, dtype=np.longdouble))
    frequencies = np.linspace(0, 30, 1201)
    transforms = np.empty(len(frequencies), dtype=complex)
    for j, w in enumerate(frequencies):
        transforms[j] = np.trapz(profile*np.exp(1j*w*x), x)+moment*ex.T_MAX**(-.5+1j*w)/(.5-1j*w)
    rho = mp.zetazero(1)
    gamma = complex(mp.gamma(rho))
    omega = float(mp.im(rho))
    value = np.trapz(profile*np.exp(1j*omega*x), x)+moment*ex.T_MAX**(-.5+1j*omega)/(.5-1j*omega)
    mask = frequencies >= 2
    peak = np.flatnonzero(mask)[np.argmax(np.abs(transforms[mask]))]
    output = 'log_profile_N%d_C%d.npz' % (n, C) if prefix == 'balanced' else 'log_profile_N%d_m%d_C%d.npz' % (n, m, C)
    np.savez_compressed(OUT/output,
                        x=x, profile=profile, frequency=frequencies, transform=transforms)
    row = {'N': n, 'm': m, 'C': C, 'mesh_order': 60, 'l2_norm': float(np.linalg.norm(vr)),
           'longdouble_profile_l2_norm': float(np.sqrt(np.trapz(profile**2, x)+moment**2/ex.T_MAX)),
           'longdouble_mantissa_bits': int(np.finfo(np.longdouble).nmant),
           'fixed_prefix_exact': bool(np.array_equal(a[:m], ex.mobius(n)[1:m+1])),
           'max_abs_coefficient': float(np.max(np.abs(a))), 'point_count': len(points),
           'mpmath_digits': 80, 'max_residual_discrepancy': max(errors),
           'blind_peak_frequency_on_2_to_30': float(frequencies[peak]),
           'first_zero_ordinate_reference': omega,
           'mellin_at_first_zero': [value.real, value.imag],
           'gamma_reference': [gamma.real, gamma.imag],
           'mellin_invariant_relative_error': float(abs(value-gamma)/abs(gamma))}
    print(json.dumps(row), flush=True)
    return row


def plot(rows):
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    fig, axes = plt.subplots(1, 3, figsize=(14, 4), layout='constrained')
    for C in [1, 2]:
        subset = [r for r in rows if r['C'] == C]
        axes[0].loglog([r['N'] for r in subset], [r['l2_norm'] for r in subset],
                       'o-', label='Quarter prefix, C=%d' % C)
    axes[0].set(xlabel='N', ylabel='Measured full L² error', title='Finite fits; no convergence claim')
    axes[0].legend(fontsize=8)
    for C in [1, 2]:
        d = np.load(OUT/('log_profile_N4096_C%d.npz' % C))
        axes[1].plot(d['x'], d['profile'], label='C=%d' % C)
        axes[2].plot(d['frequency'], np.abs(d['transform']), label='C=%d' % C)
    axes[1].set(xlim=(-20, 0), xlabel='log t', ylabel='sqrt(t) r(t)', title='Residual at N=4096')
    axes[2].axvline(rows[0]['first_zero_ordinate_reference'], color='gray', ls='--', lw=1,
                    label='First zero: reference only')
    axes[2].set(xlabel='Logarithmic frequency', ylabel='Mellin modulus', title='Blind frequency scan')
    axes[2].legend(fontsize=8)
    fig.savefig(OUT/'fixed_prefix_comparison.png', dpi=170)


if __name__ == '__main__':
    with concurrent.futures.ProcessPoolExecutor(max_workers=4) as pool:
        rows = list(pool.map(case, [(n, C) for n in [512, 1024, 2048, 4096] for C in [1, 2]]))
    (OUT/'profile_audit.json').write_text(json.dumps(rows, indent=2))
    plot(rows)
