"""D3 independent mesh, 80-digit spot checks and logarithmic profiles on Runpod."""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '4'
os.environ['OMP_NUM_THREADS'] = '4'
import json, concurrent.futures
import numpy as np
from profile_audit import case, OUT


if __name__ == '__main__':
    with concurrent.futures.ProcessPoolExecutor(max_workers=2) as pool:
        rows = list(pool.map(case, [(4096, 1, m, 'wider') for m in [16, 128]]))
    (OUT/'wider_audit.json').write_text(json.dumps(rows, indent=2))
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    baseline = [r for r in json.loads((OUT/'profile_audit.json').read_text())
                if r['N'] == 4096 and r['C'] == 1][0]
    all_rows = rows+[baseline]
    fig, axes = plt.subplots(1, 3, figsize=(13, 3.8), layout='constrained')
    axes[0].bar([str(r['m']) for r in all_rows], [r['l2_norm'] for r in all_rows], color='#446ea4')
    axes[0].set(xlabel='Number of exact Möbius coefficients', ylabel='Measured full L² error',
                title='N=4096, coefficient bound one')
    for r in all_rows:
        m = r['m']
        name = 'log_profile_N4096_C1.npz' if m == 1024 else 'log_profile_N4096_m%d_C1.npz' % m
        d = np.load(OUT/name)
        axes[1].plot(d['x'], d['profile'], label='m=%d' % m)
        axes[2].plot(d['frequency'], np.abs(d['transform']), label='m=%d' % m)
    axes[1].set(xlim=(-20, 0), xlabel='log t', ylabel='sqrt(t) r(t)', title='Residual profiles')
    axes[1].legend(fontsize=8)
    axes[2].axvline(rows[0]['first_zero_ordinate_reference'], color='gray', ls='--', lw=1,
                    label='First zero reference')
    axes[2].set(xlabel='Logarithmic frequency', ylabel='Mellin modulus', title='Blind frequency scan')
    axes[2].legend(fontsize=8)
    fig.savefig(OUT/'wider_window_comparison.png', dpi=170)
