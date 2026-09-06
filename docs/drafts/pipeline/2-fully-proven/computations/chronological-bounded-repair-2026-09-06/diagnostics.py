"""Independent residual checks and coefficient ablations; run only on Runpod.

No optimization, no asymptotic inference, and no numerical proof inputs.
The ablations test the retained vectors, not the necessity of a coefficient class.
"""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '4'
os.environ['OMP_NUM_THREADS'] = '4'
import json, concurrent.futures
import numpy as np
import mpmath as mp
import experiment as ex


def diagnose(n):
    mp.mp.dps = 80
    A, e, t, _ = ex.design(n, 52, True)
    k = np.arange(1, n + 1)
    mu = ex.mobius(n)[1:]
    rows = {}
    for C in [1, 2]:
        a = np.loadtxt(ex.OUT / ('coeff_box%d_%d.csv' % (C, n)),
                       delimiter=',', skiprows=1)[:, 2]
        variants = {'retained': a.copy()}
        b = a.copy()
        b[mu == 0] = 0
        variants['zero_nonsquarefree'] = b
        for m in [4, 8, 16]:
            b = a.copy()
            b[:m] = mu[:m]
            variants['reset_first_%d_to_mobius' % m] = b
        energies = {label: float(np.linalg.norm(A @ b + e))
                    for label, b in variants.items()}
        # New points: logarithmic grid plus points of large measured energy density.
        grid = np.geomspace(1e-7 / n, 40, 96)
        profile = np.load(ex.OUT / ('profile_%d.npz' % n))
        density = profile['t'] * profile['box2'] ** 2
        chosen = profile['t'][np.argsort(density)[-16:]]
        points = np.unique(np.r_[grid, chosen])
        direct = np.exp(-points) + ex.bose_h(points[:, None] * k) @ a
        errors = []
        values = []
        ma = [mp.mpf(float(x)) for x in a]
        for point, value in zip(points, direct):
            mt = mp.mpf(float(point))
            reference = mp.exp(-mt) + mp.fsum(
                ak * (1 / ((j + 1) * mt) - 1 / mp.expm1((j + 1) * mt))
                for j, ak in enumerate(ma))
            error = float(abs(mp.mpf(float(value)) - reference))
            errors.append(error)
            values.append({'t': float(point), 'residual_80_digit': mp.nstr(reference, 35),
                           'float_absolute_error': error})
        rows['box%d' % C] = {
            'norms_after_ablation': energies,
            'max_abs_nonsquarefree_coefficient': float(np.max(np.abs(a[mu == 0]))),
            'mean_abs_nonsquarefree_coefficient': float(np.mean(np.abs(a[mu == 0]))),
            'first_16_coefficients': a[:16].tolist(),
            'high_precision_digits': 80,
            'high_precision_sample_count': len(points),
            'maximum_absolute_residual_discrepancy': max(errors),
            'high_precision_samples': values}
    return {'N': n, 'diagnostics': rows}


if __name__ == '__main__':
    with concurrent.futures.ProcessPoolExecutor(max_workers=4) as pool:
        result = list(pool.map(diagnose, [128, 512]))
    (ex.OUT / 'diagnostics.json').write_text(json.dumps(result, indent=2))
    data = json.loads((ex.OUT / 'results.json').read_text())
    summary = []
    for row in data['results']:
        models = row['models']
        item = {'N': row['N'],
                'norms': {label: m['l2_norm'] for label, m in models.items()}}
        for C in [1, 2]:
            m = models['box%d' % C]
            item['box%d' % C] = {
                key: m[key] for key in ['max_abs_coefficient', 'mesh_energy_difference',
                    'first_eight_coefficients', 'harmonic_coefficient_sum',
                    'energy_regions_t_lt_1_over_n__middle__t_ge_1',
                    'quadrature_primal_dual_gap', 'quadrature_dual_lower_bound']}
            item['box%d' % C]['relative_mesh_energy_difference'] = (
                m['mesh_energy_difference'] / m['energy'])
        summary.append(item)
    (ex.OUT / 'summary.json').write_text(json.dumps(summary, indent=2))
    for row in result:
        print(json.dumps({'N': row['N'], 'boxes': {label: {
            'ablation_norms': m['norms_after_ablation'],
            'max_float_error': m['maximum_absolute_residual_discrepancy'],
            'max_nonsquarefree_coefficient': m['max_abs_nonsquarefree_coefficient']}
            for label, m in row['diagnostics'].items()}}), flush=True)
