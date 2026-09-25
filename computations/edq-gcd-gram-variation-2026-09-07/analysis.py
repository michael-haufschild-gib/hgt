import json
with open('results.json') as f:
    data = json.load(f)
print('M source diagonal norm_interval variation_interval V/D_interval C1_interval max_r_abs_Cr')
for row in data['results']:
    one = row['groups'][0]
    maxima = max((g['r']*max(abs(g['lower']), abs(g['upper'])), g['r']) for g in row['groups'])
    print(row['M'], row['source'], '%.8f'%row['diagonal'],
          '[%.8f, %.8f]'%(row['signed_norm_lower'], row['signed_norm_upper']),
          '[%.8f, %.8f]'%(row['variation_lower'], row['variation_upper']),
          '[%.6f, %.6f]'%(row['variation_over_diagonal_lower'], row['variation_over_diagonal_upper']),
          '[%.8f, %.8f]'%(one['lower'], one['upper']), maxima)
    print('  definite-positive', sum(g['lower']>1e-7 for g in row['groups']),
          'definite-negative', sum(g['upper'] < -1e-7 for g in row['groups']),
          'classification', row['classification'])
print('controls', data['controls'])
print('wall', data['elapsed_seconds'])
import numpy as np
from experiment import mobius, LD, ORDER, START
print('analytic_series_remainder_bounds (excluding floating point):')
for row in data['results']:
    n = row['M']
    a = mobius(n).astype(LD)
    if row['source'] == 'averaged':
        d = np.arange(1, n+1, dtype=LD)
        a[1:] *= np.log(LD(n)/np.maximum(LD(row['X']), d))/np.log(LD(4))
    tau = np.zeros(n+1, dtype=np.int64)
    weighted = LD(0)
    diagonal_weight = LD(0)
    for q in range(1, n+1):
        tau[q::q] += 1
    for q in range(2, n+1):
        mass = np.sum(abs(a[q::q]), dtype=LD)
        weighted += tau[q]*mass*mass/q
        diagonal_weight += a[q]*a[q]/q
    factor = 1/((1-LD(1)/START)**2*LD(START-1)**(ORDER+1))
    print(n, row['source'], 'gcd_variation', float(4*weighted*factor),
          'diagonal', float(diagonal_weight*factor))
