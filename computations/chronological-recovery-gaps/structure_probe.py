"""Test distinct structural routes from saved gaps; run on authorized Runpod only."""
import json
import mpmath as mp

mp.mp.dps = 90
data = json.load(open('factor-results.json'))
rho = mp.mpf(data['rho'])
gaps = [mp.mpf(row['delta']) for row in data['results']]
scaled = [g / (gaps[0] * rho**n) for n, g in enumerate(gaps)]

def triangle(values):
    rows = [values]
    while len(rows[-1]) > 1:
        row = rows[-1]
        rows.append([a-b for a, b in zip(row, row[1:])])
    return rows

def negatives(rows, start=0):
    return [{'order': k, 'index': n, 'value': str(x)}
            for k, row in enumerate(rows) for n, x in enumerate(row)
            if k >= start and x < 0]

log_rows = triangle([mp.log(x) for x in scaled])
# For infinitely divisible Hausdorff moments, -log(a_n) must have
# nonpositive backward differences of every positive order.
gap_rows = triangle(scaled)
h = [(n+1)*x for n, x in enumerate(scaled)]
h_rows = triangle(h)
out = {
    'scaled_gap_hausdorff_violations': negatives(gap_rows),
    'log_complete_monotonicity_violations': negatives(log_rows, start=1),
    'scaled_n_gap_bernstein_violations': [
        {'order': k, 'index': n, 'value': str(x)}
        for k, row in enumerate(h_rows) for n, x in enumerate(row)
        if k >= 1 and x > 0],
    'scaled_gap_hankel_spectra': {},
    'scaled_gap_differences': [[str(x) for x in row] for row in gap_rows],
    'log_gap_differences': [[str(x) for x in row] for row in log_rows],
}
for shift in (0, 1):
    mat = mp.matrix([[scaled[i+j+shift] for j in range(16)] for i in range(16)])
    out['scaled_gap_hankel_spectra'][str(shift)] = [str(v) for v in mp.eigsy(mat, eigvals_only=True)]
json.dump(out, open('structure-results.json', 'w'), indent=2)
for key in out:
    if key.endswith('violations'):
        print(key, len(out[key]), out[key][:3])
print('smallest unsquared moment eigenvalue', min(mp.mpf(v) for row in out['scaled_gap_hankel_spectra'].values() for v in row))
