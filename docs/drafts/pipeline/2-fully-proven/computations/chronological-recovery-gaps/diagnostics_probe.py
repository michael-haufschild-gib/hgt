"""Retain finite-test diagnostics from completed runs. Authorized Runpod only."""
import json
import mpmath as mp
mp.mp.dps = 125
data = json.load(open('extension-results.json'))
rho = mp.mpf(json.load(open('factor-results.json'))['rho'])
gaps = [mp.mpf(row['delta']) for row in data['results']]
ratios = [b/a for a,b in zip(gaps,gaps[1:])]
seq = [(g/gaps[0]/rho**n)**2 for n,g in enumerate(gaps)]
rows = [seq]
while len(rows[-1]) > 1:
    row = rows[-1]
    rows.append([a-b for a,b in zip(row,row[1:])])
out = {'ratios':list(map(str,ratios)),
       'all_ratios_increasing':all(a<b for a,b in zip(ratios,ratios[1:])),
       'hausdorff_entries':sum(map(len,rows)),
       'hausdorff_violations':sum(x<0 for row in rows for x in row),
       'first_unshifted_transition':[]}
for size in (17,18,19):
    mat = mp.matrix([[seq[i+j] for j in range(size)] for i in range(size)])
    b,v = mat[1:,1:],mat[1:,0]
    out['first_unshifted_transition'].append({
        'size':size, 'smallest_eigenvalue':str(mp.eigsy(mat,eigvals_only=True)[0]),
        'zeroth_moment_schur_complement':str(1-(v.T*mp.lu_solve(b,v))[0])})
json.dump(out,open('diagnostics-results.json','w'),indent=2)
print('Increasing ratios:',out['all_ratios_increasing'])
print('Hausdorff entries / violations:',out['hausdorff_entries'],out['hausdorff_violations'])
