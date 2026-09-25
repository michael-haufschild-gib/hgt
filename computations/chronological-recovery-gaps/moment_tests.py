"""Finite necessary moment tests; run on Runpod, never proof input."""
import json
import mpmath as mp
mp.mp.dps=65
with open('refined-results.json') as f: data=json.load(f)
gaps=[mp.mpf(v['delta']) for v in data['results']]
rho=mp.mpf(data['rho'])
moments=[(g/gaps[0])**2/rho**(2*i) for i,g in enumerate(gaps)]
rows=[moments]
while len(rows[-1])>1:
    p=rows[-1]
    rows.append([p[j]-p[j+1] for j in range(len(p)-1)])
out={'scaled_moments':[str(x) for x in moments],
     'hausdorff_differences':[[str(x) for x in row] for row in rows],
     'all_tested_positive':all(x>0 for row in rows for x in row),
     'degrees':list(range(len(gaps)))}
with open('moment-tests.json','w') as f:json.dump(out,f,indent=2)
print(json.dumps(out,indent=2))
