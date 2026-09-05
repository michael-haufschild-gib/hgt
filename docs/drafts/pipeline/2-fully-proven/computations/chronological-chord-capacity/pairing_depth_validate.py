"""Validate numerical leads with the candidate itself included in monotone starts.

A purported signed witness may become monotone after optimization. Its absolute
probe must be a monotone-oracle starting point, otherwise a missed local maximum
can create a false ratio above one. No output constitutes a proof certificate.
"""
import os
for name in ("OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "OMP_NUM_THREADS", "NUMEXPR_NUM_THREADS"):
    os.environ[name] = "1"
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
import json
import numpy as np
from pairing_depth_probe import family_values, maximize


def validate(row):
    d,k,seed = row['degree'],row['depth'],row['seed']
    n=2*d-1
    inc=np.array([[[int(a<=i<b) for i in range(n)] for a,b in D] for D in row['basis']],dtype=float)
    rng=np.random.default_rng(700000*d+17000*k+seed)
    updated=[]
    for trial in row['trials']:
        c=np.array(trial['coefficients'])
        g=np.array(trial['signed_probe'])
        probes=rng.dirichlet(np.full(n,.2),size=30000)
        values=np.abs(family_values(inc,probes)@c)
        starts=np.vstack((np.abs(g),np.array(trial['monotone_probe']),probes[np.argsort(values)[-40:]]))
        M,w=maximize(inc,c,np.ones(n),0,starts)
        sealed=trial['optimized_sealed_value']
        negative_mass=min(float(np.maximum(g,0).sum()),float(np.maximum(-g,0).sum()))
        updated.append({**trial,'validated_monotone_max':M,'validated_monotone_probe':w.tolist(),
                        'validated_ratio_estimate':sealed/M,'negative_mass':negative_mass})
    return {**row,'trials':updated,'best':max(updated,key=lambda t:t['validated_ratio_estimate'])}


if __name__=='__main__':
    source=json.loads(Path('pairing-depth-results.json').read_text())
    with ProcessPoolExecutor(max_workers=24) as pool:
        rows=list(pool.map(validate,source['results']))
    result={'metadata':{**source['metadata'],'validation':'Include absolute signed probe and 30000 fresh monotone probes per trial'},'results':rows}
    Path('pairing-depth-validation.json').write_text(json.dumps(result,indent=2)+'\n')
    for d,k in ((3,1),(4,1),(4,2)):
        group=[r for r in rows if r['degree']==d and r['depth']==k]
        print(json.dumps({'degree':d,'depth':k,'max_validated_ratio':max(r['best']['validated_ratio_estimate'] for r in group),
                          'lp_failures':sum(r['lp_failures'] for r in group)}),flush=True)
