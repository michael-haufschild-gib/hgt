"""Aggregate saved results only; does not rerun special functions."""
from pathlib import Path
from decimal import Decimal, localcontext
import json

root=Path(__file__).resolve().parent
rows=[json.loads(l) for l in (root/'results.jsonl').read_text().splitlines()]
samples={(r['n'],r['q'],r['dps']):r for r in rows if r['kind']=='sample' and 'error' not in r}
with localcontext() as ctx:
    ctx.prec=200
    errors={}
    for dps in [50,100]:
        differences=[]
        for (n,q,d),r in samples.items():
            if d!=160:continue
            low=samples[n,q,dps]
            differences.extend(abs(Decimal(r['contrasts'][k])-Decimal(low['contrasts'][k])) for k in ['R','N'])
        errors[str(dps)]=str(max(differences))
    minimum=min((Decimal(z[0])**2+Decimal(z[1])**2).sqrt() for r in samples.values() for item in r['rows'] for z in item['values'].values())
    out=dict(stage_gates=[r for r in rows if r['kind']=='stage_gate'],
             counts={kind:sum(r['kind']==kind for r in rows) for kind in sorted({r['kind'] for r in rows})},
             max_contrast_error_vs160=errors,min_sampled_carrier_magnitude=str(minimum),
             max_independent_scaled_error=str(max(Decimal(r['scaled_error']) for r in rows if r['kind']=='independent')),
             max_independent_refinement=str(max(Decimal(r['refinement']) for r in rows if r['kind']=='independent')),
             worker_seconds=sum(r['seconds'] for r in rows if r['kind'] in ['sample','independent']))
    (root/'analysis.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='stage_gates'},indent=2))
