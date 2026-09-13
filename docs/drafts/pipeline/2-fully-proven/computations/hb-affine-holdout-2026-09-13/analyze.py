"""Descriptive finite-sample analysis; no stochastic sampling model assumed."""
import csv
import json
from decimal import Decimal, localcontext
from pathlib import Path
from statistics import mean,median

root=Path(__file__).resolve().parent
rows=[json.loads(l) for l in (root/'raw.jsonl').read_text().splitlines()]
D={(x['n'],x['offset'],x['dps']):x for x in rows}
summary=[];contrast_rows=[]
with localcontext() as ctx:
    ctx.prec=190
    maximum={50:Decimal(0),100:Decimal(0)}
    for x in rows:
        if x['dps']==160:continue
        ref=D[x['n'],x['offset'],160]
        for field in ['stripped_log','arithmetic_response','response','log_A']:
            for a,b in zip(x[field],ref[field]):
                a,b=Decimal(a),Decimal(b)
                maximum[x['dps']]=max(maximum[x['dps']],abs(a-b)/max(1,abs(b)))
    for lo,hi in [(1,64),(65,128),(257,320)]:
        for dps in [50,100,160]:
            vals=[]
            for n in range(lo,hi+1):
                v=[Decimal(D[n,o,dps]['stripped_log'][0]) for o in ['0','-.25','.25']]
                contrast=v[0]-(v[1]+v[2])/2
                vals.append(contrast)
                contrast_rows.append([lo,hi,n,dps,str(contrast)])
            summary.append(dict(lo=lo,hi=hi,dps=dps,mean=str(mean(vals)),median=str(median(vals)),negative=sum(x<0 for x in vals)))
ind=[json.loads(l) for l in (root/'independent.jsonl').read_text().splitlines()]
indmax={f:max(Decimal(x[f]) for x in ind) for f in ['relative_error','derivative_relative_error','refined_difference','refined_derivative_difference']}
result=dict(cohorts=summary,precision_max_relative={str(k):str(v) for k,v in maximum.items()},
            independent_max={k:str(v) for k,v in indmax.items()},
            worker_seconds=sum(x['seconds'] for x in rows)+sum(x['seconds'] for x in ind),
            verdict='Frozen candidate falsified: holdout mean and median positive.')
(root/'analysis.json').write_text(json.dumps(result,indent=2)+'\n')
with open(root/'contrasts.csv','w') as out:
    writer=csv.writer(out);writer.writerow(['cohort_start','cohort_end','zero_index','dps','contrast']);writer.writerows(contrast_rows)
print(json.dumps(result,indent=2))
