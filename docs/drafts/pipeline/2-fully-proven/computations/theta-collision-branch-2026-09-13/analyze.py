import json
from pathlib import Path
from decimal import Decimal, localcontext
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

root=Path(__file__).resolve().parent
def read(name):return [json.loads(s) for s in (root/name).read_text().splitlines()]
rows=read('tracks.jsonl');back=read('return-tracks.jsonl');checks=read('source-validation.jsonl')
stats=dict(completed_tracks=sum(r['reached_endpoint'] for r in rows),tracks=len(rows),
           completed_returns=sum(r['reached_endpoint'] for r in back),
           largest_return_t_error=max(float(r['return_errors']['t']) for r in back if 'return_errors' in r),
           largest_source_scaled_error=max(float(x) for r in checks for x in r['relative_to_scale_errors']),
           worker_seconds=sum(r['seconds'] for name in ['tracks.jsonl','return-tracks.jsonl','validation.jsonl','source-validation.jsonl'] for r in read(name)))
with localcontext() as ctx:
    ctx.prec=210
    endpoints={tuple(r['seed']['direction']):{} for r in rows}
    for r in read('validation.jsonl'):
        if r['dps']==160:endpoints[tuple(r['direction'])][r['interaction']]=Decimal(r['lam'])
    stats['continued_relative_lambda_change']={str(k):str(v[1]/v[0]-1) for k,v in endpoints.items() if 0 in v and 1 in v}
(root/'analysis.json').write_text(json.dumps(stats,indent=2)+'\n')

plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False})
fig,ax=plt.subplots(1,3,figsize=(12,3.6),layout='constrained')
colors={0:'#176b8b',1:'#bd5036'}
for r in rows:
    seed=r['seed'];points=r['points'];k=[float(p['kappa']) for p in points]
    if seed['direction']==[1,-1]:
        label='from additive collision' if seed['interaction']==0 else 'from product collision'
        for axis,key in zip(ax[:2],['t','lam']):
            y=[float(p[key]) for p in points];axis.plot(k,y,'o-',ms=3,lw=1.2,color=colors[seed['interaction']],label=label)
            if not r['reached_endpoint']:axis.plot(k[-1],y[-1],'x',color='black',ms=8)
    elif seed['interaction']==0:
        initial=float(points[0]['lam']);y=[100*(float(p['lam'])/initial-1) for p in points]
        ax[2].plot(k,y,'o-',ms=3,lw=1.2,label=str(tuple(seed['direction'])))
ax[0].set_ylabel('Collision location t');ax[1].set_ylabel('Deformation parameter lambda')
ax[2].set_ylabel('Threshold change from additive (%)')
for a in ax:a.set_xlabel('Interaction strength kappa');a.grid(alpha=.2)
ax[0].set_title('(+,-): tracked locations');ax[1].set_title('(+,-): unresolved continuation stops');ax[2].set_title('Gap-24 control branches')
ax[0].legend(fontsize=8);ax[2].legend(title='Direction',fontsize=8)
fig.savefig(root/'branches.png',dpi=180);fig.savefig(root/'branches.svg')
print(json.dumps(stats,indent=2))
