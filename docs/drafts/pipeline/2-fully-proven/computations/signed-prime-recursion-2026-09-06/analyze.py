"""Read saved remote data, attribute the reversal, and produce a figure."""
import os
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'):
    os.environ[key]='1'
import json
from pathlib import Path
import math
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

base=Path('.')
first=json.loads((base/'results.json').read_text())
discovery=json.loads((base/'reverse-results.json').read_text())
holdout=json.loads((base/'holdout-results.json').read_text())
attribution=json.loads((base/'attribution-results.json').read_text())
dilation=json.loads((base/'dilation-results.json').read_text())
summary={'identity_max_abs':max(abs(r['identity_residual']) for c in first['results'] for r in c['rows']),
         'reverse_identity_max_abs':max(abs(r['residual']) for d in (discovery,holdout,attribution) for r in d['rows']),
         'holdout_pass_count':sum(r['error']>r['control_quantiles'][3] for r in holdout['rows']),
         'holdout_count':len(holdout['rows']), 'attribution':[]}
centered={r['n']:sum(c['error']-c['charge_mean_error'] for c in r['cohorts'])/r['root']
          for r in dilation['rows']}
summary['dilation_comparisons']=[dict(n=n,p=p,base=centered[n],dilated=centered[p*n],
                                     reverses=centered[n]*centered[p*n]<0)
    for n in (2**19,2**20,2**21) for p in (2,3,5,7)]
print('H2 reversals',sum(c['reverses'] for c in summary['dilation_comparisons']),'/ 12',flush=True)
for c in summary['dilation_comparisons']:
    if not c['reverses']:
        print('H2 failure',c,flush=True)
for r in attribution['rows']:
    center=[dict(lo=c['lo'],value=(c['error']-c['charge_mean_error'])/r['root']) for c in r['cohorts']]
    summary['attribution'].append(dict(n=r['n'],centered_sum=sum(c['value'] for c in center),
        centered_small=sum(c['value'] for c in center if c['lo']<64),
        centered_large=sum(c['value'] for c in center if c['lo']>=64),
        largest=sorted(center,key=lambda c:abs(c['value']),reverse=True)[:6]))
    print(summary['attribution'][-1],flush=True)

fig,(ax,heat)=plt.subplots(2,1,figsize=(10,8),gridspec_kw={'height_ratios':[1.1,1]},constrained_layout=True)
for d,marker,color,label in [(discovery,'o','#165a88','Discovery'),(holdout,'D','#b94716','Withheld cutoffs')]:
    rows=sorted(d['rows'],key=lambda r:r['n'])
    xs=np.array([r['n'] for r in rows])
    ys=np.array([r['error']/r['root'] for r in rows])
    med=np.array([r['control_quantiles'][2]/r['root'] for r in rows])
    low=np.array([r['control_quantiles'][1]/r['root'] for r in rows])
    high=np.array([r['control_quantiles'][3]/r['root'] for r in rows])
    ax.errorbar(xs,med,yerr=[med-low,high-med],fmt='_',color='#aaa7a0',capsize=4,lw=2)
    ax.scatter(xs,ys,marker=marker,color=color,s=42,label=label,zorder=5)
ax.scatter([2**22],[next(r['error']/r['root'] for r in attribution['rows'] if r['n']==2**22)],
           color='#333333',marker='x',s=70,label='Reversal attribution')
ax.axhline(0,color='#777',lw=.6)
ax.set_xscale('log',base=2)
ax.set_xlabel('Integer cutoff N')
ax.set_ylabel('Signed counting-error pairing / sqrt(N)')
ax.set_title('Arithmetic alignment changes direction across the tested cutoffs',loc='left',weight='bold',fontsize=12)
ax.legend(frameon=False,ncol=3,fontsize=9)
ax.text(.01,.88,'Gray bars: 5th–95th percentile of charge-preserving controls',transform=ax.transAxes,
        va='top',fontsize=9,color='#555')

data=np.full((4,24),np.nan)
for i,r in enumerate(attribution['rows']):
    for c in r['cohorts']:
        k=int(math.log2(c['lo']))
        if k<24:
            data[i,k]=(c['error']-c['charge_mean_error'])/r['root']
bound=float(np.nanmax(abs(data)))
cmap=plt.get_cmap('RdBu_r').copy()
cmap.set_bad('#eeeeee')
im=heat.imshow(data,aspect='auto',cmap=cmap,vmin=-bound,vmax=bound)
heat.set_yticks(range(4),[f'2^{int(math.log2(r["n"]))}' for r in attribution['rows']])
heat.set_xticks(range(0,24,2),[str(k) for k in range(0,24,2)])
heat.set_xlabel('Cofactor block [2^k, 2^(k+1)): exponent k')
heat.set_ylabel('Cutoff N')
heat.set_title('Charge-centered contributions retain both signs across cofactor scales',loc='left',fontsize=11)
fig.colorbar(im,ax=heat,label='Signed contribution / sqrt(N)',shrink=.85)
fig.savefig('signed-reversal.png',dpi=180)
fig.savefig('signed-reversal.svg')
Path('analysis.json').write_text(json.dumps(summary,indent=2))
print('identity residuals',summary['identity_max_abs'],summary['reverse_identity_max_abs'])
