from pathlib import Path
import json
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np
P=Path(__file__).resolve().parent
D=json.loads((P/'summary.json').read_text())['rows'];D=[r for r in D if r['dps']==160 and r['status']=='ok']
fig,ax=plt.subplots(1,2,figsize=(11,4.6),layout='constrained')
colors={'.5':'#126f96','1':'#ce6e29'}
for r in D:
 j=r['row'];p=j['job']['p'];a=j['job']['alpha'];x,y=map(float,r['root'])
 if j['role']=='lowest-found-full':
  ax[0].scatter(x,y,color=colors[a],s=48,marker='o' if a=='.5' else '^')
  if a=='.5':ax[0].annotate(p,(x,y),xytext=(8,7),textcoords='offset points',fontsize=8)
 if p=='2' and a=='.5':
  ax[1].scatter(x,y,color='#126f96',s=65,marker='x' if j['kind']=='tail' else 'o');ax[1].annotate(j['role'].replace('lowest-found-',''),(x,y),xytext=(0,10 if j['kind']=='tail' else -20),ha='center',textcoords='offset points',fontsize=8)
for a in ax:
 a.axhline(np.pi/4,color='#87919a',ls='--',lw=1);a.set_ylim(0,.82);a.set_xlabel('Re(source coordinate z)');a.set_ylabel('Im(source coordinate z)');a.grid(alpha=.15)
ax[0].scatter([],[],color=colors['.5'],label='decay α = 1/2');ax[0].scatter([],[],color=colors['1'],marker='^',label='decay α = 1');ax[0].legend(frameon=False,loc='upper left');ax[0].set_title('Validated interior zeros: 14 representations\nLabels show shift base p (primes and controls)',fontsize=11)
ax[1].set_xlim(-.1,12.5);ax[1].set_title('p = 2, α = 1/2: zeros persist far into the tail\nCross: tail-limit node; circles: actual source nodes',fontsize=11)
fig.suptitle('A zero-preserving spectral multiplier does not remove source zeros',fontsize=13)
fig.savefig(P/'source-representation-obstruction.png',dpi=180);fig.savefig(P/'source-representation-obstruction.pdf')
(P/'plot-environment.json').write_text(json.dumps(dict(matplotlib=matplotlib.__version__,numpy=np.__version__),indent=2)+'\n')
