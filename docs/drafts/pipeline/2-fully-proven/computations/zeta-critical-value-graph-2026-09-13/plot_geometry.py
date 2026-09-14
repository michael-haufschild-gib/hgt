from pathlib import Path
import json,sys
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np
b=Path('docs/drafts/pipeline/2-fully-proven/computations')
plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False})
fig,axs=plt.subplots(1,2,figsize=(11,4.6),layout='constrained')
r=json.loads((b/'zeta-monodromy-independent-challenge-2026-09-13'/'check-1-circle-160.json').read_text());path=np.array([[float(v[1]),float(v[2])] for v in r['path']]);axs[0].plot(path[:,0],path[:,1],color='#17628d');axs[0].scatter([.5,-4],[14.1347251417,0],color=['#17628d','#b44332'],zorder=3);axs[0].annotate('First nontrivial zero',(.5,14.1347),xytext=(-3.8,14.8));axs[0].annotate('Trivial zero −4',(-4,0),xytext=(-3.7,1));axs[0].axvline(.5,color='gray',alpha=.35,ls=':');axs[0].set(xlabel='Re(s)',ylabel='Im(s)',title='Lift of w = 1 − exp(2πiu)')
r=json.loads((b/'zeta-critical-graph-independent-challenge-2026-09-13'/'check-59-160-1e-7.json').read_text());cp=list(map(float,r['critical_point']))
for branch,color in zip(r['branches'],['#17628d','#b44332']):
 path=np.array([[float(v[1]),float(v[2])] for v in branch['path']]);axs[1].plot(path[:,0],path[:,1],color=color,label='To zero '+str(branch['nearest_zero'][0]));axs[1].scatter(path[-1,0],path[-1,1],color=color,zorder=3)
axs[1].scatter(cp[0],cp[1],color='#373737',marker='x',s=60,zorder=3,label="ζ′(s) = 0");axs[1].axvline(.5,color='gray',alpha=.35,ls=':');axs[1].set(xlabel='Re(s)',ylabel='Im(s)',title='Two branches reaching zeros 57 and 60');axs[1].legend(loc='best',frameon=False);fig.suptitle('Finite inverse connections of the Riemann zeta function — numerical evidence',fontsize=12)
p=b/'zeta-critical-value-graph-2026-09-13';fig.savefig(p/'inverse-connections.png',dpi=180);fig.savefig(p/'inverse-connections.pdf');plt.close(fig)
rows=json.loads((b/'zeta-one-fibre-access-2026-09-13'/'summary.json').read_text())['rows'];fig,axs=plt.subplots(1,2,figsize=(11,4.1),layout='constrained')
for n,color in [(1,'#17628d'),(6,'#b44332')]:
 r=json.loads((b/'zeta-one-fibre-access-2026-09-13'/f'access-{n:03d}-0.json').read_text());path=np.array([[48*float(v[0]),float(v[1]),float(v[2])] for v in r['path']]);axs[0].plot(path[:,0],path[:,1],label=f'Zero {n}',color=color)
axs[0].set(xlabel='R, where target is 1 − 2^(−R)',ylabel='Re(s)',title='Two ways to approach the value 1');axs[0].legend(frameon=False)
for a,y in [(-1,0),(0,1),(1,2)]:
 for cat,color in [('finite_like','#b44332'),('escape_like','#17628d'),('unresolved','#b6a142')]:
  xx=[r['n'] for r in rows if r['angle_thirds_pi']==a and r.get('category')==cat];axs[1].scatter(xx,[y]*len(xx),s=22,color=color,label=cat.replace('_',' ') if a==-1 else None)
axs[1].set(xlabel='Cached zero label',yticks=[0,1,2],yticklabels=['−π/3','0','+π/3'],ylabel='Approach angle',title='Finite endpoint classifications (R ≤ 48)');axs[1].set_ylim(-.7,2.7);axs[1].legend(frameon=False,loc='upper left',bbox_to_anchor=(0,-.18),ncol=2);p=b/'zeta-one-fibre-access-2026-09-13';fig.savefig(p/'value-one-access.png',dpi=180);fig.savefig(p/'value-one-access.pdf');plt.close(fig)
(p/'plot-environment.json').write_text(json.dumps({'python':sys.version,'matplotlib':matplotlib.__version__,'numpy':np.__version__},indent=2)+'\n')
print('Figures saved')
