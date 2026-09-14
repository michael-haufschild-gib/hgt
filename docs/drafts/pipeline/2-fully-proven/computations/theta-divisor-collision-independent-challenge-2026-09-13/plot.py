import json
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
B=Path(__file__).resolve().parent.parent;P=Path(__file__).resolve().parent
rows=json.loads((P/'summary.json').read_text())['rows'];rows={r['row']['id']:r for r in rows if r['dps']==160}
rootrows=json.loads((B/'theta-divisor-single-independent-challenge-2026-09-13/summary.json').read_text())['rows']
plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False})
fig,axs=plt.subplots(1,3,figsize=(12.4,4.1),layout='constrained')
ax=axs[0]
for r in rootrows:
 if r['dps']==160 and r['row']['id'] in [0,1]:
  x,y=map(float,r['root']);ax.scatter([x,x],[y,-y],c='#9a3065',s=48)
ax.axhline(0,color='.4',lw=.8);ax.set(xlabel='Re w',ylabel='Im w',title='One source pair removed\nNonreal Fourier zeros',ylim=(-3,3))
for ax,k,title in [(axs[1],0,'Extra quartet: pair becomes real'),(axs[2],2,'Extra quartet: pair becomes nonreal')]:
 r=rows[k];wc=float(r['w'][0]);lc=float(r['lambda_value']);ax.axhline(0,color='.4',lw=.8)
 for lower,color,marker in [(True,'#9a3065','o'),(False,'#167b8c','s')]:
  q=[b for b in r['branches'] if (float(b['lambda_value'])<lc)==lower];x=[float(b['root'][0])-wc for b in q];y=[float(b['root'][1]) for b in q];ax.scatter(x,y,color=color,marker=marker,s=48,label='below collision' if lower else 'above collision')
 ax.scatter([0],[0],color='.2',marker='x',s=45);ax.set(xlabel=r'Re $(w-w_c)$',ylabel='Im w',title=title+'\n'+rf'$w_c={wc:.4f}$, $\lambda_c={lc:.4f}$');ax.legend(frameon=False,fontsize=8)
fig.suptitle('Theta-source divisor surgery — validated numerical snapshots',fontsize=13)
fig.savefig(P/'source-divisor-response.png',dpi=180);fig.savefig(P/'source-divisor-response.pdf')
(P/'FIGURE.md').write_text('Each point is a100/160-digit checked Fourier zero of a declared positive-source deformation. Left: divide literal theta source by1+x^2/a^2, a≈.638830053600594. Middle/right: mass-normalized convex interpolation between that quotient and a further actual source-quartet deletion. Snapshots on both sides of selected collisions; connecting trajectories are not plotted. These are not zeros of the undeformed zeta function. No HB physical interpretation is asserted.\n')
