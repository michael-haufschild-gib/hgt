import json
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
B=Path('docs/drafts/pipeline/2-fully-proven/computations')
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'axes.spines.top':False,'axes.spines.right':False})
fig,axes=plt.subplots(1,2,figsize=(11,5.4),constrained_layout=True)
P=B/'photonic-lattice-cusp-readers-2026-09-13';rows=json.loads((P/'summary.json').read_text())['rows']
colors=['#2962aa','#c64b30','#40895a','#8759a4']
for d,col in zip([1,2,3,4],colors):
 rr=sorted([r for r in rows if r['job']['dim']==d and float(r['job']['y'])*float(r['job']['delta'])>.7],key=lambda r:float(r['job']['y']))
 for ch,style in [('density','-'),('projector','--')]:axes[0].plot([float(r['job']['y']) for r in rr],[float(r[ch]['ratio']) for r in rr],style,marker='o',color=col,label=f'd={d}, '+('mixture' if ch=='density' else 'support'))
axes[0].axhline(1,color='#333',ls=':',lw=1);axes[0].set(xscale='log',yscale='log',xlabel='Cusp height y (δy = 0.8)',ylabel='Shape tensor ratio Qxx / Qyy',title='Changing the reader does not restore ratio 1')
axes[0].legend(ncol=2,fontsize=8,loc='upper center',bbox_to_anchor=(.5,-.18))
P2=B/'photonic-lattice-phase-fibres-2026-09-13';rows2=json.loads((P2/'summary.json').read_text())['rows']
for d,col in zip([1,3],[colors[0],colors[2]]):
 for a,b,ls,lab in [('0','0','--','zero phases'),('.5','.5','-','invariant phases')]:
  rr=sorted([r for r in rows2 if r['job']['dim']==d and r['job']['a']==a and r['job']['b']==b and r['job']['c']=='.8'],key=lambda r:float(r['job']['y']))
  axes[1].plot([float(r['job']['y']) for r in rr],[float(r['density']['ratio']) for r in rr],ls,marker='o',color=col,label=f'd={d}, {lab}')
axes[1].axhline(1,color='#333',ls=':',lw=1);axes[1].set(xscale='log',yscale='log',xlabel='Cusp height y (δy = 0.8)',ylabel='Mixture tensor ratio Qxx / Qyy',title='Stabilizer phases change the physical geometry')
axes[1].legend(ncol=2,fontsize=8,loc='upper center',bbox_to_anchor=(.5,-.18))
fig.suptitle('Finite-energy optical lattices: geometry tests, not scattering measurements',fontsize=12)
for out in [P,P2]:
 fig.savefig(out/'geometry-readers.png',dpi=180);fig.savefig(out/'geometry-readers.pdf')
print(P/'geometry-readers.png')
