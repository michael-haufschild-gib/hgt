import json
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
B=Path('docs/drafts/pipeline/2-fully-proven/computations');P=B/'photonic-native-loop-response-2026-09-13';R=B/'photonic-native-loop-step-refinement-2026-09-13'
base=json.loads((P/'summary.json').read_text())['rows'];ref=json.loads((R/'summary.json').read_text())['rows']
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'axes.spines.top':False,'axes.spines.right':False})
fig,ax=plt.subplots(1,2,figsize=(11,5.4),constrained_layout=True)
for delta,col in [('.2','#3268ac'),('.05','#cf572f')]:
 rows=[r for r in base if r['job']['dim']==2 and r['job']['m']==3 and r['job']['delta']==delta]+[r for r in ref if r['job']['dim']==2 and r['job']['m']==3 and r['job']['delta']==delta];rows.sort(key=lambda r:r['job']['steps']);ns=[r['job']['steps'] for r in rows]
 for ch,ls,lab in [('geometric','--','monitor only'),('driven_monitored','-','drive + monitor')]:
  label=f'δ={delta}, {lab}';ax[0].plot(ns,[float(r[ch]['mean_survival']) for r in rows],ls,marker='o',color=col,label=label)
  ax[1].plot(ns,[float(r[ch]['projective_distance_to_ideal']) for r in rows],ls,marker='o',color=col,label=label)
ax[0].set(xscale='log',yscale='log',xlabel='Monitoring steps per physical period',ylabel='Mean survival probability',title='The actual drive prevents severe geometric loss')
ax[1].set(xscale='log',yscale='log',xlabel='Monitoring steps per physical period',ylabel='Projective distance from ideal lattice return',title='High survival does not identify the logical response')
for a in ax:a.legend(loc='upper center',bbox_to_anchor=(.5,-.18),ncol=2,fontsize=8)
fig.suptitle('One native two-layer PTC cycle: trace 3, code dimension 2',fontsize=12)
for p in [P,R]:fig.savefig(p/'physical-loop-readers.png',dpi=180);fig.savefig(p/'physical-loop-readers.pdf')
print(P/'physical-loop-readers.png')
