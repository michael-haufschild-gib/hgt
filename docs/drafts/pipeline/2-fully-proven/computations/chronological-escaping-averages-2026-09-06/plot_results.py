"""Render saved frozen-prefix diagnostics on Runpod only."""
import json,pathlib
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
ROOT=pathlib.Path(__file__).resolve().parent
rows=json.loads((ROOT/'results.json').read_text())['results']
release=json.loads((ROOT/'release_results.json').read_text())['results']
plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False})
fig,ax=plt.subplots(1,2,figsize=(12,4.5),layout='constrained')
labels=['All raw cutoffs','Freeze N/64','Freeze N/16','Freeze N/4','Freeze N/2']
colors=['#267fc0','#2da78e','#9e78c7','#cf973d','#c05e60']
for i,label,color in zip(range(5),labels,colors):
    ax[0].loglog([r[i]['N'] for r in rows],[r[i]['norm'] for r in rows],
                 'o-',label=label,color=color)
ax[0].set(xlabel='Maximum cutoff N',ylabel='Measured full L² error',
          title='Positive averages: cost of freezing more history')
ax[0].legend(fontsize=9)
ax[0].grid(alpha=.15)
vals=[rows[-1][-1]['norm']]+[r['norm'] for r in release]
ax[1].bar(range(4),vals,color=['#c05e60','#2da78e','#9e78c7','#267fc0'])
ax[1].set(yscale='log',ylabel='Measured full L² error',
          title='N=8192: first 4096 coefficients fixed to Möbius',
          xticks=range(4),xticklabels=['Positive\naverages','Keep signs;\nallow oscillations',
                                     'Squarefree\nunit box','Full\nunit box'])
for j,x in enumerate(vals):
    ax[1].annotate('%.3g'%x,(j,x),xytext=(0,5),textcoords='offset points',ha='center',fontsize=9)
ax[1].set_ylim(min(vals)/3,max(vals)*4)
fig.suptitle('Exploratory numerical evidence; no asymptotic convergence certificate',fontsize=12)
fig.savefig(ROOT/'escaping-averages.png',dpi=180)
fig.savefig(ROOT/'escaping-averages.pdf')
