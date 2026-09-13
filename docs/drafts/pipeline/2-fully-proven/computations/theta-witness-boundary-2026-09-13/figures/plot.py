import json,os,time
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

data=json.loads(Path('plot-data.json').read_text())
fig,axes=plt.subplots(2,2,figsize=(10.2,6.8),constrained_layout=True)
for col,(mode,item) in enumerate(data.items()):
    rows=[]
    for tr in item['tracks']:
        l0=float(tr['witness_lambda'])
        rows += [(float(p['ratio'])*l0,float(p['t'][0]),float(p['t'][1])) for p in tr['points']]
    for r in item['boundaries']:rows.append((float(r['lam']),float(r['t']),0.0))
    rows=np.array(sorted(set(rows)))
    lo,hi=min(rows[:,0]),max(rows[:,0])
    axes[0,col].plot(rows[:,0],rows[:,1],'.-',color='#196b92',ms=3,lw=1)
    axes[1,col].plot(rows[:,0],rows[:,2],'.-',color='#ae4a27',ms=3,lw=1)
    axes[1,col].plot(rows[:,0],-rows[:,2],'.-',color='#ae4a27',ms=3,lw=1,alpha=.55,label='conjugate by symmetry')
    for ax in axes[:,col]:
        ax.axvline(lo,c='0.6',ls='--',lw=.8);ax.axvline(hi,c='0.6',ls='--',lw=.8)
        ax.grid(alpha=.18);ax.set_xlabel('Deformation amplitude lambda')
    axes[0,col].set_ylabel('Real part of transform zero t')
    axes[1,col].set_ylabel('Imaginary part of transform zero t')
    axes[0,col].set_title('Theta: additive (+, -)' if mode=='theta' else 'Conductor 5: product (-, +)')
    axes[1,col].axhline(0,c='0.4',lw=.6)
    axes[1,col].legend(loc='upper right',fontsize=8)
fig.suptitle('Tracked deformed zero pairs leave and return to the real axis',fontsize=13)
fig.savefig('returning-zero-pairs.png',dpi=170)
fig.savefig('returning-zero-pairs.svg')
Path('plot-environment.json').write_text(json.dumps(dict(matplotlib=matplotlib.__version__,numpy=np.__version__,scope='Rendering recorded points only; lines are visual guides, not interval certificates. Lower branch shown by conjugation symmetry.'),indent=2)+'\n')
