"""Describe the complete finite data without extrapolating. Runpod only."""
import os
os.environ.update(OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1", MKL_NUM_THREADS="1")
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
ROOT=Path(__file__).resolve().parent
x=np.load(ROOT/'all-endpoints.npz')
m,r,d,s=(x[k] for k in ('M','ratio','diagonal','source'))
bands=[]
for j in range(1,22):
    mask=(m>=2**j)&(m<2**(j+1))
    if not mask.any():
        continue
    where=np.flatnonzero(mask); peak=where[np.argmax(r[mask])]
    bands.append(dict(lower=int(m[where[0]]),upper=int(m[where[-1]]),
                      peak_M=int(m[peak]),peak_ratio=float(r[peak]),
                      median_ratio=float(np.median(r[mask])),
                      min_diagonal=float(d[mask].min()),max_diagonal=float(d[mask].max())))
(ROOT/'bands.json').write_text(json.dumps(bands,indent=2)+'\n')
# Plot only complete bands: the final endpoint is not a new full band.
bands=[b for b in bands if b['upper']==2*b['lower']-1]
fig,ax=plt.subplots(1,2,figsize=(10,3.4))
left=[b['lower'] for b in bands]
ax[0].plot(left,[b['peak_ratio'] for b in bands],'o-',label='Maximum over every integer in band')
ax[0].plot(left,[b['median_ratio'] for b in bands],'.--',label='Median')
ax[0].axhline(1,color='#ad302d',lw=1,label='SD1 failure boundary')
ax[0].set(xscale='log',xlabel='Band lower endpoint M',ylabel='Source square / diagonal',ylim=(-.02,1.08))
ax[0].legend(fontsize=7,loc='upper right')
ax[1].fill_between(left,[b['min_diagonal'] for b in bands],[b['max_diagonal'] for b in bands],alpha=.3)
ax[1].plot(left,[b['max_diagonal'] for b in bands],'.-',color='#346b94')
ax[1].set(xscale='log',xlabel='Band lower endpoint M',ylabel='Diagonal / M² (full band range)')
for a in ax:
    a.grid(alpha=.2); a.spines[['top','right']].set_visible(False)
fig.suptitle('Complete finite source: all integers through 2,097,152; no all-scale proof',fontsize=10)
fig.tight_layout()
fig.savefig(ROOT/'summary.png',dpi=180)
print(json.dumps([bands[j] for j in (0,5,10,15,19)],indent=2))
