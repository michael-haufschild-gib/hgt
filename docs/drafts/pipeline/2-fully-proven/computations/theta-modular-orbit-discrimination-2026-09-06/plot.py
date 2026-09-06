"""Render downloaded experiment records on Runpod; no additional numerical claims."""
from pathlib import Path
import json
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np
ROOT=Path(__file__).resolve().parent
data=json.loads((ROOT/'results.json').read_text())
fig,axs=plt.subplots(1,3,figsize=(14,4.2),constrained_layout=True)
for row in data['rows']:
    if row['label'] not in ('theta','X=10','X=15','X=18','X=20','X=25'):continue
    axs[0].plot(row['points'],row['relative'],label=row['label'],lw=2 if row['label']=='theta' else 1)
axs[0].axhline(0,color='black',lw=.6)
axs[0].axvspan(0,137/2000,alpha=.08,color='green')
axs[0].set(title='Signed D1 / absolute determinant terms',xlabel='x',ylabel='signed ratio')
axs[0].legend(fontsize=7,ncol=2)
row=next(r for r in data['rows'] if r['label']=='theta')
x=np.asarray(row['points']);y=np.asarray(row['states']);cut=x<=137/2000
for k,name,scale in [(0,'−S',-1),(2,'W',1)]:axs[1].plot(x[cut],scale*y[cut,k],label=name)
axs[1].plot(x[cut],13*x[cut],'--',lw=1,label='13x bound')
axs[1].plot(x[cut],14*x[cut],'--',lw=1,label='14x bound')
axs[1].set(title='Actual orbit in compact certificate region',xlabel='x')
axs[1].legend(fontsize=8)
for label in ('theta_delta=-0.0001','theta','theta_delta=0.0001'):
    row=next(r for r in data['rows'] if r['label']==label)
    y=np.asarray(row['long_states']);axs[2].plot(row['long_points'],y[:,0],label=label)
axs[2].set_yscale('symlog',linthresh=3)
axs[2].axhline(-3,color='black',lw=.6,ls=':')
axs[2].set(title='Seam perturbations: finite-time ODE probe',xlabel='x',ylabel='S')
axs[2].legend(fontsize=7)
fig.suptitle('Theta source experiments — numerical guidance; proof certificates checked separately',fontsize=12)
fig.savefig(ROOT/'summary.png',dpi=170)
