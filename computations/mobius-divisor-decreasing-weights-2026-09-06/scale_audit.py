"""Independent GH1 falsification audit and retained finite-data plot; Runpod only."""
import os
os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1')
from pathlib import Path
import json,time
import mpmath as mp
from geometric_cross import audit
ROOT=Path(__file__).resolve().parent
if __name__=='__main__':
    start=time.monotonic()
    rows=[audit(1802,'0.000001',dps) for dps in (60,100)]
    out=dict(audits=rows,seconds=time.monotonic()-start)
    (ROOT/'scale_audit.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    import numpy as np
    data=json.loads((ROOT/'geometric_scale.json').read_text())
    fig,axes=plt.subplots(1,2,figsize=(11,4),layout='constrained')
    for r in data['rows']:
        if r['M'] in (1024,32768,1865411):
            axes[0].semilogx([v['u'] for v in r['values']], [v['relative'] for v in r['values']],label=f"M={r['M']:,}")
    axes[0].axhline(0,color='black',lw=.7);axes[0].legend()
    axes[0].set(xlabel='Scale-normalized geometric rate u',ylabel='Signed pairing / absolute term mass',title='GH1: small-scale pass does not persist')
    data=json.loads((ROOT/'followup.json').read_text())
    rows=[r for r in data['audits'] if r['dps']==100]
    labels=['Flat','Strictly decreasing','Square-root']
    values=[float(r['ratio']) for r in rows]
    axes[1].bar(labels,values,color=['#b54a42','#b54a42','#377a91'])
    axes[1].axhline(1,color='black',lw=.7,ls='--')
    axes[1].set(ylabel='Source square / diagonal',title='Complete source at M=7')
    fig.savefig(ROOT/'summary.png',dpi=180)
