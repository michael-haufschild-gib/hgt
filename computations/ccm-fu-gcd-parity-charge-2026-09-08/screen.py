"""Frozen gcd parity-charge diagnostic. Execute only on supplied RunPod."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
os.environ['OMP_NUM_THREADS']='1'
os.environ['MKL_NUM_THREADS']='1'
import hashlib
import json
import multiprocessing as multiprocessing
from pathlib import Path
import signal
import time
import numpy as np

LD=np.longdouble
CUTOFFS=list(range(101,257))+[2**j for j in range(9,18)]
MU=None


def cutoff(M):
    path=Path('cutoff_{}.npz'.format(M))
    with np.load(path) as data:
        C,G=data['C'],data['G']
    D=np.sum(C*C,dtype=LD)
    S=np.sum(C,dtype=LD)
    L=np.sum(G,dtype=LD)
    J=np.sum(MU[:M]*np.abs(G),dtype=LD)
    assert np.max(np.abs(G[MU[:M]==0])) <= LD('1e-12')*D
    cls_plus=np.sum(G[MU[:M]*G>0],dtype=LD)
    cls_minus=np.sum(G[MU[:M]*G<0],dtype=LD)
    errors=[abs(L-(S*S-D)),abs(cls_plus-(L+J)/2),abs(cls_minus-(L-J)/2)]
    assert max(errors)<=LD('1e-12')*D
    Uc=max(cls_plus,LD(0))+max(cls_minus,LD(0))
    ratio=(S*S+abs(J))/D
    existing=Path('flow_{}.json'.format(M))
    flow=None
    gap=None
    if existing.exists():
        flow=LD(str(json.loads(existing.read_text())['U_over_D']))
        gap=flow-Uc/D
        assert gap>=-LD('1e-10')
    return dict(M=M,diagonal=str(D),head=str(S),signed_cross=str(L),parity_charge=str(J),
                class_plus=str(cls_plus),class_minus=str(cls_minus),
                colour_deficit=str(Uc),colour_over_D=float(Uc/D),
                necessary_ratio=float(ratio),failure=bool(ratio-3>LD('1e-9')),
                existing_prime_flow_over_D=None if flow is None else float(flow),
                local_gap_over_D=None if gap is None else float(gap),
                max_formula_error=str(max(errors)),
                input_sha256=hashlib.sha256(path.read_bytes()).hexdigest())


def deadline(*_):
    raise TimeoutError('Frozen60seconddeadline')


def worker_init():
    signal.signal(signal.SIGALRM,signal.SIG_DFL)
    signal.signal(signal.SIGTERM,signal.SIG_DFL)


if __name__=='__main__':
    signal.signal(signal.SIGALRM,deadline)
    signal.signal(signal.SIGTERM,deadline)
    signal.alarm(60)
    start=time.monotonic()
    with np.load('source.npz') as data:
        MU=data['mu']
    with multiprocessing.get_context('fork').Pool(4,initializer=worker_init) as pool:
        rows=pool.map(cutoff,CUTOFFS,chunksize=1)
    failures=[r for r in rows if r['failure']]
    selected=failures[0] if failures and failures[0]['M']<=1024 else max(
        (r for r in rows if r['M']<=256),key=lambda r:r['necessary_ratio'])
    report=dict(workers=4,seconds=time.monotonic()-start,cutoffs=CUTOFFS,rows=rows,
                failures=[r['M'] for r in failures],selected_audit_M=selected['M'],
                script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    Path('summary.json').write_text(json.dumps(report,indent=2))
    signal.alarm(0)
    print(json.dumps(dict(seconds=report['seconds'],failures=report['failures'],
                         selected_audit_M=selected['M'],
                         maximum=max(rows,key=lambda r:r['necessary_ratio']),
                         colour_positive_count=sum(r['colour_over_D']>1e-10 for r in rows),
                         largest_local_gap=max((r for r in rows if r['local_gap_over_D'] is not None),
                                               key=lambda r:r['local_gap_over_D']),
                         dyadic=[r for r in rows if r['M']>=512])),flush=True)
