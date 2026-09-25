"""Scale-invariance test of the numerical optimizer; no mathematical proof input."""
import os
os.environ['OPENBLAS_NUM_THREADS']='4'
os.environ['OMP_NUM_THREADS']='4'
import pathlib,sys,json,time,concurrent.futures
import numpy as np
from scipy.optimize import lsq_linear
import experiment as ex

def run_case(task):
    n,C,scale=task
    A,e,t,_=ex.design(n,20)
    V,v,tv,_=ex.design(n,36,True)
    fit=lsq_linear(scale*A,-scale*e,bounds=(-C,C),tol=1e-14,max_iter=300,
                   method='trf',lsq_solver='exact')
    a=np.clip(fit.x,-C,C)
    r=A@a+e
    vr=V@a+v
    grad=A.T@r
    energy=float(vr@vr)
    gap=2*float(a@grad)+2*C*float(np.abs(grad).sum())
    return {'N':n,'C':C,'scale':scale,'validated_norm':float(np.sqrt(energy)),
            'iterations':int(fit.nit),'status':int(fit.status),
            'quadrature_primal_dual_gap':gap,'mesh_energy_difference':float(abs(energy-r@r))}

if __name__=='__main__':
    tasks=[(n,C,scale) for n in [32,256,512] for C in [1.,2.] for scale in [1.,1e6]]
    with concurrent.futures.ProcessPoolExecutor(max_workers=4) as pool:
        rows=list(pool.map(run_case,tasks))
    (ex.OUT/'optimizer_scaling_check.json').write_text(json.dumps(rows,indent=2))
    for row in rows: print(json.dumps(row),flush=True)
