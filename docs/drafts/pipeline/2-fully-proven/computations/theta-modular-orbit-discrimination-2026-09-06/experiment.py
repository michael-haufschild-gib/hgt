"""Source ODE experiment. All mathematical computation belongs on Runpod."""
import os
os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1')
from pathlib import Path
import json,time,multiprocessing as pool
import numpy as np
import sympy as sy
import mpmath as mp
from scipy.integrate import solve_ivp
from scipy.stats import qmc
ROOT=Path(__file__).resolve().parent

def rhs(x,y):
    S,A,W=y
    return (3-S*S/3-3*A/4,-2*A*W,2+A/2+2*S*S/9-2*S*W/3)

def signature(y):
    f=np.asarray([fn(*y) + np.zeros_like(np.asarray(y)[0]) for fn in JETS])
    p0=f[0]**2;p2=2*(f[0]*f[2]-f[1]**2)
    p4=2*f[0]*f[4]-8*f[1]*f[3]+6*f[2]**2
    p6=2*f[0]*f[6]-12*f[1]*f[5]+30*f[2]*f[4]-20*f[3]**2
    p8=2*f[0]*f[8]-16*f[1]*f[7]+56*f[2]*f[6]-112*f[3]*f[5]+70*f[4]**2
    terms=np.array([p0*p4*p8,-p0*p6*p6,-p2*p2*p8,2*p2*p4*p6,-p4**3])
    d=terms.sum(axis=0);mass=np.abs(terms).sum(axis=0)
    return f[0],d,np.divide(d,mass,out=np.zeros_like(d),where=mass>0)

def run(item):
    label,X=item
    t=np.unique(np.r_[np.linspace(0,137/2000,129),np.linspace(.07,.3,94)])
    sol=solve_ivp(rhs,(0,.3),(0,X,0),t_eval=t,rtol=2e-12,atol=2e-13,method='DOP853')
    f,d,rel=signature(sol.y)
    def exit_big(t,y):return 1e5-np.linalg.norm(y)
    exit_big.terminal=True;exit_big.direction=-1
    long=solve_ivp(rhs,(0,5),(0,X,0),dense_output=True,events=exit_big,rtol=2e-12,atol=2e-13,method='DOP853')
    tl=np.linspace(0,long.t[-1],301);yl=long.sol(tl)
    compact=sol.t<=137/2000
    return dict(label=label,X=X,success=sol.success,points=sol.t.tolist(),states=sol.y.T.tolist(),
                source_f0=f.tolist(),D1=d.tolist(),relative=rel.tolist(),
                compact_min=float(d[compact].min()),compact_min_relative=float(rel[compact].min()),
                min_relative=float(rel.min()),negative_count=int(np.sum(rel< -1e-8)),
                long_end=float(long.t[-1]),long_success=long.success,long_points=tl.tolist(),long_states=yl.T.tolist())

if __name__=='__main__':
    start=time.monotonic();S,A,W=sy.symbols('S A W');vs=(S,A,W)
    F=(3-S*S/3-3*A/4,-2*A*W,2+A/2+2*S*S/9-2*S*W/3)
    H=[sy.Integer(1)]
    for n in range(10):H.append(sy.Poly(sum(sy.diff(H[-1],v)*g for v,g in zip(vs,F))-S*H[-1]/6,*vs).as_expr())
    polys=[sy.Poly((H[n+2]-H[n]/4)/2,*vs) for n in range(9)]
    JETS=[sy.lambdify(vs,p.as_expr(),'numpy',cse=True) for p in polys]
    (ROOT/'jet_polynomials.json').write_text(json.dumps([[dict(exponents=list(e),coefficient=str(c)) for e,c in p.terms()] for p in polys],indent=2)+'\n')
    # Independent corpus seam polynomial identity, before any numerical experiment.
    X=sy.symbols('X');fj=[p.as_expr().subs({S:0,A:X,W:0}) for p in polys]
    p0=fj[0]**2;p2=2*fj[0]*fj[2];p4=2*fj[0]*fj[4]+6*fj[2]**2
    p6=2*fj[0]*fj[6]+30*fj[2]*fj[4];p8=2*fj[0]*fj[8]+56*fj[2]*fj[6]+70*fj[4]**2
    seam=sy.expand(p0*p4*p8-p0*p6**2-p2**2*p8+2*p2*p4*p6-p4**3)
    coeff=[(3444525,512),(-80754975,2048),(4194195795,65536),(-2646917595,65536),(5201727255,524288),(-1723813569,1048576),(4581650223,16777216),(-612571059,16777216),(35927199,16777216),(1999197,268435456),(-117855,134217728),(-13245,536870912),(14025,8589934592)]
    assert sy.expand(seam-sum(sy.Rational(a,b)*X**i for i,(a,b) in enumerate(coeff)))==0
    mp.mp.dps=60;theta=1+2*mp.fsum(mp.exp(-mp.pi*n*n) for n in range(1,21));X0=(mp.pi*theta**4)**2
    items=[(f'X={x}',x) for x in (6.25,10,15,18,19,19.1,19.2,20,25,40)]
    items+=[('theta',float(X0))]+[(f'theta_delta={delta}',float(X0)*(1+delta)) for delta in (-.01,-.0001,-.000001,.000001,.0001,.01)]
    with pool.get_context('fork').Pool(8) as p:rows=list(p.imap(run,items))
    box=qmc.Sobol(3,scramble=True,seed=20260906).random_base2(13)*np.array([1,3,1.2])+np.array([-1,17,0])
    f,d,rel=signature(box.T);j=int(np.argmin(rel))
    np.savez_compressed(ROOT/'box.npz',states=box,D1=d,relative=rel,source_f0=f)
    out=dict(source_X0=mp.nstr(X0,60),seam_identity_exact=True,rows=rows,
             box=dict(min_relative=float(rel[j]),witness=box[j].tolist(),D1=float(d[j]),negative_count=int(np.sum(rel< -1e-8))),seconds=time.monotonic()-start)
    (ROOT/'results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({**{k:v for k,v in out.items() if k!='rows'},'rows':[{k:v for k,v in r.items() if k not in ('points','states','source_f0','D1','relative','long_points','long_states')} for r in rows]},indent=2))
