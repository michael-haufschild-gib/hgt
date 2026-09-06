"""Hostile optimization between the two compensation boundaries; run on Runpod only."""
import os
for key in ("OMP_NUM_THREADS","OPENBLAS_NUM_THREADS","MKL_NUM_THREADS"):
    os.environ[key] = "1"
import json
import math
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
import numpy as np
from scipy.optimize import differential_evolution, minimize


def source_mass(a0):
    return sum(math.exp(-a0*(n*n-1))*(n**4+1.5*n*n*(n*n-1)/(a0-1.5))
        for n in range(2,12))


def evaluate(x, atoms, floor, mass_multiplier=1):
    a0, t, l = floor+x[0], x[1], x[2]
    nodes = np.r_[3.,3+10**np.array(x[3:atoms+2])]
    logits = np.r_[0.,x[atoms+2:2*atoms+1]]
    weights = np.exp(logits-np.max(logits))
    weights /= np.sum(weights)
    mass = source_mass(a0)*mass_multiplier
    ac = a0*math.exp(2*t)
    scales = np.array([ac,ac*math.exp(2*t),a0])
    damp = weights[None,:]*np.exp(-(scales[:,None]-a0)*nodes[None,:])*mass
    m0,m1,m2,m3 = [np.sum(damp*nodes[None,:]**j,axis=1) for j in range(4)]
    z0 = 1+m0
    mean = m1/z0
    variance = m2/z0-mean**2
    c3 = m3/z0-3*mean*m2/z0+2*mean**3
    f = np.log1p(m0)
    j1 = -2*scales*mean
    j2 = 4*scales**2*variance-4*scales*mean
    j3 = -8*scales**3*c3+24*scales**2*variance-8*scales*mean
    z = 2*math.sinh(t)**2
    zp = 2*math.sinh(2*t)
    alpha = 3*ac/(ac-1.5)**2
    fg = 1-alpha*z
    slope = 2*ac+alpha/fg
    dscl = -6*ac*(ac+1.5)/(ac-1.5)**3
    dq = 2*f[0]-f[1]-f[2]
    da = j1[2]-j1[1]
    db = -j2[1]-j2[2]
    ds = 2*j1[0]-j1[1]-j1[2]
    dm = j2[2]-j2[1]
    q = 2*ac*z-math.log(fg)+l*dq
    a = slope*zp+l*da
    b = 4*alpha**2/fg**2*z*(z+2)+4*slope*(z+1)+l*db
    S = 4*ac*z+dscl*z/fg+l*ds
    m = (4*ac+dscl/fg**2)*zp+l*dm
    H = a*t*m-(a+t*b)*S
    H1 = da*t*m+a*t*dm-(da+t*db)*S-(a+t*b)*ds
    H2 = 2*(da*t*dm-(da+t*db)*ds)
    gates = q>0 and a>0 and b>0 and S>0 and H<0 and H1>0 and H2>0 and dq<0
    if not gates:
        return dict(score=100.,gates=False)
    beta = 1+2*math.exp(-q)/(-math.expm1(-q))
    r, s, h = -da/(a*(-dq)), H1/((-H)*(-dq)), H2/((-H)*dq*dq)
    logk = math.log(4)-q-2*math.log(-math.expm1(-q))
    k = math.exp(logk) if logk>-740 else 0.
    L = (6+4*beta)*r-2*k
    gap = 12*(r-beta/2)*(s-beta/2)-1
    base = 12*(r-beta/2)*(r+s-r+h/(2*r)-beta/2)-1
    if L<=0:
        score = -1000.
    elif gap>=0:
        score = 50+math.log1p(gap)
    else:
        score = (math.log(h)-logk-math.log(-gap)+math.log(3*L))/math.log(10)
    return dict(score=float(score),gates=True,left_A=float(a0),t=float(t),l=float(l),
        nodes=nodes.tolist(),weights=weights.tolist(),mass=float(mass),
        mass_multiplier=mass_multiplier,q=float(q),r=float(r),s=float(s),h=float(h),
        gap=float(gap),base_gap=float(base),lower_slope=float(L),
        h2=float(H2),beta=float(beta),x=list(map(float,x)))


def run(spec):
    atoms, floor, seed = spec
    start = time.monotonic()
    bounds = [(0,12),(.015,1.4),(0,1)]+[(-3,4.5)]*(atoms-1)+[(-25,25)]*(atoms-1)
    count = 0
    best = None
    def objective(x):
        nonlocal count,best
        count += 1
        try:
            row = evaluate(x,atoms,floor)
            score = row["score"]
        except (ValueError,OverflowError,ZeroDivisionError,FloatingPointError):
            return 1000.
        if row["gates"] and (best is None or score<best["score"]):
            best = row
        return score
    result = differential_evolution(objective,bounds,seed=seed,popsize=8,maxiter=140,
        tol=1e-8,polish=False,callback=lambda x,convergence:time.monotonic()-start>24)
    minimize(objective,result.x,method="Nelder-Mead",bounds=bounds,
        options=dict(maxiter=300,xatol=1e-9,fatol=1e-9))
    return dict(spec=spec,seconds=time.monotonic()-start,evaluations=count,best=best,
        solver_success=bool(result.success),solver_message=str(result.message))


if __name__ == "__main__":
    start = time.monotonic()
    specs = [(a,f,s) for a in (3,4) for f in (math.pi,6.) for s in (1021,1022,1023,1024)]
    rows = []
    with ProcessPoolExecutor(max_workers=8) as pool,open("interior-results.jsonl","w") as out:
        for future in as_completed([pool.submit(run,s) for s in specs]):
            row = future.result()
            rows.append(row)
            out.write(json.dumps(row)+"\n")
            out.flush()
            print(json.dumps(dict(spec=row["spec"],seconds=row["seconds"],
                best=None if row["best"] is None else row["best"]["score"])),flush=True)
    summary = dict(seconds=time.monotonic()-start,results=rows)
    with open("interior-results.json","w") as out:
        json.dump(summary,out,indent=2)
