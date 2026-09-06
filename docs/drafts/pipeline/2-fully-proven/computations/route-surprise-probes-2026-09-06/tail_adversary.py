"""Use a negative mixed tensor to locate tiny spectral contaminants, then validate."""
import os
for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import json
import time
from concurrent.futures import ProcessPoolExecutor
import mpmath as mp
from tail_polarization import linear_jets
from tail_interventions import data_with_jets, atomic_jets
import clg_compensation as old


def run(spec):
    left,ts,gs = spec
    mp.mp.dps = 80
    a0,t,g = map(mp.mpf,(left,ts,gs))
    x0 = mp.log(a0/mp.pi)/2
    u = x0+t
    base = data_with_jets(u,t,lambda x:(0,0,0,0))
    d1 = data_with_jets(u,t,lambda x:linear_jets(x,x0,mp.mpf(3)))
    d2 = data_with_jets(u,t,lambda x:linear_jets(x,x0,g))
    def p(w1,w2):
        d = base.copy()
        for key in ("dq","da","db","dc","ds","dm","dn"):
            d[key] = w1*d1[key]+w2*d2[key]
        return old.comp3(d,mp.mpf(0))[0]
    c0,c3 = p(1,0),p(0,1)
    plus = p(1,1)-c0-c3
    minus = p(1,-1)-c0+c3
    c1,c2 = (plus-minus)/2,(plus+minus)/2
    # Homogeneous cubic p(1,w)=c0+c1*w+c2*w²+c3*w³.
    discriminant = 4*c2*c2-12*c3*c1
    candidates = [mp.mpf(0)]
    if discriminant >= 0 and c3:
        candidates += [v for v in ((-2*c2-mp.sqrt(discriminant))/(6*c3),
            (-2*c2+mp.sqrt(discriminant))/(6*c3)) if v>0]
    best_w = min(candidates,key=lambda w:p(1,w))
    eps = best_w/(1+best_w)
    mass = old.moments(old.Bcoord(x0))[0]-1
    rows = []
    for factor in (".1",".3","1","3","10"):
        e = eps*mp.mpf(factor)
        if not 0 < e < 1:
            continue
        d = data_with_jets(u,t,lambda x:atomic_jets(x,x0,mass,[mp.mpf(3),g],[1-e,e]))
        for ls in ("0",".5","1"):
            val = old.comp3(d,mp.mpf(ls))[0]
            rows.append(dict(epsilon=mp.nstr(e,45),factor=factor,l=ls,c3=mp.nstr(val,45),
                c3_over_mass_cubed=mp.nstr(val/mass**3,35)))
    return dict(left_A=left,t=ts,g=gs,coefficients=[mp.nstr(v,50) for v in (c0,c1,c2,c3)],
        leading_best_weight=mp.nstr(eps,45),leading_minimum=mp.nstr(p(1,best_w)/(1+best_w)**3,45),
        mass=mp.nstr(mass,45),rows=rows)


def validate(case,row,dps):
    mp.mp.dps = dps
    a0,t,g = map(mp.mpf,(case["left_A"],case["t"],case["g"]))
    e,l = map(mp.mpf,(row["epsilon"],row["l"]))
    x0 = mp.log(a0/mp.pi)/2
    u = x0+t
    mass = old.moments(old.Bcoord(x0))[0]-1
    def lp(x):
        da = mp.pi*(mp.exp(2*x)-mp.exp(2*x0))
        return mp.log1p(mass*((1-e)*mp.exp(-3*da)+e*mp.exp(-g*da)))
    def jets(x):
        return (lp(x),mp.diff(lp,x,1),mp.diff(lp,x,2),mp.diff(lp,x,3))
    d = data_with_jets(u,t,jets)
    closed = old.comp3(d,l)[0]
    # Differentiate the original compensation, not its displayed third derivative.
    numerical_derivative = mp.diff(lambda z:old.comp3(d,z)[1],l,3)
    analytic_d = data_with_jets(u,t,lambda x:atomic_jets(x,x0,mass,[mp.mpf(3),g],[1-e,e]))
    analytic = old.comp3(analytic_d,l)[0]
    return dict(dps=dps,closed_from_differentiated_LP=mp.nstr(closed,70),
        third_derivative_of_compensation=mp.nstr(numerical_derivative,70),
        analytic_jets=mp.nstr(analytic,70),relative_derivative_error=mp.nstr(abs((closed-numerical_derivative)/closed),10),
        relative_jet_error=mp.nstr(abs((closed-analytic)/closed),10))


if __name__ == "__main__":
    start = time.monotonic()
    jobs = [(a,t,g) for a in ("6","9","30") for t in (".0001",".0003",".001",".003",".01",".03") for g in ("24","63","255")]
    with ProcessPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(run,jobs))
    negatives = [(case,row) for case in results for row in case["rows"] if mp.mpf(row["c3"])<0]
    witness = None
    if negatives:
        case,row = min(negatives,key=lambda v:mp.mpf(v[1]["c3_over_mass_cubed"]))
        witness = dict(case={k:v for k,v in case.items() if k!="rows"},row=row,
            validation=[validate(case,row,dps) for dps in (80,120)])
    out = dict(seconds=time.monotonic()-start,results=results,negative_count=len(negatives),witness=witness)
    with open("tail-adversary.json","w") as f:
        json.dump(out,f,indent=2)
    print("negative_count",len(negatives),flush=True)
    print("witness",json.dumps(witness),flush=True)
    print("seconds",out["seconds"],flush=True)
