"""Inverse-design positive measures on r=beta/2, where two-channel budget is adverse."""
import os
for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import json
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
import mpmath as mp
from boundary_search import literal_moments, jets, record
from tail_interventions import data_with_jets


def run(spec):
    mp.mp.dps = 90
    left, node, weight, ls = spec
    A0 = mp.pi if left == "pi" else mp.mpf(left)
    g, epsilon, l = map(mp.mpf,(node,weight,ls))
    mass = literal_moments(A0)[0]
    x0 = mp.log(A0/mp.pi)/2
    def data(t):
        def get_jets(x):
            A = mp.pi*mp.exp(2*x)
            moments = [mass*((1-epsilon)*3**j*mp.exp(-3*(A-A0))+
                epsilon*g**j*mp.exp(-g*(A-A0))) for j in range(4)]
            return jets(A,moments)
        return data_with_jets(x0+t,t,get_jets)
    def objective(t):
        d = data(t)
        q = d["q"]+l*d["dq"]
        a = d["a"]+l*d["da"]
        if q <= 0 or a <= 0:
            return None
        r = -d["da"]/(a*(-d["dq"]))
        beta = 1+2/mp.expm1(q)
        return r-beta/2
    lo = max(mp.mpf(".005"),mp.log(6/A0)/2+mp.mpf(".000001"))
    hi = mp.mpf(3)
    flo, fhi = objective(lo), objective(hi)
    if flo is None or fhi is None or flo*fhi >= 0:
        return dict(spec=spec,unbracketed=True)
    for _ in range(100):
        mid = (lo+hi)/2
        fm = objective(mid)
        if fm*flo > 0:
            lo, flo = mid, fm
        else:
            hi, fhi = mid, fm
    t = (lo+hi)/2
    d = data(t)
    out = record(d,mass,epsilon,l)
    q = d["q"]+l*d["dq"]
    a,b,S,m = (d[k]+l*d["d"+k] for k in ("a","b","s","m"))
    H = a*t*m-(a+t*b)*S
    H2 = 2*(d["da"]*t*d["dm"]-(d["da"]+t*d["db"])*d["ds"])
    h = H2/((-H)*d["dq"]**2)
    k = 4*mp.exp(-q)/(1-mp.exp(-q))**2
    beta = 1+2/mp.expm1(q)
    critical = k/(3*(3*beta+2))
    out.update(spec=spec,t=mp.nstr(t,60),root_residual=mp.nstr(objective(t),20),
        log10_curvature_ratio=mp.nstr(mp.log10(h/critical),35) if h>0 else None,
        positive_curvature=bool(h>0),critical_curvature=mp.nstr(critical,35))
    return out


if __name__ == "__main__":
    start = time.monotonic()
    weights = ["0",".000000001",".000001",".001",".01",".1",".5",".9","1"]
    specs = [(a,g,w,l) for a in ("pi","4","6","9","16")
        for g in ("15","255","4095") for w in weights for l in ("0","1")]
    results = []
    with ProcessPoolExecutor(max_workers=8) as pool,open("slope-boundary.jsonl","w") as f:
        for result in as_completed([pool.submit(run,s) for s in specs]):
            row = result.result()
            results.append(row)
            f.write(json.dumps(row)+"\n")
            f.flush()
    eligible = [r for r in results if r.get("gates")]
    summary = dict(seconds=time.monotonic()-start,specs=len(specs),
        bracketed=sum(not r.get("unbracketed",False) for r in results),eligible=len(eligible),
        counterexamples=sum(r["counterexample"] for r in eligible),
        smallest_reserves=sorted(eligible,key=lambda r:mp.mpf(r["log10_curvature_ratio"]))[:5])
    with open("slope-boundary.json","w") as f:
        json.dump(dict(summary=summary,results=results),f,indent=2)
    print(json.dumps(summary,indent=2))
