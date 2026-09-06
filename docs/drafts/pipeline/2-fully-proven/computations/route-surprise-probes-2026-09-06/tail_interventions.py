"""Mass-matched spectral interventions on the C5 higher likelihood tail."""
import os
for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import json
import time
from concurrent.futures import ProcessPoolExecutor
from itertools import combinations
import mpmath as mp
import clg_compensation as old


def atomic_jets(x, x0, mass, nodes, probs):
    A = mp.pi*mp.exp(2*x)
    A0 = mp.pi*mp.exp(2*x0)
    moments = [mass*sum(p*g**j*mp.exp(-(A-A0)*g) for g,p in zip(nodes,probs)) for j in range(4)]
    z = 1+moments[0]
    mean = moments[1]/z
    var = moments[2]/z-mean**2
    k3 = moments[3]/z-3*mean*moments[2]/z+2*mean**3
    return (mp.log1p(moments[0]), -2*A*mean,
        4*A*A*var-4*A*mean, -8*A**3*k3+24*A*A*var-8*A*mean)


def data_with_jets(u, t, jets):
    # Explicit callback avoids changing the imported solver's source function.
    A = old.Ascale(u)
    z = mp.cosh(2*t)-1
    zp = 2*mp.sinh(2*t)
    lam = 3*A/(A-mp.mpf("1.5"))**2
    F = 1-lam*z
    if F <= 0:
        raise ValueError("Outside first-atom background domain")
    slope = 2*A+lam/F
    d = -6*A*(A+mp.mpf("1.5"))/(A-mp.mpf("1.5"))**3
    lu,j1u,j2u,j3u = jets(u)
    lp,j1p,j2p,j3p = jets(u+t)
    lm,j1m,j2m,j3m = jets(u-t)
    return dict(t=t,q=2*A*z-mp.log(F),dq=2*lu-lp-lm,
        a=slope*zp,da=j1m-j1p,
        b=4*lam**2/F**2*z*(z+2)+4*slope*(z+1),db=-j2p-j2m,
        c=zp*(8*lam**3/F**3*z*(z+2)+12*lam**2/F**2*(z+1)+4*slope),dc=j3m-j3p,
        s=4*A*z+d*z/F,ds=2*j1u-j1p-j1m,
        m=(4*A+d/F**2)*zp,dm=j2m-j2p,
        n=4*(2*lam*d/F**3*z*(z+2)+(4*A+d/F**2)*(z+1)),dn=-j3p-j3m)


def run(spec):
    left_a, ts = spec
    mp.mp.dps = 60
    a0 = mp.pi if left_a == "pi" else mp.mpf(left_a)
    t = mp.mpf(ts)
    x0 = mp.log(a0/mp.pi)/2
    u = x0+t
    if old.Ascale(u) < 6:
        return []
    mass = old.moments(old.Bcoord(x0))[0]-1
    nodes = list(map(mp.mpf,[3,4,8,15,24,63,255]))
    models = [("one_atom",[g],[mp.mpf(1)]) for g in nodes]
    for g,h in combinations(nodes,2):
        for prob in (".01",".1",".5",".9",".99"):
            p = mp.mpf(prob)
            models.append(("two_atom",[g,h],[p,1-p]))
    rows = []
    literal_data = data_with_jets(u,t,old.LPjets)
    models.insert(0,("literal",[],[]))
    for kind,gs,ps in models:
        d = literal_data if kind=="literal" else data_with_jets(u,t,
            lambda x: atomic_jets(x,x0,mass,gs,ps))
        for ls in ("0",".5","1"):
            c3,c0,act,vc = old.comp3(d,mp.mpf(ls))
            rows.append(dict(left_A=left_a,t=ts,u=mp.nstr(u,25),kind=kind,
                nodes=[str(g) for g in gs],probs=[str(p) for p in ps],l=ls,
                mass=mp.nstr(mass,25),c3=mp.nstr(c3,25),c0=mp.nstr(c0,25),
                c3_over_mass_cubed=mp.nstr(c3/mass**3,25),action=mp.nstr(act,25),
                velocity_center=mp.nstr(vc,25)))
    return rows


if __name__ == "__main__":
    start = time.monotonic()
    jobs = [(a,t) for a in ("pi","4","6","9") for t in (".02",".08",".2",".45",".8")]
    with ProcessPoolExecutor(max_workers=8) as pool:
        groups = list(pool.map(run,jobs))
    rows = [r for group in groups for r in group]
    out = dict(experiment="H3",seconds=time.monotonic()-start,dps=60,NMAX=old.NMAX,rows=rows)
    with open("tail-results.json","w") as f:
        json.dump(out,f,indent=2)
    for kind in ("literal","one_atom","two_atom"):
        sub = [r for r in rows if r["kind"]==kind]
        neg = [r for r in sub if mp.mpf(r["c3"])<0]
        print(kind,len(sub),"negative",len(neg),flush=True)
        if neg:
            print("witness",json.dumps(neg[0]),flush=True)
    print("seconds",out["seconds"],flush=True)
