"""Independent differentiated audit of the smallest observed slope-boundary reserve."""
import os
for key in ("OMP_NUM_THREADS","OPENBLAS_NUM_THREADS","MKL_NUM_THREADS"):
    os.environ[key] = "1"
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
import json
import mpmath as mp
import clg_compensation as original
from tail_interventions import data_with_jets


rows = []
for precision, cutoff in ((90,40),(140,80)):
    mp.mp.dps = precision
    original.NMAX = cutoff
    mass = original.moments(mp.pi-mp.mpf("1.5"))[0]-1
    def lp(x):
        return mp.log1p(mass*mp.exp(-3*(mp.pi*mp.exp(2*x)-mp.pi)))
    def get_jets(x):
        return tuple(mp.diff(lp,x,j) for j in range(4))
    def data(t):
        return data_with_jets(t,t,get_jets)
    def root_equation(t):
        d = data(t)
        beta = 1+2/mp.expm1(d["q"])
        r = -d["da"]/(d["a"]*(-d["dq"]))
        return r-beta/2
    t = mp.findroot(root_equation,(mp.mpf(".47"),mp.mpf(".48")))
    d = data(t)
    direct = original.comp3(d,mp.mpf(0))[0]
    differentiated = mp.diff(lambda l:original.comp3(d,l)[1],mp.mpf(0),3)
    H = d["a"]*t*d["m"]-(d["a"]+t*d["b"])*d["s"]
    H2 = 2*(d["da"]*t*d["dm"]-(d["da"]+t*d["db"])*d["ds"])
    h = H2/((-H)*d["dq"]**2)
    q = d["q"]
    beta = 1+2/mp.expm1(q)
    critical = (4*mp.exp(-q)/(1-mp.exp(-q))**2)/(3*(3*beta+2))
    rows.append(dict(dps=precision,cutoff=cutoff,t=mp.nstr(t,70),
        mass=mp.nstr(mass,70),c3=mp.nstr(direct,70),
        independently_differentiated_c3=mp.nstr(differentiated,70),
        relative_difference=mp.nstr(abs((direct-differentiated)/direct),15),
        h2=mp.nstr(H2,70),curvature_ratio=mp.nstr(h/critical,70),
        root_residual=mp.nstr(root_equation(t),15)))
with open("boundary-validation.json","w") as f:
    json.dump(rows,f,indent=2)
print(json.dumps(rows,indent=2))
