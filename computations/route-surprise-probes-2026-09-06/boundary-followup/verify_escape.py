"""Independent audit with simple fixed source parameters, not optimizer coordinates."""
import os
for key in ("OMP_NUM_THREADS","OPENBLAS_NUM_THREADS","MKL_NUM_THREADS"):
    os.environ[key] = "1"
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
import json
import mpmath as mp
import clg_compensation as old
from tail_interventions import data_with_jets
from boundary_search import record


rows = []
for precision,cutoff,match in ((90,40,"fixed_excess"),(150,80,"fixed_excess"),
        (90,40,"actual_mean"),(150,80,"actual_mean")):
    mp.mp.dps = precision
    old.NMAX = cutoff
    a0,t,g,c = mp.mpf(6),mp.mpf(".52"),mp.mpf("1e12"),mp.mpf(1)/5
    x0 = mp.log(a0/mp.pi)/2
    actual = old.moments(a0-mp.mpf("1.5"))
    mass = actual[0]-1
    if match=="actual_mean":
        c = actual[1]/mass-3
    epsilon = c/(g-3)
    def lp(x):
        A = mp.pi*mp.exp(2*x)
        return mp.log1p(mass*((1-epsilon)*mp.exp(-3*(A-a0))+epsilon*mp.exp(-g*(A-a0))))
    def jets(x):
        return tuple(mp.diff(lp,x,j) for j in range(4))
    d = data_with_jets(x0+t,t,jets)
    direct = old.comp3(d,mp.mpf(0))[0]
    independent = mp.diff(lambda l:old.comp3(d,l)[1],mp.mpf(0),3)
    row = record(d,mass,epsilon,mp.mpf(0))
    row.update(dps=precision,cutoff=cutoff,match=match,left_A="6",t=".52",g="1e12",excess=mp.nstr(c,70),
        mass=mp.nstr(mass,80),c3_direct=mp.nstr(direct,80),
        c3_independent=mp.nstr(independent,80),
        relative_error=mp.nstr(abs((direct-independent)/direct),20),
        conditional_moments=[mp.nstr((1-epsilon)*3**j+epsilon*g**j,65) for j in range(4)],
        first_moment_match_error=mp.nstr(mass*((1-epsilon)*3+epsilon*g)-actual[1],30),
        actual_second_conditional_moment=mp.nstr(actual[2]/mass,65))
    rows.append(row)
with open("escape-validation.json","w") as out:
    json.dump(rows,out,indent=2)
print(json.dumps(rows,indent=2))
