"""Independent differential audit of the mass/mean/second-moment counterfactual."""
import json
import mpmath as mp
from tail_moment_dissection import model
from tail_interventions import data_with_jets
import clg_compensation as old

rows=[]
for precision,cutoff in ((80,40),(120,40),(120,80)):
    mp.mp.dps=precision
    old.NMAX=cutoff
    x0=mp.log(6/mp.pi)/2
    t=mp.mpf(".0001")
    e=mp.mpf(".000000003")
    z,m1,m2,m3=old.moments(old.Bcoord(x0))
    mass=z-1
    moments=[mp.mpf(1),m1/mass,m2/mass,m3/mass]
    nodes,weights=model(moments,mp.mpf(255),e,2)
    def lp(x):
        da=mp.pi*(mp.exp(2*x)-mp.exp(2*x0))
        return mp.log1p(mass*sum(w*mp.exp(-da*g) for g,w in zip(nodes,weights)))
    def jets(x):
        return (lp(x),mp.diff(lp,x),mp.diff(lp,x,2),mp.diff(lp,x,3))
    d=data_with_jets(x0+t,t,jets)
    direct=old.comp3(d,mp.mpf(0))[0]
    differentiated=mp.diff(lambda l:old.comp3(d,l)[1],mp.mpf(0),3)
    rows.append(dict(dps=precision,NMAX=cutoff,nodes=[mp.nstr(g,65) for g in nodes],
        weights=[mp.nstr(w,65) for w in weights],
        matched_moment_errors=[mp.nstr(sum(w*g**j for w,g in zip(weights,nodes))-moments[j],10) for j in range(3)],
        c3=mp.nstr(direct,65),independent_derivative=mp.nstr(differentiated,65),
        relative_difference=mp.nstr(abs((direct-differentiated)/direct),10)))
with open("moment-witness-validation.json","w") as f:
    json.dump(rows,f,indent=2)
print(json.dumps(rows))
