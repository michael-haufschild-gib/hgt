"""Locate and display the separated sign crossings of the actual-mean replacement."""
import os
for key in ("OMP_NUM_THREADS","OPENBLAS_NUM_THREADS","MKL_NUM_THREADS"):
    os.environ[key] = "1"
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
import json
import mpmath as mp
import clg_compensation as old
from tail_interventions import data_with_jets, atomic_jets
from tail_moment_dissection import channels


mp.mp.dps = 90
old.NMAX = 40
a0,t = mp.mpf(6),mp.mpf(".52")
x0 = mp.log(a0/mp.pi)/2
actual = old.moments(a0-mp.mpf("1.5"))
mass = actual[0]-1
c = actual[1]/mass-3


def values(logg):
    g = 10**logg
    e = c/(g-3)
    d = data_with_jets(x0+t,t,lambda x:atomic_jets(x,x0,mass,[mp.mpf(3),g],[1-e,e]))
    terms,h2 = channels(d,mp.mpf(0))
    D = -d["da"]
    return sum(terms)/mass**3,h2/mass**2,h2/(2*D*D)


def crossing(index):
    lo,hi = mp.mpf(6),mp.mpf(16)
    flo = values(lo)[index]
    if flo*values(hi)[index] >= 0:
        raise ValueError("Missing sign bracket")
    for _ in range(100):
        mid = (lo+hi)/2
        fm = values(mid)[index]
        if flo*fm>0:
            lo,flo = mid,fm
        else:
            hi = mid
    return dict(log10_bracket=[mp.nstr(lo,60),mp.nstr(hi,60)],
        node=mp.nstr(10**((lo+hi)/2),50))


roots = dict(compensation=crossing(0),curvature=crossing(1))
grid = [mp.mpf(6)+mp.mpf(j)/15 for j in range(151)]
rows = [dict(logg=str(x),values=[mp.nstr(y,45) for y in values(x)]) for x in grid]
with open("escape-profile.json","w") as f:
    json.dump(dict(roots=roots,rows=rows),f,indent=2)
print(json.dumps(roots,indent=2))

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
fig,ax = plt.subplots(figsize=(9,5),layout="constrained")
x = [float(r["logg"]) for r in rows]
for i,label,color in ((0,"Complete compensation", "#b64232"),(1,"Lower-transport curvature", "#207a65")):
    y = [float(mp.mpf(r["values"][i])/mp.mpf(rows[0]["values"][i])) for r in rows]
    ax.plot(x,y,label=label,color=color,lw=2)
ax.axhline(0,color="#555555",lw=.8)
ax.set_yscale("symlog",linthresh=.15)
ax.set_ylim(-1e6,2)
ax.set_xlim(6,16)
rc = float(mp.log10(mp.mpf(roots["compensation"]["node"])))
rh = float(mp.log10(mp.mpf(roots["curvature"]["node"])))
ax.axvspan(rc,rh,color="#f7c66b",alpha=.22,label="Compensation negative, curvature positive")
ax.set_xlabel("log₁₀(remote spectral node)")
ax.set_ylabel("Each quantity divided by its value at node 10⁶")
ax.set_title("Mass and mean preserved; the compensation sign still fails")
ax.legend(loc="lower left",fontsize=9)
ax.grid(alpha=.15)
fig.text(.5,-.015,"Positive two-atom replacement, left scale 6, displacement 0.52. Counterfactual source; no RH conclusion.",
    ha="center",fontsize=9)
fig.savefig("escape-profile.png",dpi=170,bbox_inches="tight")
fig.savefig("escape-profile.svg",bbox_inches="tight")
