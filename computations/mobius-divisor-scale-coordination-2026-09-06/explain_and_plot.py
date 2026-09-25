"""Audit the large-prime fiber explanation and render exported figures on Runpod."""
import json
import os
from pathlib import Path
import time

os.environ.update(OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1", MKL_NUM_THREADS="1")
import numpy as np
import mpmath as mp
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent
started = time.monotonic()
mp.mp.dps = 60
b = [mp.mpf(0), 2*mp.euler-1, mp.log(2)-2+2*mp.euler,
     mp.log(6)-3+2*mp.euler, mp.log(12)-4+2*mp.euler]
F4 = sum(b[k]*(mp.sqrt(k+1)-mp.sqrt(k)) for k in range(1,4))
t0 = (2-F4/b[4])**2
aperture = json.loads((ROOT/"aperture.json").read_text())
with np.load(ROOT/"source.npz") as data:
    primes = np.flatnonzero(data["tau"] == 2)
    psi = data["psi"]
    direct = data["direct"]
checks = []
for row in aperture["endpoints"]:
    M = row["M"]
    y = row["peak_recorded_y"]
    p = primes[(primes>y)&(primes<=M)]
    t = M/p
    q = np.floor(t).astype(int)
    F = direct[q-1]+(psi[q]-q+2*float(mp.euler))*(t-q)/(np.sqrt(t)+np.sqrt(q))
    # For y>sqrt(M), each nontrivial rough part is one prime; collapse its whole cofactor family.
    assert y*y > M
    rough_sum = float(-np.sum(np.sqrt(p)*F)/M)
    matched = next(r for r in row["rows"] if r["y"]==y)
    residual = rough_sum-(row["actual"]-matched["smooth_mean"])
    assert abs(residual) < 2e-10
    checks.append(dict(M=M, y=y, smooth_mean=matched["smooth_mean"],
                       actual=row["actual"], prime_fiber_rough_sum=rough_sum,
                       residual=residual, bias_fraction=matched["smooth_mean"]**2/matched["ensemble"]))
report = dict(F4=mp.nstr(F4,55), b4=mp.nstr(b[4],55),
              first_candidate_zero_t=mp.nstr(t0,55), aperture_fraction=mp.nstr(1/t0,55),
              explanation="Finite prime-cofactor identity; root values numerical, no all-scale estimate.",
              checks=checks)
(ROOT/"explanation.json").write_text(json.dumps(report,indent=2)+"\n")

plt.rcParams.update({"font.size":10,"axes.spines.top":False,"axes.spines.right":False})
fig, axes = plt.subplots(1,2,figsize=(12,4.5),layout="constrained")
colors = ["#2369bd","#c56824","#6b479a"]
for endpoint,color in zip(aperture["endpoints"][::4],colors):
    x=np.array([r["y"] for r in endpoint["rows"]])
    total=np.array([r["ensemble"] for r in endpoint["rows"]])
    noise=np.array([r["noise_variance"] for r in endpoint["rows"]])
    axes[0].loglog(x,total,"o-",markersize=3,color=color,label="M = %s"%format(endpoint["M"],","))
    axes[0].loglog(x[noise>0],noise[noise>0],"--",color=color,alpha=.6)
axes[0].set(xlabel="Preserved prime cutoff y",ylabel="Ensemble mean square",
            title="Preserving more prime relations can amplify the response")
axes[0].legend(frameon=False)
axes[0].text(.02,.02,"Solid: total   Dashed: centered variance",transform=axes[0].transAxes,fontsize=9)
endpoint=aperture["endpoints"][8]
x=np.array([r["y"] for r in endpoint["rows"]])
smooth=np.array([r["smooth_mean"] for r in endpoint["rows"]])
axes[1].semilogx(x,smooth,"o-",markersize=3,color="#bd573e",label="Smooth part")
axes[1].semilogx(x,endpoint["actual"]-smooth,"o-",markersize=3,color="#207e72",label="Actual rough part")
axes[1].axhline(endpoint["actual"],color="#252525",label="Complete source")
axes[1].axhline(0,color="#bbbbbb",linewidth=.5)
axes[1].set(xlabel="Preserved prime cutoff y",ylabel="Normalized signed source",
            title="M = 1,048,576: large opposite terms leave 0.00227")
axes[1].legend(frameon=False)
fig.savefig(ROOT/"coordination.png",dpi=180)
fig.savefig(ROOT/"coordination.pdf")
print(json.dumps(dict(seconds=time.monotonic()-started,F4=report["F4"],
                     aperture_fraction=report["aperture_fraction"],
                     largest=checks[8],max_identity_error=max(abs(r["residual"]) for r in checks)),indent=2))
