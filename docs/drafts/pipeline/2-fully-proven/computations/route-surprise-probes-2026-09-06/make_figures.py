"""Standalone scientific figures from downloaded-run data; execute on Runpod."""
import os
os.environ["OPENBLAS_NUM_THREADS"]="1"
import json
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap

plt.rcParams.update({"font.size":11,"axes.spines.top":False,"axes.spines.right":False})
def read(name):
    with open(name) as f:
        return json.load(f)

regime=read("regime-diagnostics.json")
phase=regime["phases"]
t=np.array([float(r["t"]) for r in phase])
eps=np.array([float(r["epsilon"]) for r in phase[0]["rows"]])
c3=np.array([[float(r["c3_scaled"]) for r in row["rows"]] for row in phase])
h2=np.array([[float(r["h2_scaled"]) for r in row["rows"]] for row in phase])
fig,ax=plt.subplots(1,2,figsize=(13,5),layout="constrained")
ax[0].pcolormesh(t,eps,np.sign(c3).T,cmap=ListedColormap(["#d65f39","#cbdde8"]),shading="nearest",vmin=-1,vmax=1)
ax[0].contour(t,eps,c3.T,levels=[0],colors=["#9b3015"],linewidths=1.2)
ax[0].contour(t,eps,h2.T,levels=[0],colors=["#234c67"],linestyles="--",linewidths=1)
ax[0].scatter([.003],[.0000026],c="black",marker="x",s=65,zorder=5)
ax[0].set(xscale="log",yscale="log",xlabel="Displacement t",ylabel="Fraction of tail mass at node 255",
    title="Mass preserved; compensation sign changes")
ax[0].text(.03,.04,"Orange: negative M'''\nDashed: H'' = 0\nCross: independently verified witness",
    transform=ax[0].transAxes,fontsize=9,bbox=dict(facecolor="white",alpha=.9,edgecolor="none"))
idx=np.argmin(abs(t-.003))
ax[1].plot(eps,c3[idx],color="#234c67",lw=2)
ax[1].axhline(0,color="black",lw=.8)
ax[1].set(xscale="log",yscale="symlog",xlabel="Fraction of tail mass at node 255",ylabel="M''' / (tail mass)³",
    title="Mixture can lose and regain the sign")
ax[1].set_yscale("symlog",linthresh=.01)
ax[1].text(.03,.95,"t = %.5g; nodes 3 and 255"%t[idx],transform=ax[1].transAxes,va="top",fontsize=10)
fig.suptitle("Counterfactual theta tails: a narrow failure missed by coarse mixture weights",fontsize=14)
fig.savefig("theta-contamination.png",dpi=170)
fig.savefig("theta-contamination.svg")
plt.close(fig)

controls=read("prime-partition-controls.json")["rows"]
fig,axes=plt.subplots(2,2,figsize=(12,7),layout="constrained",sharex=True)
for ax,r in zip(axes.flat,controls):
    values=[v["capture"] for v in r["rows"]]
    ax.hist(values,bins=24,color="#b6ccd8",edgecolor="white")
    ax.axvline(r["residue"]["capture"],color="#bb4f31",lw=2,label="Residue classes modulo 6")
    ax.set(title=f"Basis {r['basis']}; {r['control'].replace('_',' ')}",ylabel="Random balanced partitions")
    ax.text(.03,.9,f"Residue grouping: {100*r['residue_empirical_percentile']:.1f}th percentile",transform=ax.transAxes,fontsize=10)
    ax.legend(fontsize=8,frameon=False)
for ax in axes[-1]:
    ax.set_xlabel("Fraction of collective norm saving captured")
fig.suptitle("Grouping primes: the apparent arithmetic advantage is not stable",fontsize=14)
fig.savefig("prime-grouping-controls.png",dpi=170)
fig.savefig("prime-grouping-controls.svg")
plt.close(fig)

mob=read("mobius-interactions.json")["results"]
fig,axes=plt.subplots(1,3,figsize=(13,4.2),layout="constrained")
for ax,r in zip(axes,[mob[0],mob[1],mob[5]]):
    corr=np.array(r["correlation"])
    np.fill_diagonal(corr,np.nan)
    im=ax.imshow(corr,cmap="RdBu",vmin=-1,vmax=1,origin="lower")
    ax.set(title=r["kind"].replace("_"," "),xlabel="Dyadic block index",ylabel="Dyadic block index")
fig.colorbar(im,ax=axes,label="Normalized block cross energy",shrink=.8)
fig.suptitle("Möbius energy: signed interaction across scales, including matched controls",fontsize=14)
fig.savefig("mobius-interaction-map.png",dpi=170)
fig.savefig("mobius-interaction-map.svg")
plt.close(fig)
print("Created three PNG/SVG figures")
