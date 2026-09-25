"""Counterexample audit and figures; execute only on the authorized Runpod."""
import json
import math
import time
from pathlib import Path

import mpmath as mp
import numpy as np

ROOT = Path(__file__).resolve().parent


def fresh_counts(edges):
    # Resieve only this interval, using independently enumerated trial-division base primes.
    low, high = int(edges[0]), int(edges[-1])
    base = [n for n in range(2,math.isqrt(high)+1)
            if all(n % d for d in range(2,math.isqrt(n)+1))]
    keep = np.ones(high-low,dtype=bool)
    for p in base:
        first = max(p*p,((low+p-1)//p)*p)
        keep[first-low::p] = False
    return [int(keep[int(a)-low:int(b)-low].sum()) for a,b in zip(edges[:-1],edges[1:])]


def precise(rows,digits):
    mp.mp.dps = digits
    masses = [mp.ei(mp.log(int(row[4])))-mp.ei(mp.log(int(row[3]))) for row in rows]
    residuals = [mp.mpf(int(row[5]))-mass for row,mass in zip(rows,masses)]
    whole = sum(residuals)**2/sum(masses)
    fine = sum(c*c/L for c,L in zip(residuals,masses))/16
    return {"digits":digits,"whole_square":mp.nstr(whole,60),
            "mean_fine_square":mp.nstr(fine,60),"ratio":mp.nstr(whole/fine,60),
            "difference":mp.nstr(whole-fine,60),
            "cell_masses":[mp.nstr(L,60) for L in masses],
            "cell_residuals":[mp.nstr(c,60) for c in residuals]}


def main():
    start = time.monotonic()
    rows = np.load(ROOT/"boundary-validation-rows.npz")["rows"]
    groups = rows.reshape(-1,16,7)
    violations = []
    for group in groups:
        c,L = group[:,5]-group[:,6],group[:,6]
        ratio = c.sum()**2/L.sum()/np.mean(c*c/L)
        if ratio > 1:
            violations.append({"phase_eighths":int(group[0,0]),"k":int(group[0,1]),
                               "ratio":float(ratio)})
    worst = max(violations,key=lambda item:item["ratio"])
    chosen = rows[(rows[:,0] == worst["phase_eighths"]) & (rows[:,1] == worst["k"])]
    edges = np.r_[chosen[:,3],chosen[-1,4]].astype(np.int64)
    counts = fresh_counts(edges)
    assert counts == chosen[:,5].astype(int).tolist()
    p60,p90 = precise(chosen,60),precise(chosen,90)
    assert abs(mp.mpf(p60["ratio"])-mp.mpf(p90["ratio"])) < mp.mpf("1e-45")
    # A second numerical integration method checks the analytic antiderivative.
    quadrature = [mp.quad(lambda x:1/mp.log(x),[int(a),int(b)])
                  for a,b in zip(edges[:-1],edges[1:])]
    mp.mp.dps = 90
    quad_error = max(abs(q-mp.mpf(L)) for q,L in zip(quadrature,p90["cell_masses"]))
    assert quad_error < mp.mpf("1e-50")
    out = {"phase":"audit","violations_count":len(violations),"observations":len(groups),
        "violations":violations,"worst":worst,"edges":edges.tolist(),"counts":counts,
        "fresh_interval_sieve_matches":True,"precision_60":p60,"precision_90":p90,
        "independent_quadrature_max_error":mp.nstr(quad_error,30),
        "wall_seconds":time.monotonic()-start}
    (ROOT/"audit.json").write_text(json.dumps(out,indent=2))
    np.savetxt(ROOT/"worst-block.csv",chosen,delimiter=",",
        header="phase_eighths,k,j,a,b,count,reference_mass",comments="",
        fmt=["%d","%d","%d","%d","%d","%d","%.17g"])
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        fig,axes = plt.subplots(1,2,figsize=(11,4.2),layout="constrained")
        discovery=json.loads((ROOT/"boundary-discovery.json").read_text())
        validation=json.loads((ROOT/"boundary-validation.json").read_text())
        extensions=[json.loads((ROOT/name).read_text()) for name in
            ["extension.json","extension-k256.json"] if (ROOT/name).exists()]
        labels=["4–22","24–30","32–62","64–88"]+[
            f"{entry['range'][0]}–{entry['range'][1]}" for entry in extensions]
        for t in range(8):
            values=[r["ratio"] for data in [discovery,validation]
                    for r in data["results"][t]["ranges"]]
            values += [entry["results"][t]["ratio"] for entry in extensions]
            axes[0].plot(range(len(labels)),values,marker="o",label=f"{t}/8",alpha=.8)
        axes[0].axhline(.5,color="black",linestyle="--",label="Frozen B2 ceiling")
        axes[0].set_xticks(range(len(labels)),labels,rotation=20)
        axes[0].set_xlabel("Quartic block index k")
        axes[0].set_ylabel("Whole / fine mean squared count error")
        axes[0].set_title("Fixed average margin fails on the larger band" if
            any(not entry["advance"] for entry in extensions) else "Average reduction across scale bands")
        axes[0].legend(fontsize=7,ncol=3)
        c,L=chosen[:,5]-chosen[:,6],chosen[:,6]
        axes[1].bar(np.arange(16),c/np.sqrt(L),color=np.where(c>=0,"#b94a48","#337ab7"))
        axes[1].axhline(0,color="black",linewidth=.8)
        axes[1].set_xlabel("Fine cell j")
        axes[1].set_ylabel("(Prime count − reference mass) / √mass")
        axes[1].set_title(f"Pointwise contraction fails: k={worst['k']}, shift={worst['phase_eighths']}/8")
        fig.suptitle("Finite numerical evidence — no all-scale bound or RH proof",fontsize=12)
        fig.savefig(ROOT/"comparison.png",dpi=170)
        fig.savefig(ROOT/"comparison.pdf")
        plt.close(fig)
    except ImportError as e:
        (ROOT/"plot-unavailable.txt").write_text(str(e))
    print(json.dumps({"violations":len(violations),"worst":worst,
        "high_precision_ratio":p90["ratio"],"high_precision_difference":p90["difference"],
        "fresh_sieve_matches":True,"wall_seconds":time.monotonic()-start},indent=2))


if __name__ == "__main__":
    main()
