"""Summarize conditioned crossings; recompute source ratios without rounded coordinates."""
import os
for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import json
from concurrent.futures import ProcessPoolExecutor
import mpmath as mp
from boundary_search import make_family, record


def inspect(result):
    mp.mp.dps = 100
    if not result.get("crossings"):
        return []
    data, mass = make_family(*result["spec"])
    out = []
    for crossing in result["crossings"]:
        epsilon = sum(map(mp.mpf, crossing["bracket"]))/2
        d = data(epsilon)
        for l in map(mp.mpf, ("0", ".5", "1")):
            t = d["t"]
            q = d["q"]+l*d["dq"]
            a, b, S, m = (d[k]+l*d["d"+k] for k in ("a", "b", "s", "m"))
            H = a*t*m-(a+t*b)*S
            H1 = d["da"]*t*m+a*t*d["dm"]-(d["da"]+t*d["db"])*S-(a+t*b)*d["ds"]
            H2 = 2*(d["da"]*t*d["dm"]-(d["da"]+t*d["db"])*d["ds"])
            A, B = -d["dq"], -H
            beta = 1+2/mp.expm1(q)
            r, s, h = -d["da"]/(a*A), H1/(B*A), H2/(B*A*A)
            kappa = s-r+h/(2*r)
            base_gap = 12*(r-beta/2)*(r+kappa-beta/2)-1
            out.append(dict(spec=result["spec"], epsilon=mp.nstr(epsilon,60), l=str(l),
                action=mp.nstr(q,35), r=mp.nstr(r,35), s=mp.nstr(s,35),
                kappa=mp.nstr(kappa,35), h=mp.nstr(h,35),
                base_gap=mp.nstr(base_gap,35),
                gates_without_curvature=bool(q>0 and a>0 and b>0 and S>0 and H<0 and H1>0),
                r_minus_half_beta=mp.nstr(r-beta/2,35),
                s_minus_half_beta=mp.nstr(s-beta/2,35)))
    return out


if __name__ == "__main__":
    with open("boundary-results.json") as f:
        raw = json.load(f)
    with ProcessPoolExecutor(max_workers=8) as pool:
        rows = [row for part in pool.map(inspect,raw["results"]) for row in part]
    admissible = [r for r in rows if r["gates_without_curvature"]]
    side_rows = [r for result in raw["results"] for c in result.get("crossings",[]) for r in c["rows"]]
    summary = dict(families=len(raw["results"]),
        non_skipped=sum("skip" not in r for r in raw["results"]),
        crossings=raw["crossing_count"], side_evaluations=len(side_rows),
        side_gates=sum(r["gates"] for r in side_rows),
        negative_complete=sum(mp.mpf(r["c3"])<0 for r in side_rows),
        admissible_center_evaluations=len(admissible),
        negative_base_gap=sum(mp.mpf(r["base_gap"])<0 for r in admissible),
        negative_kappa=sum(mp.mpf(r["kappa"])<0 for r in admissible),
        smallest_base_gaps=sorted(admissible,key=lambda r:mp.mpf(r["base_gap"]))[:8],
        smallest_r_shifts=sorted(admissible,key=lambda r:mp.mpf(r["r_minus_half_beta"]))[:4])
    with open("boundary-interrogation.json","w") as f:
        json.dump(dict(summary=summary,rows=rows),f,indent=2)
    print(json.dumps(summary,indent=2))
