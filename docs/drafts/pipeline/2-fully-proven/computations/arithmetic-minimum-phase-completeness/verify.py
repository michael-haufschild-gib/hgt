"""Runpod-only independent bisection and high-precision remainder verification."""
import os
for key in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key]="1"
import concurrent.futures
import json
import mpmath as mp
from hurwitz_kernel import w_value


def task(row):
    mp.mp.dps=100
    sigma=mp.mpf(row["sigma"])
    t=mp.mpf(row["height"])
    def f(h):
        s=mp.mpc(sigma,h)
        return mp.re(mp.zeta(s)/(s*(s+1)))
    lo,hi=t-mp.mpf("0.00001"),t+mp.mpf("0.00001")
    flo,fhi=f(lo),f(hi)
    if not flo*fhi<0:
        return {"zero_index":row["zero_index"],"sigma":row["sigma"],"error":"No numerical sign-changing bracket"}
    initial=[str(flo),str(fhi)]
    for _ in range(300):
        mid=(lo+hi)/2
        fm=f(mid)
        if flo*fm<0:
            hi=mid
        else:
            lo,flo=mid,fm
    t=(lo+hi)/2
    s=mp.mpc(sigma,t)
    z=mp.zeta(s)
    p=row["min_X_index"]
    head=max(32,int(mp.ceil(4*abs(t)/p)))
    w1=w_value(s,p,head,12)
    w2=w_value(s,p,head+32,18)
    return {"zero_index":row["zero_index"],"sigma":row["sigma"],"height":str(t),
            "height_scan_discrepancy":str(abs(t-mp.mpf(row["height"]))),
            "initial_bracket_sign_values":initial,"final_bracket_width":str(hi-lo),
            "projected_residual":str(f(t)),"zeta":[str(mp.re(z)),str(mp.im(z))],
            "abs_zeta":str(abs(z)),"complex_residual_im":str(mp.im(z/(s*(s+1)))),
            "modulus":p,"W":[str(mp.re(w2)),str(mp.im(w2))],
            "W_head_order_drift":str(abs(w2-w1)),"heads":[head,head+32]}


if __name__=="__main__":
    mp.mp.dps=100
    data=json.load(open("results.json"))["results"]
    selected=[r for r in data if "error" not in r and
              ((r["zero_index"]==1) or (r["zero_index"] in (7,12,24) and r["sigma"]=="0.45"))]
    with concurrent.futures.ProcessPoolExecutor(max_workers=4) as pool:
        results=list(pool.map(task,selected))
    json.dump({"digits":100,"bisection_steps":300,"workers":4,"orders":[12,18],
               "note":"Independent numerical checks, not interval certificates or Lean inputs.",
               "results":results},open("verification.json","w"),indent=2)
    good=[r for r in data if "error" not in r]
    jumps=[{"zero_index":r["zero_index"],"sigma":r["sigma"],"height_shift":r["height_shift"]}
           for r in good if abs(mp.mpf(r["height_shift"]))>1 or
           any(abs(mp.mpf(h["step"]))>1 for h in r["continuation"])]
    local=[r for r in good if abs(mp.mpf(r["height_shift"]))<=1 and
           all(abs(mp.mpf(h["step"]))<=1 for h in r["continuation"])]
    analysis={"one_unit_jump_filter":"Post-scan diagnostic; not a certification of branch identity.",
              "converged_targets":len(good),"failed_targets":len(data)-len(good),
              "large_jump_warnings":jumps,"targets_without_large_jump":len(local),
              "distinct_converged_points_at_30_decimal_places":len({(r["sigma"],mp.nstr(mp.mpf(r["height"]),30)) for r in good}),
              "local_matching_XY":sum(r["min_X_index"]==r["min_Y_index"] for r in local),
              "local_matching_reference_X":sum(r["min_X_index"]==r["reference_min_index"] for r in local),
              "max_verified_projected_residual":str(max(abs(mp.mpf(r["projected_residual"])) for r in results)),
              "max_verified_W_drift":str(max(mp.mpf(r["W_head_order_drift"]) for r in results))}
    json.dump(analysis,open("analysis.json","w"),indent=2)
    print(json.dumps(analysis),flush=True)
