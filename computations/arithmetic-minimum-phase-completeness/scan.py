"""Runpod experiment: test whether the actual projected balance identifies zeros."""
import os
for key in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import concurrent.futures
import json
import time
import platform
import mpmath as mp
import numpy as np
from remainder_kernel import values, mobius_table, MAX_P


def projected(sigma, height):
    s = mp.mpc(sigma, height)
    return mp.re(mp.zeta(s)/(s*(s+1)))


def task(index):
    mp.mp.dps = 55
    zero = mp.zetazero(index)
    t0 = mp.im(zero)
    p = np.arange(1, MAX_P+1, dtype=float)
    mu = mobius_table(MAX_P)[1:]
    records = []
    for endpoint in ("0.45", "0.55"):
        t = t0
        history = []
        try:
            for k in range(1, 6):
                sigma = mp.mpf("0.5")+(mp.mpf(endpoint)-mp.mpf("0.5"))*k/5
                old = t
                t = mp.findroot(lambda h: projected(sigma,h), (t-mp.mpf("0.001"),t+mp.mpf("0.001")),
                                solver="secant", tol=mp.mpf("1e-48"), maxsteps=80)
                slope = mp.diff(lambda h: projected(sigma,h), t)
                history.append({"sigma":str(sigma), "height":str(t),
                                "step":str(t-old), "height_derivative":str(slope)})
            s = mp.mpc(endpoint,t)
            zs = mp.zeta(s)
            u = mp.conj(s)
            balance = -1/(2*u*(1-u))-mp.conj(zs)/(u*(u+1))
            boundary = -1/(2*u*(1-u))
            wa = values(complex(s), complex(zs), 6, 10)
            wb = values(complex(s), complex(zs), 9, 14)
            bases = (mu*wb/(complex(u)*(complex(u)+1))).real
            x = p*bases
            y = p**(4*float(endpoint)-1)*bases
            wzero = values(complex(zero), complex(mp.zeta(zero)), 9,14)
            xzero = p*(mu*wzero/(complex(mp.conj(zero))*(complex(mp.conj(zero))+1))).real
            records.append({"zero_index":index,"sigma":endpoint,"reference_height":str(t0),
                            "height":str(t),"height_shift":str(t-t0),
                            "zeta":[str(mp.re(zs)),str(mp.im(zs))],"abs_zeta":str(abs(zs)),
                            "projected_residual":str(projected(mp.mpf(endpoint),t)),
                            "complex_residual_im":str(mp.im(balance-boundary)),
                            "min_X_index":int(np.argmin(x))+1,"min_Y_index":int(np.argmin(y))+1,
                            "reference_min_index":int(np.argmin(xzero))+1,
                            "min_X":float(np.min(x)),"min_Y":float(np.min(y)),
                            "W_head_order_drift":float(np.max(np.abs(wb-wa))),
                            "X_head_order_drift":float(np.max(np.abs(p*(mu*(wb-wa)/(complex(u)*(complex(u)+1))).real))),
                            "continuation":history})
        except Exception as exc:
            records.append({"zero_index":index,"sigma":endpoint,"error":repr(exc),"continuation":history})
    print("completed",index,flush=True)
    return records


if __name__ == "__main__":
    start=time.time()
    with concurrent.futures.ProcessPoolExecutor(max_workers=8) as pool:
        records=[row for group in pool.map(task,range(1,25)) for row in group]
    result={"note":"Approximate roots of a real projection, not zeta zeros or proof certificates.",
            "digits":55,"workers":8,"python":platform.python_version(),"mpmath":mp.__version__,
            "max_p":MAX_P,"seconds":time.time()-start,"results":records}
    with open("results.json","w") as out:
        json.dump(result,out,indent=2)
    successes=[r for r in records if "error" not in r]
    summary={"successes":len(successes),"failures":len(records)-len(successes),
             "matching_finite_XY_labels":sum(r["min_X_index"]==r["min_Y_index"] for r in successes),
             "matching_reference_X_labels":sum(r["min_X_index"]==r["reference_min_index"] for r in successes),
             "max_abs_projected_residual":str(max((abs(mp.mpf(r["projected_residual"])) for r in successes),default=0)),
             "min_abs_zeta":str(min((mp.mpf(r["abs_zeta"]) for r in successes),default=0)),
             "max_W_drift":max((r["W_head_order_drift"] for r in successes),default=0),
             "max_X_drift":max((r["X_head_order_drift"] for r in successes),default=0)}
    with open("summary.json","w") as out:
        json.dump(summary,out,indent=2)
    print(summary,flush=True)
