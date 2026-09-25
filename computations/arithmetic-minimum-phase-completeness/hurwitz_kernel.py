"""Runpod-only independent Hurwitz-tail checks of selected minimum witnesses."""
import os
for key in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import concurrent.futures
import json
import mpmath as mp


def w_value(s, p, head, order):
    u = mp.conj(s)
    a = 2*mp.re(s)
    total = mp.mpc(0)
    for n in range(1, head+1):
        x = mp.mpf(p*n)
        r = -mp.zeta(u, x+1)-x**(1-u)/(1-u)-x**(-u)/2
        total += mp.mpf(n)**(-s)*r
    total *= mp.mpf(p)**(1-s)
    for k in range(1, order+1):
        coefficient = -mp.bernoulli(2*k)*mp.rf(u, 2*k-1)/mp.factorial(2*k)
        total += coefficient*mp.mpf(p)**(2-a-2*k)*mp.zeta(a+2*k-1, head+1)
    return total


def task(row):
    mp.mp.dps = 75
    s = mp.zetazero(row["zero_index"])
    p = row["min_X_index"]
    mu = row["rows"][p-1][1]
    head = max(32, int(mp.ceil(4*mp.im(s)/p)))
    w1 = w_value(s, p, head, 12)
    w2 = w_value(s, p, head+32, 18)
    u = mp.conj(s)
    x = p*mu*mp.re(w2/(u*(u+1)))
    c = mp.zeta(2)/12*mp.re(1/(u+1))
    return {"zero_index": row["zero_index"], "p": p, "mu": mu,
            "height": str(mp.im(s)), "X": str(x), "tail_lower_boundary": str(-c),
            "gap": str(x+c), "W": [str(mp.re(w2)),str(mp.im(w2))],
            "W_head_order_drift": str(abs(w2-w1)),
            "scan_X_discrepancy": str(abs(x-mp.mpf(row["min_X"]))),
            "zeta_residual": str(abs(mp.zeta(s))), "heads": [head,head+32]}


if __name__ == "__main__":
    with open("results.json") as source:
        data = json.load(source)
    selected = [r for r in data["results"] if r["sigma"] == 0.5 and r["zero_index"] in [1,12,49,81]]
    with concurrent.futures.ProcessPoolExecutor(max_workers=4) as pool:
        result = list(pool.map(task,selected))
    with open("verification.json","w") as out:
        json.dump({"digits":75,"orders":[12,18],"workers":4,
                   "note":"Independent high-precision diagnostics; no rigorous interval certificate.",
                   "results":result},out,indent=2)
    for row in result:
        print(row["zero_index"],row["p"],row["gap"],row["W_head_order_drift"],flush=True)
