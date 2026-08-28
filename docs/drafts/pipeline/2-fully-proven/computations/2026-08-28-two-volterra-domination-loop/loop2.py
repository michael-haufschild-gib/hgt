"""Cycle-5 battery: slice contraction law, Laguerre hierarchy coefficients, Lehmer dip.

Objects: xic(w) = xi(1/2+w); Xi(tau) = xic(i tau) real; tilt_pm = xic' +- c xic;
lambda_c = tilt-/tilt+; exact law: 1-|lambda_c|^2 = 4c Re(xic' conj xic)/|tilt+|^2;
Re(xic' conj xic)(sigma+i tau) = (1/2) d/dsigma |xic|^2 and |xic(sigma+i tau)|^2 = |Xi(tau - i sigma)|^2.
Predicted expansion: |xic(s+it)|^2 = Xi^2 + s^2 L1 + s^4 L2/12 + O(s^6),
L1 = Xi'^2 - Xi Xi'', L2 = Xi Xi'''' - 4 Xi' Xi''' + 3 Xi''^2.
"""
import json, sys, time
from multiprocessing import Pool
import mpmath as mp

NPROC = 100
DPS = 30

def xifn(s):
    return mp.mpf('0.5')*s*(s-1)*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)

def xic(w):
    return xifn(mp.mpf('0.5') + w)

def dxic(w, k=1, h=None):
    if h is None: h = mp.mpf(10)**(-(mp.mp.dps//3))
    if k == 1:
        return (8*(xic(w+h)-xic(w-h)) - (xic(w+2*h)-xic(w-2*h)))/(12*h)
    raise ValueError

def Xi_jets(tau, order=4):
    """Xi and tau-derivatives via central differences at dps precision."""
    h = mp.mpf(10)**(-(mp.mp.dps//4))
    vals = [xic(mp.mpc(0, tau + k*h)).real for k in range(-3, 4)]
    Xi = vals[3]
    d1 = (vals[4]-vals[2])/(2*h) - 0  # refine below with 5-pt
    d1 = (8*(vals[4]-vals[2]) - (vals[5]-vals[1]))/(12*h)
    d2 = (16*(vals[4]+vals[2]) - (vals[5]+vals[1]) - 30*vals[3])/(12*h**2)
    d3 = ((vals[5]-vals[1]) - 2*(vals[4]-vals[2]))/(2*h**3)
    d4 = ((vals[5]+vals[1]) - 4*(vals[4]+vals[2]) + 6*vals[3])/(h**4)
    return Xi, d1, d2, d3, d4

def task_L(args):
    tau, = args
    mp.mp.dps = DPS
    try:
        Xi, d1, d2, d3, d4 = Xi_jets(tau)
        L1 = d1*d1 - Xi*d2
        L2 = Xi*d4 - 4*d1*d3 + 3*d2*d2
        return {"tau": float(tau), "Xi": float(Xi), "L1": float(L1), "L2": float(L2)}
    except Exception as e:
        return {"tau": float(tau), "error": repr(e)}

def task_slice(args):
    tau, eps, c = args
    mp.mp.dps = DPS
    try:
        w = mp.mpc(eps, tau)
        f = xic(w); d = dxic(w)
        tp = d + c*f; tm = d - c*f
        one_minus = 1 - (mp.fabs(tm)/mp.fabs(tp))**2
        # first-order prediction from wall jets
        Xi, d1, d2, d3, d4 = Xi_jets(tau)
        L1 = d1*d1 - Xi*d2
        L2 = Xi*d4 - 4*d1*d3 + 3*d2*d2
        tp0sq = d1*d1 + c*c*Xi*Xi   # |tilt+(i tau)|^2 = Xi'^2 + c^2 Xi^2
        pred1 = 4*c*eps*L1/tp0sq if tp0sq > 0 else None
        # exact u = Re(xic' conj xic) on the slice, and Jensen expansion check
        u = (d*mp.conj(f)).real
        u_pred = eps*L1 + eps**3*L2/3  # u = (1/2) d/ds |xic|^2 = s L1 + s^3 L2/3 + ...
        return {"tau": float(tau), "eps": float(eps), "c": float(c),
                "one_minus": float(one_minus),
                "pred1": float(pred1) if pred1 is not None else None,
                "u": float(u), "u_pred": float(u_pred),
                "neg": bool(one_minus < 0)}
    except Exception as e:
        return {"tau": float(tau), "eps": float(eps), "c": float(c), "error": repr(e)}

def main():
    t0 = time.time()
    # 1. L1/L2 profile on [0.2, 120]
    taus = [mp.mpf(2)/10 + mp.mpf(k)*mp.mpf('0.05') for k in range(0, 2397)]
    with Pool(NPROC) as pool:
        recs = pool.map(task_L, [(float(t),) for t in taus], chunksize=16)
    good = [r for r in recs if "error" not in r]
    minL1 = min(good, key=lambda r: r["L1"])
    minL2 = min(good, key=lambda r: r["L2"])
    negL1 = [r for r in good if r["L1"] < 0]
    negL2 = [r for r in good if r["L2"] < 0]
    print(f"[{time.time()-t0:.0f}s] L-profile n={len(good)}; min L1 = {minL1['L1']:.6e} at tau={minL1['tau']:.2f};"
          f" min L2 = {minL2['L2']:.6e} at tau={minL2['tau']:.2f}; negL1={len(negL1)} negL2={len(negL2)}", flush=True)
    json.dump({"minL1": minL1, "minL2": minL2, "negL1": len(negL1), "negL2": len(negL2)},
              open("/root/precert/loop2_L.json", "w"))

    # 2. Lehmer window near tau ~ 7005.06/7005.10
    lt = [7004.8 + 0.002*k for k in range(0, 351)]
    with Pool(NPROC) as pool:
        lrecs = pool.map(task_L, [(t,) for t in lt], chunksize=2)
    lgood = [r for r in lrecs if "error" not in r]
    lmin = min(lgood, key=lambda r: r["L1"])
    print(f"[{time.time()-t0:.0f}s] Lehmer window: min L1 = {lmin['L1']:.6e} at tau={lmin['tau']:.4f};"
          f" ref scale: L1(7004.8)={lgood[0]['L1']:.4e}", flush=True)
    json.dump(lgood, open("/root/precert/loop2_lehmer.json", "w"))

    # 3. slice law + contraction check
    tasks = []
    for c in (0.5, 2.0, 10.0):
        for eps in (0.02, 0.05, 0.1, 0.2, 0.45):
            for k in range(0, 121):
                tasks.append((0.25 + 0.5*k, eps, c))
    with Pool(NPROC) as pool:
        srecs = pool.map(task_slice, tasks, chunksize=8)
    sgood = [r for r in srecs if "error" not in r]
    neg = [r for r in sgood if r["neg"]]
    # law accuracy at smallest eps
    small = [r for r in sgood if r["eps"] == 0.02 and abs(r["u"]) > 1e-300]
    relerr1 = max(abs(r["u"] - r["u_pred"])/(abs(r["u"])) for r in small)
    tight = min(sgood, key=lambda r: r["one_minus"])
    print(f"[{time.time()-t0:.0f}s] slices n={len(sgood)}; negatives={len(neg)};"
          f" max rel err of u vs (eps L1 + eps^3 L2/3) at eps=0.02: {relerr1:.3e};"
          f" tightest 1-|lam|^2 = {tight['one_minus']:.6e} at tau={tight['tau']}, eps={tight['eps']}, c={tight['c']}", flush=True)
    json.dump({"n": len(sgood), "negatives": len(neg), "relerr_small_eps": relerr1,
               "tightest": tight}, open("/root/precert/loop2_slice.json", "w"))
    for r in neg[:5]:
        print("NEGATIVE:", json.dumps(r))
    print("DONE", time.time()-t0)

if __name__ == "__main__":
    main()
