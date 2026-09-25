"""Cycle-5 battery, corrected: dps 60, h = 1e-6 stencils, log-safe normalized records."""
import json, time
from multiprocessing import Pool
import mpmath as mp

NPROC = 100
DPS = 60

def xifn(s):
    return mp.mpf('0.5')*s*(s-1)*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)

def xic(w):
    return xifn(mp.mpf('0.5') + w)

def Xi_jets(tau):
    h = mp.mpf(10)**(-6)
    v = [xic(mp.mpc(0, tau + k*h)).real for k in range(-3, 4)]
    Xi = v[3]
    d1 = (45*(v[4]-v[2]) - 9*(v[5]-v[1]) + (v[6]-v[0]))/(60*h)
    d2 = (270*(v[4]+v[2]) - 27*(v[5]+v[1]) + 2*(v[6]+v[0]) - 490*v[3])/(180*h**2)
    d3 = (-13*(v[4]-v[2]) + 8*(v[5]-v[1]) - (v[6]-v[0]))/(8*h**3)
    d4 = (-39*(v[4]+v[2]) + 12*(v[5]+v[1]) - (v[6]+v[0]) + 56*v[3])/(6*h**4)
    return Xi, d1, d2, d3, d4

def nrm(x, scale):
    return float(x/scale) if scale > 0 else None

def task_L(args):
    tau, = args
    mp.mp.dps = DPS
    try:
        Xi, d1, d2, d3, d4 = Xi_jets(tau)
        L1 = d1*d1 - Xi*d2
        L2 = Xi*d4 - 4*d1*d3 + 3*d2*d2
        s1 = d1*d1 + Xi*Xi + abs(Xi*d2)      # scale for L1
        s2 = 3*d2*d2 + abs(Xi*d4) + 4*abs(d1*d3)
        return {"tau": float(tau), "L1n": nrm(L1, s1), "L2n": nrm(L2, s2),
                "L1neg": bool(L1 < 0), "L2neg": bool(L2 < 0)}
    except Exception as e:
        return {"tau": float(tau), "error": repr(e)}

def main():
    t0 = time.time()
    taus = [0.2 + 0.05*k for k in range(0, 2397)]
    with Pool(NPROC) as pool:
        recs = pool.map(task_L, [(t,) for t in taus], chunksize=16)
    good = [r for r in recs if "error" not in r]
    n1 = [r for r in good if r["L1neg"]]; n2 = [r for r in good if r["L2neg"]]
    m1 = min(good, key=lambda r: r["L1n"]); m2 = min(good, key=lambda r: r["L2n"])
    print(f"[{time.time()-t0:.0f}s] [0.2,120]: negL1={len(n1)} negL2={len(n2)};"
          f" min normalized L1={m1['L1n']:.4e} at {m1['tau']:.2f};"
          f" min normalized L2={m2['L2n']:.4e} at {m2['tau']:.2f}", flush=True)

    # Lehmer window (normalized dip)
    lt = [7004.9 + 0.001*k for k in range(0, 301)]
    with Pool(NPROC) as pool:
        lrecs = pool.map(task_L, [(t,) for t in lt], chunksize=2)
    lgood = [r for r in lrecs if "error" not in r]
    ln1 = [r for r in lgood if r["L1neg"]]
    lm = min(lgood, key=lambda r: r["L1n"])
    base = [r for r in lgood if abs(r["tau"] - 7004.95) < 0.011]
    print(f"[{time.time()-t0:.0f}s] Lehmer: negL1={len(ln1)}; min normalized L1={lm['L1n']:.4e}"
          f" at tau={lm['tau']:.4f}; reference L1n at 7004.95 ~ {base[0]['L1n']:.4e}", flush=True)
    json.dump({"range": {"negL1": len(n1), "negL2": len(n2), "minL1n": m1, "minL2n": m2},
               "lehmer": {"neg": len(ln1), "min": lm}},
              open("/root/precert/loop2b.json", "w"))

    # slice-law verification at dps 60 (u vs eps L1 + eps^3 L2/3), small sample
    def slice_check(args):
        tau, eps = args
        mp.mp.dps = DPS
        w = mp.mpc(eps, tau)
        h = mp.mpf(10)**(-10)
        d = (8*(xic(w+h)-xic(w-h)) - (xic(w+2*h)-xic(w-2*h)))/(12*h)
        f = xic(w)
        u = (d*mp.conj(f)).real
        Xi, d1, d2, d3, d4 = Xi_jets(tau)
        L1 = d1*d1 - Xi*d2; L2 = Xi*d4 - 4*d1*d3 + 3*d2*d2
        up = eps*L1 + eps**3*L2/3
        return float(abs(u - up)/abs(u)) if u != 0 else None
    pts = [(2.0 + 3.7*k, 0.02) for k in range(15)] + [(2.0 + 3.7*k, 0.05) for k in range(15)]
    with Pool(NPROC) as pool:
        errs = pool.map(slice_check, pts, chunksize=1)
    errs = [e for e in errs if e is not None]
    print(f"[{time.time()-t0:.0f}s] slice law rel err: max {max(errs):.3e} at eps<=0.05 "
          f"(expect O(eps^4) ~ {0.05**4:.1e})", flush=True)
    print("DONE", time.time()-t0)

if __name__ == "__main__":
    main()
