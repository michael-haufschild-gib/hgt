"""Numerical search for spaced multi-band configurations hiding their pair-form energy.

Model (mean-spacing units): frequencies u_j with pairwise gaps >= D, amplitudes exp(alpha*delta_j*L),
S(alpha) = sum_j exp(alpha*delta_j*L) exp(2 pi i u_j alpha), alpha in [eta, 1-eta].
Hiding ratio H = max_alpha |S(alpha)|^2 / max_alpha DIAG(alpha), DIAG(alpha) = sum_j exp(2 alpha delta_j L).
Floors: single band, window length ell: H >= c exp(-2 ell delta L) (Montgomery-Vaughan window bound);
perfect hiding would be H ~ exp(-2 delta_top L (1-eta)).
Smooth max over an alpha grid minimised by L-BFGS with analytic gradients, restarts in parallel.
"""
import sys, json, time, math
import numpy as np
from scipy.optimize import minimize
from multiprocessing import Pool

L = 30.0
ETA = 0.1
NALPHA = 401
ALPHAS = np.linspace(ETA, 1 - ETA, NALPHA)
TEMP = 0.05

def build(structure):
    d = []
    for (delta, n) in structure:
        d += [delta] * n
    return np.array(d, dtype=float)

def softplus(g):
    return np.logaddexp(0.0, g)

def sigmoid(g):
    return 1.0 / (1.0 + np.exp(-g))

def positions(g, D):
    gaps = D + softplus(g)
    return np.concatenate([[0.0], np.cumsum(gaps)])

def objective(g, D, deltas, amp, alphas):
    u = positions(g, D)                       # N
    phase = 2 * np.pi * np.outer(u, alphas)   # N x A
    c = amp * np.cos(phase); s = amp * np.sin(phase)
    Sre = c.sum(0); Sim = s.sum(0)            # A
    E = Sre * Sre + Sim * Sim + 1e-300
    logE = np.log(E)
    z = logE / TEMP
    zmax = z.max()
    w = np.exp(z - zmax); Z = w.sum(); w /= Z
    obj = TEMP * (zmax + math.log(Z))
    # dE/du_j = 2 Re(conj(S) * 2 pi i alpha A_j e^{i phi_j}) = 4 pi alpha A_j (Sre*(-sin) ... ) computed directly:
    # conj(S) e^{i phi} = (Sre - i Sim)(cos + i sin) => real: Sre cos + Sim sin ; imag: Sre sin - Sim cos
    # Re(i * that) = -(Sre sin - Sim cos)
    dE_du = 4 * np.pi * alphas[None, :] * (-(Sre[None, :] * s - Sim[None, :] * c))   # N x A (amp already inside c,s)
    dlogE_du = dE_du / E[None, :]
    dobj_du = (dlogE_du * w[None, :]).sum(1)  # N
    # u_j = sum_{k<j} (D + softplus(g_k)) => d obj / d g_k = sigmoid(g_k) * sum_{j>k} dobj_du[j]
    suffix = np.cumsum(dobj_du[::-1])[::-1]   # suffix[j] = sum_{i>=j} dobj_du[i]
    grad = sigmoid(g) * suffix[1:]
    return obj, grad

def run_one(args):
    seed, structure, D, iters = args
    rng = np.random.default_rng(seed)
    deltas = build(structure)
    N = len(deltas)
    amp = np.exp(np.outer(deltas, ALPHAS) * L)                # N x A
    diag = (np.exp(2 * np.outer(deltas, ALPHAS) * L)).sum(0)
    diag_max = float(diag.max())
    # random spaced start: gaps D + Exp(1) -> g = log(expm1(x))
    x = rng.exponential(1.0, size=N - 1)
    g0 = np.log(np.expm1(x) + 1e-12)
    t0 = time.time()
    f0, _ = objective(g0, D, deltas, amp, ALPHAS)
    H0 = math.exp(f0) / diag_max
    res = minimize(objective, g0, args=(D, deltas, amp, ALPHAS), jac=True, method="L-BFGS-B",
                   options=dict(maxiter=iters, maxfun=iters * 2))
    g = res.x
    u = positions(g, D)
    phase = 2 * np.pi * np.outer(u, ALPHAS)
    Sre = (amp * np.cos(phase)).sum(0); Sim = (amp * np.sin(phase)).sum(0)
    E = Sre * Sre + Sim * Sim
    H = float(E.max()) / diag_max
    prof = [float(np.log10(max(E[i], 1e-300))) for i in range(0, NALPHA, 50)]
    return dict(seed=seed, N=N, H_start=H0, H=H, log10H=math.log10(max(H, 1e-300)),
                alpha_argmax=float(ALPHAS[int(np.argmax(E))]), profile_log10=prof,
                seconds=time.time() - t0, nit=int(res.nit))

if __name__ == "__main__":
    D = float(sys.argv[1]) if len(sys.argv) > 1 else 2.0
    restarts = int(sys.argv[2]) if len(sys.argv) > 2 else 16
    iters = int(sys.argv[3]) if len(sys.argv) > 3 else 400
    structures = {
        "single_band": [(0.30, 400)],
        "two_bands": [(0.20, 400), (0.30, 60)],
        "ladder_4": [(0.15, 800), (0.20, 300), (0.25, 110), (0.30, 40)],
        "ladder_8": [(0.15, 800), (0.17, 500), (0.19, 320), (0.21, 200), (0.23, 130), (0.25, 80), (0.27, 50), (0.30, 30)],
    }
    out = {"L": L, "eta": ETA, "D": D, "restarts": restarts, "iters": iters, "temp": TEMP, "structures": {}}
    for name, structure in structures.items():
        deltas = build(structure)
        dtop = float(deltas.max())
        ell = 1.0 / D + 0.05
        floors = {"single_window_floor_log10": math.log10(math.exp(-2 * ell * dtop * L)),
                  "perfect_hiding_log10": math.log10(math.exp(-2 * dtop * L * (1 - ETA)))}
        args = [(s, structure, D, iters) for s in range(restarts)]
        with Pool(min(restarts, 48)) as pool:
            res = pool.map(run_one, args)
        best = min(res, key=lambda r: r["H"])
        out["structures"][name] = {"structure": structure, "floors": floors, "best": best,
                                   "all_log10H": sorted(r["log10H"] for r in res)}
        print(name, "best log10 H =", round(best["log10H"], 3), "start", round(math.log10(best["H_start"]), 3),
              "floors", {k: round(v, 3) for k, v in floors.items()}, "sec", round(best["seconds"], 1), flush=True)
    with open("ladder_results_D%g.json" % D, "w") as f:
        json.dump(out, f, indent=1)
