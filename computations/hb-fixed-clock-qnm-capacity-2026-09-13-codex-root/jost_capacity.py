import json
import math
import multiprocessing as mpool
import os
import time

os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")

import numpy as np


BETAS = (0.2, 0.5, 0.8)
GAMMAS = (14.134725141734695, 30.424876125859512, 49.7738324776723)
PER_BRANCH = (2, 4, 8, 16)
WINDOWS = (0.5, 1.0, 2.0, 4.0, 6.0)
RIDGES = np.logspace(-24, 2, 80)


def frequencies(beta, gamma, per_branch):
    plus = [gamma / 2 - 1j * (2 * n + 1 + beta / 2) for n in range(per_branch)]
    minus = [-gamma / 2 - 1j * (2 * n + 2 - beta / 2) for n in range(per_branch)]
    return np.asarray(plus + minus, dtype=np.complex128)


def response_matrix(t, omega):
    return np.exp(-1j * t[:, None] * omega[None, :])


def pareto_front(points):
    points = sorted(points, key=lambda p: (p["max_error"], p["l1"]))
    out = []
    best_l1 = float("inf")
    for p in points:
        if p["l1"] < best_l1:
            out.append(p)
            best_l1 = p["l1"]
    return out


def analyze(cfg):
    beta, gamma, per_branch, T = cfg
    omega = frequencies(beta, gamma, per_branch)
    t_train = np.linspace(0.0, T, 401)
    t_val = np.linspace(0.0, T, 2001)
    A = response_matrix(t_train, omega)
    Av = response_matrix(t_val, omega)
    y = -np.ones(len(t_train), dtype=np.complex128)
    U, s, Vh = np.linalg.svd(A, full_matrices=False)
    uy = U.conj().T.dot(y)
    candidates = []
    for lam in RIDGES:
        c = Vh.conj().T.dot((s / (s * s + lam)) * uy)
        rv = Av.dot(c) + 1.0
        candidates.append({
            "ridge": float(lam),
            "max_error": float(np.max(np.abs(rv))),
            "rms_error": float(np.sqrt(np.mean(np.abs(rv) ** 2))),
            "endpoint_error": float(abs(rv[-1])),
            "l1": float(np.sum(np.abs(c))),
            "l2": float(np.linalg.norm(c)),
        })
    # Truncated-SVD solutions add hard rank variants to the ridge frontier.
    for rcond in (1e-4, 1e-6, 1e-8, 1e-10, 1e-12, 1e-14):
        keep = s > rcond * s[0]
        c = Vh.conj().T[:, keep].dot(uy[keep] / s[keep])
        rv = Av.dot(c) + 1.0
        candidates.append({
            "rcond": rcond,
            "rank": int(np.sum(keep)),
            "max_error": float(np.max(np.abs(rv))),
            "rms_error": float(np.sqrt(np.mean(np.abs(rv) ** 2))),
            "endpoint_error": float(abs(rv[-1])),
            "l1": float(np.sum(np.abs(c))),
            "l2": float(np.linalg.norm(c)),
        })
    floor = min(-w.imag for w in omega)
    for p in candidates:
        p["endpoint_l1_lower_bound"] = float(max(0.0, 1.0 - p["endpoint_error"]) * math.exp(floor * T))
        p["bound_ratio"] = float(p["l1"] / p["endpoint_l1_lower_bound"]) if p["endpoint_l1_lower_bound"] > 0 else None
    feasible = {}
    for eps in (0.5, 0.2, 0.1, 0.05, 0.01):
        q = [p for p in candidates if p["max_error"] <= eps]
        feasible[str(eps)] = min(q, key=lambda p: p["l1"]) if q else None
    return {
        "beta": beta,
        "gamma": gamma,
        "per_branch": per_branch,
        "total_modes": 2 * per_branch,
        "T": T,
        "damping_floor": floor,
        "condition_number": float(s[0] / s[-1]) if s[-1] > 0 else None,
        "singular_min": float(s[-1]),
        "singular_max": float(s[0]),
        "best_max_error": min(candidates, key=lambda p: p["max_error"]),
        "feasible_min_l1": feasible,
        "pareto": pareto_front(candidates),
    }


def main():
    started = time.time()
    configs = [(b, g, m, T) for b in BETAS for g in GAMMAS for m in PER_BRANCH for T in WINDOWS]
    with mpool.Pool(processes=16) as pool:
        rows = pool.map(analyze, configs)
    summary = {}
    for beta in BETAS:
        rb = [r for r in rows if r["beta"] == beta]
        summary[str(beta)] = {
            "min_error_T6": min(r["best_max_error"]["max_error"] for r in rb if r["T"] == 6.0),
            "min_l1_for_error_0.1_T6": min(
                (r["feasible_min_l1"]["0.1"]["l1"] for r in rb if r["T"] == 6.0 and r["feasible_min_l1"]["0.1"]),
                default=None,
            ),
        }
    payload = {
        "target": "persistent normalized counterterm -1",
        "train_points": 401,
        "validation_points": 2001,
        "rows": rows,
        "summary": summary,
        "seconds": time.time() - started,
    }
    with open("jost-capacity.json", "w") as f:
        json.dump(payload, f, indent=2)


if __name__ == "__main__":
    main()
