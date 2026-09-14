import json
import os

os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")

import mpmath as mp
import numpy as np


BETA = 0.5
GAMMA = 14.134725141734695
PER_BRANCH = 16
T = 2.0
RCOND = 1e-14


def frequencies_np():
    plus = [GAMMA / 2 - 1j * (2 * n + 1 + BETA / 2) for n in range(PER_BRANCH)]
    minus = [-GAMMA / 2 - 1j * (2 * n + 2 - BETA / 2) for n in range(PER_BRANCH)]
    return np.asarray(plus + minus, dtype=np.complex128)


def main():
    omega = frequencies_np()
    train = np.linspace(0.0, T, 401)
    A = np.exp(-1j * train[:, None] * omega[None, :])
    y = -np.ones(len(train), dtype=np.complex128)
    U, s, Vh = np.linalg.svd(A, full_matrices=False)
    keep = s > RCOND * s[0]
    c = Vh.conj().T[:, keep].dot((U.conj().T.dot(y))[keep] / s[keep])

    mp.mp.dps = 80
    om = [mp.mpc(w.real, w.imag) for w in omega]
    cm = [mp.mpc(x.real, x.imag) for x in c]
    grid = [mp.mpf(k) * T / 400 for k in range(401)]

    def residual(coeff, t):
        return 1 + mp.fsum(coeff[j] * mp.exp(-mp.j * om[j] * t) for j in range(len(om)))

    base_values = [abs(residual(cm, t)) for t in grid]
    rng = np.random.RandomState(20260913)
    direction = rng.normal(size=len(c)) + 1j * rng.normal(size=len(c))
    direction = direction / np.linalg.norm(direction) * np.linalg.norm(c)
    perturb = {}
    for eps in (1e-14, 1e-12, 1e-10):
        cp = c + eps * direction
        cmp = [mp.mpc(x.real, x.imag) for x in cp]
        vals = [abs(residual(cmp, t)) for t in grid]
        perturb[str(eps)] = {
            "max_error": mp.nstr(max(vals), 25),
            "rms_error": mp.nstr(mp.sqrt(mp.fsum(v * v for v in vals) / len(vals)), 25),
        }

    moments = []
    for k in range(13):
        target = -1 if k == 0 else 0
        val = mp.fsum(cm[j] * (-mp.j * om[j]) ** k for j in range(len(om))) - target
        scale = max(mp.mpf(1), mp.fsum(abs(cm[j] * (-mp.j * om[j]) ** k) for j in range(len(om))))
        moments.append({
            "order": k,
            "absolute_residual": mp.nstr(abs(val), 25),
            "relative_to_term_budget": mp.nstr(abs(val) / scale, 25),
        })

    out = {
        "beta": BETA,
        "gamma": GAMMA,
        "per_branch": PER_BRANCH,
        "T": T,
        "rcond": RCOND,
        "retained_rank": int(np.sum(keep)),
        "coefficient_l1": mp.nstr(sum(abs(x) for x in cm), 25),
        "coefficient_l2": mp.nstr(mp.sqrt(sum(abs(x) ** 2 for x in cm)), 25),
        "high_precision_grid": {
            "points": len(grid),
            "max_error": mp.nstr(max(base_values), 25),
            "rms_error": mp.nstr(mp.sqrt(mp.fsum(v * v for v in base_values) / len(base_values)), 25),
            "endpoint_error": mp.nstr(base_values[-1], 25),
        },
        "relative_coefficient_perturbations": perturb,
        "moment_cancellations": moments,
    }
    with open("jost-validation.json", "w") as f:
        json.dump(out, f, indent=2)


if __name__ == "__main__":
    main()
