import json
import numpy as np

from clock_atlas import CHANNELS, OVERTONES, quadrature


CASES = (
    ("zeta1", 0.5, 14.134725141734695),
    ("zeta10", 0.5, 49.7738324776723),
    ("mid9", 0.5, 48.889491679419734),
    ("tilt_low_zeta10", 0.2, 49.7738324776723),
    ("tilt_high_zeta10", 0.8, 49.7738324776723),
)


def transform(zs, order):
    x, w = quadrature(order)
    zs = np.asarray(zs, dtype=np.complex128)
    return np.cosh(zs[:, None] * x[None, :]).dot(w)


def coherence(zs, order):
    zs = np.asarray(zs, dtype=np.complex128)
    return np.abs(transform(zs, order)) / np.real(transform(zs.real.astype(np.complex128), order))


rows = []
for label, beta, gamma in CASES:
    rho = beta + 1j * gamma
    base = np.asarray([a * rho + b + 2 * n for _, a, b in CHANNELS for n in OVERTONES])
    for L in (1.0, 3.0):
        c320 = coherence(L * base, 320)
        c640 = coherence(L * base, 640)
        rows.append({
            "label": label,
            "beta": beta,
            "gamma": gamma,
            "L": L,
            "order320": {"min": float(c320.min()), "median": float(np.median(c320)), "max": float(c320.max())},
            "order640": {"min": float(c640.min()), "median": float(np.median(c640)), "max": float(c640.max())},
            "max_absolute_difference": float(np.max(np.abs(c320 - c640))),
            "max_relative_difference_above_1e-14": float(np.max(np.abs(c320 - c640) / np.maximum(c640, 1e-14))),
        })

with open("clock-crosscheck.json", "w") as f:
    json.dump(rows, f, indent=2)
