import numpy as np


def inertia_from_eigs(eigs, tol=1e-12):
    vals = np.array(eigs, dtype=float)
    return (
        int(np.sum(vals < -tol)),
        int(np.sum(np.abs(vals) <= tol)),
        int(np.sum(vals > tol)),
    )


families = [
    ("all positive", [1.0, 1.0, 1.0, 1.0]),
    ("one tiny negative, positive mean", [-1e-6, 1.0, 1.0, 1.0]),
    ("one large negative, zero trace", [-3.0, 1.0, 1.0, 1.0]),
    ("zero minimum, positive mean", [0.0, 1.0, 1.0, 1.0]),
    ("two signed directions, positive mean", [-0.1, -0.1, 1.0, 1.0]),
]

print("Nearby false statements for Rayleigh/faithful-index positivity")
print("statement A: positive trace implies positive definite")
print("statement B: positive mean plus small variance implies positive definite")
print("statement C: nonnegative Rayleigh minimum implies no negative index")
for name, eigs in families:
    vals = np.array(eigs, dtype=float)
    trace = float(vals.sum())
    mean = float(vals.mean())
    variance = float(np.mean((vals - mean) ** 2))
    lam_min = float(vals.min())
    inertia = inertia_from_eigs(vals)
    print(
        f"{name:38s} trace={trace:+9.6f} mean={mean:+9.6f} "
        f"var={variance:10.8f} min={lam_min:+10.6f} inertia={inertia}"
    )
