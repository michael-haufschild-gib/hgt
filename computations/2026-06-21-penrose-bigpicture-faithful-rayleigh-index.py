import numpy as np


def make_matrix(n, negative=-1e-3, positive=1.0, seed=0):
    rng = np.random.default_rng(seed)
    q, _ = np.linalg.qr(rng.normal(size=(n, n)))
    eigs = np.full(n, positive)
    eigs[0] = negative
    return q @ np.diag(eigs) @ q.T, eigs


def sample_min_rayleigh(a, samples, seed=1):
    rng = np.random.default_rng(seed)
    best = float("inf")
    hits = 0
    for _ in range(samples):
        x = rng.normal(size=a.shape[0])
        x /= np.linalg.norm(x)
        r = float(x @ a @ x)
        best = min(best, r)
        if r < 0:
            hits += 1
    return best, hits


print("Rayleigh quotient: measured trace vs faithful negative index")
for n in [10, 50, 200]:
    a, eigs = make_matrix(n)
    vals = np.linalg.eigvalsh(a)
    inertia = (int(np.sum(vals < -1e-12)), int(np.sum(np.abs(vals) <= 1e-12)), int(np.sum(vals > 1e-12)))
    trace = float(np.trace(a))
    mean = trace / n
    variance = float(np.mean((vals - mean) ** 2))
    best, hits = sample_min_rayleigh(a, samples=20_000, seed=n)
    print(
        f"n={n:3d} trace={trace:10.6f} mean={mean:9.6f} var={variance:10.8f} "
        f"lambda_min={vals[0]:+10.6f} inertia={inertia} "
        f"sample_min={best:+10.6f} negative_hits={hits}"
    )
