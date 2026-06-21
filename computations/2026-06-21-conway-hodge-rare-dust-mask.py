import numpy as np


def trial(n=400, alpha=2.0, probes=20000, seed=20260621):
    rng = np.random.default_rng(seed)
    # Krein/Hodge toy: one negative direction in a large positive space.
    # Eigenvalues: -alpha, 1, ..., 1.
    eigs = np.ones(n)
    eigs[0] = -alpha
    trace_mean = float(np.mean(eigs))
    kappa_minus = int(np.sum(eigs < 0))
    hits = 0
    mins = []
    for _ in range(probes):
        x = rng.normal(size=n)
        x /= np.linalg.norm(x)
        q = float(np.sum(eigs * x * x))
        hits += q < 0
        mins.append(q)
    return {
        "n": n,
        "alpha": alpha,
        "trace_mean": trace_mean,
        "kappa_minus": kappa_minus,
        "random_negative_rate": hits / probes,
        "min_probe": float(np.min(mins)),
        "q01": float(np.quantile(mins, 0.01)),
    }


def main():
    print("NODE: bulk tissue signals can mask rare but important subpopulations")
    print("ResearchNode 39: Hilbert-Polya/Hodge/F1 route")
    print("method #3 reverse: one rare negative direction does not force bulk negativity")
    for n in [50, 200, 1000]:
        for alpha in [0.5, 2.0, 10.0]:
            row = trial(n=n, alpha=alpha, probes=12000, seed=20260621 + n + int(alpha * 10))
            print(
                "ROW",
                f"n={row['n']}",
                f"alpha={row['alpha']}",
                f"trace_mean={row['trace_mean']:+.4f}",
                f"kappa_minus={row['kappa_minus']}",
                f"random_negative_rate={row['random_negative_rate']:.5f}",
                f"min_probe={row['min_probe']:+.4f}",
                f"q01={row['q01']:+.4f}",
            )
    print("VERDICT: bulk positivity/random probes are not faithful; only inertia/index sees the rare direction.")


if __name__ == "__main__":
    main()
