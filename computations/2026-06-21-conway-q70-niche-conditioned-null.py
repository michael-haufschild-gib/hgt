import math
import numpy as np
import mpmath as mp


def first_primes(n):
    primes = []
    candidate = 2
    while len(primes) < n:
        ok = True
        for p in primes:
            if p * p > candidate:
                break
            if candidate % p == 0:
                ok = False
                break
        if ok:
            primes.append(candidate)
        candidate += 1 if candidate == 2 else 2
    return tuple(primes)


def gamma_part(s):
    return complex(-0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0))


def dlog_zeta(s, h=1e-4):
    z0 = mp.fp.zeta(s)
    return complex((mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300)))


def dlog_finite(s, primes):
    out = 0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def phase_defect(g, p):
    d = math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300)
    return max(0.0, d)


def node_niche(seed=20260621):
    rng = np.random.default_rng(seed)
    n_niches = 80
    cells_per = 30
    niche = rng.normal(size=n_niches)
    # No intrinsic cell fate difference: all cells in one niche share the same
    # external probability shift.
    probs = 1 / (1 + np.exp(-(1.6 * niche)))
    events = []
    labels = []
    for i, p in enumerate(probs):
        x = rng.random(cells_per) < p
        events.append(x.astype(float))
        labels.extend([i] * cells_per)
    y = np.concatenate(events)
    # Raw overdispersion of clone/niche means vs Bernoulli baseline.
    niche_means = np.array([e.mean() for e in events])
    raw_var = float(np.var(niche_means))
    shuffled = []
    for _ in range(200):
        ys = y.copy()
        rng.shuffle(ys)
        shuffled.append(np.var([ys[i * cells_per : (i + 1) * cells_per].mean() for i in range(n_niches)]))
    return raw_var, float(np.mean(shuffled)), float(raw_var / np.mean(shuffled))


def component(kind, s, primes, rng):
    if kind == "true":
        return dlog_zeta(s)
    if kind == "finite":
        return dlog_finite(s, primes)
    if kind == "random":
        base = dlog_zeta(s)
        theta = rng.uniform(-math.pi, math.pi)
        return abs(base) * complex(math.cos(theta), math.sin(theta))
    raise ValueError(kind)


def field(kind, sigmas, ts, primes, seed):
    rng = np.random.default_rng(seed)
    mat = np.zeros((len(sigmas), len(ts)))
    for i, sigma in enumerate(sigmas):
        for j, t in enumerate(ts):
            s = complex(float(sigma), float(t))
            mat[i, j] = phase_defect(gamma_part(s), component(kind, s, primes, rng))
    return mat


def event_matrix(mat, q=0.70):
    # q70 per-lane threshold; event means lane-specific high phase-defect.
    out = np.zeros_like(mat, dtype=bool)
    for i in range(mat.shape[0]):
        out[i] = mat[i] >= np.quantile(mat[i], q)
    return out


def top_eig(events):
    x = events.astype(float)
    x = x - x.mean(axis=1, keepdims=True)
    cov = x @ x.T / max(1, x.shape[1] - 1)
    np.fill_diagonal(cov, 0.0)
    vals = np.linalg.eigvalsh(cov)
    return float(vals[-1])


def time_count_null(events, trials=300, seed=0):
    rng = np.random.default_rng(seed)
    n_lanes, n_t = events.shape
    counts = events.sum(axis=0).astype(int)
    vals = []
    for _ in range(trials):
        fake = np.zeros_like(events, dtype=bool)
        for j, c in enumerate(counts):
            if c:
                idx = rng.choice(n_lanes, size=c, replace=False)
                fake[idx, j] = True
        vals.append(top_eig(fake))
    return float(np.mean(vals)), float(np.quantile(vals, 0.95))


def main():
    print("NODE: extrinsic niche variation can be mistaken for intrinsic stochastic fate choice")
    raw, shuf, ratio = node_niche()
    print("NODE_ROW", f"raw_niche_var={raw:.5f}", f"shuffled_var={shuf:.5f}", f"raw_over_shuffle={ratio:.2f}")
    print()
    print("TRANSFER: ResearchNode 23 q70 association gate")
    print("method #23 classify boundary cases: raw q70 association vs time-count-conditioned niche null")
    primes = first_primes(120)
    sigmas = np.linspace(0.2, 0.9, 9)
    windows = [(100.0, 170.0), (500.0, 570.0), (900.0, 970.0)]
    for kind in ["true", "finite", "random"]:
        for window in windows:
            ts = np.linspace(window[0], window[1], 180)
            mat = field(kind, sigmas, ts, primes, seed=20260621 + int(window[0]) + len(kind))
            ev = event_matrix(mat, q=0.70)
            raw_e = top_eig(ev)
            null_mean, null_q95 = time_count_null(ev, seed=3030 + int(window[0]) + len(kind))
            print(
                "ROW",
                kind,
                f"window={window}",
                f"raw_top={raw_e:.5f}",
                f"niche_null_mean={null_mean:.5f}",
                f"niche_null_q95={null_q95:.5f}",
                f"excess={raw_e - null_mean:+.5f}",
                f"above_q95={int(raw_e > null_q95)}",
                f"mean_active_lanes={ev.sum(axis=0).mean():.3f}",
            )


if __name__ == "__main__":
    main()
