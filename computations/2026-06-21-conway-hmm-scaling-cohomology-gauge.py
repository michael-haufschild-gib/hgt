import math
import numpy as np
import mpmath as mp


mp.mp.dps = 50


def node_hmm_scaling(n=9000):
    trans = np.array([[0.997, 0.003], [0.02, 0.98]], dtype=float)
    emit = np.array([[0.94, 0.06], [0.18, 0.82]], dtype=float)
    obs = np.zeros(n, dtype=int)
    for start, width in [(350, 80), (900, 70), (1200, 15), (2100, 130), (4200, 60), (7100, 90)]:
        obs[start : start + width] = 1
    raw = np.array([0.5, 0.5], dtype=float)
    scaled = raw.copy()
    scales = []
    raw_zero_at = None
    for t, y in enumerate(obs):
        raw = raw @ trans * emit[:, y]
        scaled = scaled @ trans * emit[:, y]
        c = scaled.sum()
        scales.append(c)
        scaled = scaled / c
        if raw_zero_at is None and raw.sum() == 0:
            raw_zero_at = t
    # Apply a second arbitrary positive scaling gauge to the normalized alphas.
    gauge = np.exp(0.25 + 0.7 * np.sin(np.linspace(0, 8 * math.pi, n)))
    scaled2 = np.array([0.5, 0.5], dtype=float)
    max_posterior_diff = 0.0
    loglike = 0.0
    loglike_gauge = 0.0
    for t, y in enumerate(obs):
        scaled2 = scaled2 @ trans * emit[:, y]
        c = scaled2.sum()
        posterior = scaled2 / c
        posterior_gauge = (gauge[t] * scaled2) / (gauge[t] * c)
        max_posterior_diff = max(max_posterior_diff, float(np.max(np.abs(posterior - posterior_gauge))))
        loglike += math.log(c)
        loglike_gauge += math.log(gauge[t] * c)
        scaled2 = posterior
    return raw.sum(), raw_zero_at, sum(math.log(c) for c in scales), loglike_gauge - loglike, max_posterior_diff


def xi_log_deriv(s):
    s = mp.mpc(s)
    return (
        1 / s
        + 1 / (s - 1)
        - mp.log(mp.pi) / 2
        + mp.digamma(s / 2) / 2
        + mp.diff(mp.zeta, s) / mp.zeta(s)
    )


def boundary(rect, n):
    a, b, t0, t1 = rect
    pts = []
    for k in range(n):
        u = k / n
        pts.append(mp.mpc(a + (b - a) * u, t0))
    for k in range(n):
        u = k / n
        pts.append(mp.mpc(b, t0 + (t1 - t0) * u))
    for k in range(n):
        u = k / n
        pts.append(mp.mpc(b - (b - a) * u, t1))
    for k in range(n):
        u = k / n
        pts.append(mp.mpc(a, t1 - (t1 - t0) * u))
    pts.append(pts[0])
    return pts


def gauge_deriv(s, lam, mu):
    # d/ds of phi(s)=lam*s+mu*s^2, an exact analytic gauge.
    return lam + 2 * mu * s


def loop_stats(rect, n, lam=0, mu=0):
    pts = boundary(rect, n)
    integral = mp.mpc(0)
    energy = mp.mpf("0")
    max_abs = mp.mpf("0")
    for z0, z1 in zip(pts, pts[1:]):
        mid = (z0 + z1) / 2
        h = xi_log_deriv(mid) + gauge_deriv(mid, lam, mu)
        dz = z1 - z0
        integral += h * dz
        energy += abs(h) * abs(dz)
        max_abs = max(max_abs, abs(h))
    return integral / (2j * mp.pi), energy, max_abs


def main():
    print("NODE: HMM forward/backward scaling/log-space underflow")
    raw_sum, raw_zero_at, loglike, gauge_shift, postdiff = node_hmm_scaling()
    print(
        "NODE_ROW",
        f"raw_final_sum={raw_sum:.3e}",
        f"raw_zero_at={raw_zero_at}",
        f"loglike={loglike:.3f}",
        f"arbitrary_gauge_log_shift={gauge_shift:.3e}",
        f"max_posterior_diff={postdiff:.3e}",
    )
    print()
    print("TRANSFER: ResearchNode 5 Cohomology target")
    print("method #4 change viewpoint: HMM scaling constants are a 0-cochain/gauge; cohomology lives after quotienting exact gauges.")
    print("test: add exact analytic gauges d(lam*s+mu*s^2) to dlog xi; loop residue should survive, scalar boundary energies should not.")
    zero1 = mp.mpf("14.134725141734693790457251983562")
    rects = {
        "contains_zero": (0.45, 0.55, float(zero1 - mp.mpf("0.11")), float(zero1 + mp.mpf("0.11"))),
        "gap": (0.62, 0.82, float(zero1 - mp.mpf("0.11")), float(zero1 + mp.mpf("0.11"))),
        "near_shadow": (0.5005, 0.62, float(zero1 - mp.mpf("0.11")), float(zero1 + mp.mpf("0.11"))),
    }
    gauges = [(0, 0), (3.0, 0), (0, 0.7), (-2.0, 0.4)]
    for name, rect in rects.items():
        base_count, base_energy, base_max = loop_stats(rect, 80, 0, 0)
        print(f"RECT {name}")
        for lam, mu in gauges:
            count, energy, max_abs = loop_stats(rect, 80, lam, mu)
            print(
                " GAUGE",
                f"lam={lam:+.1f}",
                f"mu={mu:+.1f}",
                f"count={float(mp.re(count)):+.6f}",
                f"count_drift={float(abs(count - base_count)):.2e}",
                f"energy_ratio={float(energy / base_energy):.3f}",
                f"max_abs_ratio={float(max_abs / base_max):.3f}",
            )


if __name__ == "__main__":
    main()
