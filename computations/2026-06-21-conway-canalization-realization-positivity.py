import math
import numpy as np


def node_canalization():
    rng = np.random.default_rng(20260621)
    hidden = rng.normal(0, 1, size=2000)
    # Canalized phenotype clips variation until stress exceeds a buffer.
    normal = np.tanh(0.15 * hidden)
    stress = np.tanh(1.2 * hidden)
    return {
        "normal_var": float(np.var(normal)),
        "stress_var": float(np.var(stress)),
        "normal_tail": float(np.mean(abs(normal) > 0.8)),
        "stress_tail": float(np.mean(abs(stress) > 0.8)),
    }


def quartet_zeros(a, gamma):
    return [
        complex(a, gamma),
        complex(-a, gamma),
        complex(a, -gamma),
        complex(-a, -gamma),
    ]


def online_matched_zeros(a, gamma):
    # Match the second central power sum p2 of the off-line quartet by one
    # on-line quartet at height sqrt(gamma^2 - a^2).  FE symmetry and the
    # quadratic bulk moment agree, but positivity/localization differs.
    b = math.sqrt(gamma * gamma - a * a)
    return [complex(0, b), complex(0, b), complex(0, -b), complex(0, -b)]


def power_sum(zeros, k):
    return sum(z ** k for z in zeros)


def logabs_poly(z, zeros):
    out = 0.0
    for r in zeros:
        out += math.log(abs(z - r) + 1e-300)
    return out


def curvature_sigma(tau, zeros, h=1e-4):
    # second derivative in the real/sigma direction at central coordinate sigma=0
    f0 = logabs_poly(complex(0, tau), zeros)
    fp = logabs_poly(complex(h, tau), zeros)
    fm = logabs_poly(complex(-h, tau), zeros)
    return (fp - 2 * f0 + fm) / (h * h)


def fe_residual(zeros, grid):
    # Central-coordinate FE symmetry z -> -conj(z).
    return max(abs(logabs_poly(z, zeros) - logabs_poly(-z.conjugate(), zeros)) for z in grid)


def main():
    print("NODE: developmental canalization hides cryptic variation until stress exposes it")
    n = node_canalization()
    print(
        "NODE_ROW",
        f"normal_var={n['normal_var']:.5f}",
        f"stress_var={n['stress_var']:.5f}",
        f"normal_tail={n['normal_tail']:.5f}",
        f"stress_tail={n['stress_tail']:.5f}",
    )
    print()
    print("TRANSFER: ResearchNode 16 positivity vs realization")
    print("method #22: compare nearby false statements")
    print("false statement A: FE/realization symmetry implies positivity")
    print("false statement B: FE plus low-order bulk moment implies positivity")
    grid = [complex(x, y) for x in np.linspace(-0.4, 0.4, 9) for y in np.linspace(18.0, 22.0, 9)]
    gamma = 20.0
    for a in [0.02, 0.05, 0.10, 0.20]:
        off = quartet_zeros(a, gamma)
        on = online_matched_zeros(a, gamma)
        p2_gap = abs(power_sum(off, 2) - power_sum(on, 2))
        p4_gap = abs(power_sum(off, 4) - power_sum(on, 4))
        fe_off = fe_residual(off, grid)
        fe_on = fe_residual(on, grid)
        taus = np.linspace(-4 * a, 4 * a, 201)
        off_curv = [curvature_sigma(gamma + tau, off) for tau in taus]
        on_curv = [curvature_sigma(gamma + tau, on) for tau in taus]
        print(
            "ROW",
            f"a={a:.3f}",
            f"p2_gap={p2_gap:.3e}",
            f"p4_gap={p4_gap:.3e}",
            f"FE_off={fe_off:.2e}",
            f"FE_on={fe_on:.2e}",
            f"off_curv_max={max(off_curv):+.3e}",
            f"off_curv_min={min(off_curv):+.3e}",
            f"on_curv_max={max(on_curv):+.3e}",
            f"on_curv_min={min(on_curv):+.3e}",
        )


if __name__ == "__main__":
    main()
