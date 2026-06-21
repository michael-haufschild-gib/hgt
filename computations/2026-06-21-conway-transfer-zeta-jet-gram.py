#!/usr/bin/env python3
"""
Step 8 transfer script.

NODE script:
  finite Gram kernel PSD requires every finite subset, not pairwise checks.

Minimal transfer selected by Levenshtein:
  finite Gram matrix of zeta derivative jets requires every finite jet subset,
  not pairwise checks.

We form L2 Gram matrices of continuum derivative-jet functions
  f_j(t)=d^j/dsigma^j log xi(sigma+i t)
on a critical-strip line segment.  Pairwise correlations can look harmless
while the multi-jet Gram determinant is tiny, i.e. near finite-rank closure.
"""

import numpy as np
import mpmath as mp

mp.mp.dps = 50


def xi_completed(s):
    return mp.mpf("0.5") * s * (s - 1) * mp.power(mp.pi, -s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def log_xi(s):
    return mp.log(xi_completed(s))


def jet_value(order, sigma, t):
    f = lambda x: log_xi(x + 1j * t)
    return complex(mp.diff(f, sigma, order))


def sample_jets(sigma, t_values, max_order):
    data = np.zeros((max_order + 1, len(t_values)), dtype=complex)
    for j in range(max_order + 1):
        for k, t in enumerate(t_values):
            data[j, k] = jet_value(j, sigma, float(t))
    return data


def complex_l2_gram(data):
    # trapezoid weights are constant enough for this diagnostic grid
    return data @ data.conjugate().T / data.shape[1]


def corr_from_gram(G):
    d = np.sqrt(np.maximum(np.real(np.diag(G)), 0))
    C = G / np.outer(d, d)
    return C


def condition_report(G):
    evals = np.linalg.eigvalsh(G)
    return float(evals[0]), float(evals[-1]), float(evals[-1] / max(evals[0], 1e-300)), float(np.linalg.det(G).real)


def main():
    sigma = 0.6
    t_values = np.linspace(10.0, 30.0, 81)
    max_order = 5
    print("Step 8 transfer: zeta/completed-xi derivative jet Gram")
    print(f"sigma={sigma}, t-window=[{t_values[0]}, {t_values[-1]}], samples={len(t_values)}, max_order={max_order}")
    data = sample_jets(sigma, t_values, max_order)
    # Normalize each jet to isolate dependence structure rather than scale.
    norms = np.sqrt(np.mean(np.abs(data) ** 2, axis=1))
    normalized_data = data / norms[:, None]
    G = complex_l2_gram(normalized_data)
    C = corr_from_gram(G)

    print()
    print("pairwise absolute correlations:")
    for i in range(max_order + 1):
        row = []
        for j in range(max_order + 1):
            row.append(f"{abs(C[i, j]):.3f}")
        print("  " + " ".join(row))

    print()
    print("prefix Gram condition reports after per-jet normalization:")
    print("  size min_eig max_eig condition det")
    for n in range(2, max_order + 2):
        H = G[:n, :n]
        mn, mx, cond, det = condition_report(H)
        print(f"  {n:>4} {mn:+.6e} {mx:+.6e} {cond:.6e} {det:+.6e}")

    print()
    print("nearby false shortcut:")
    pairwise_max = max(abs(C[i, j]) for i in range(max_order + 1) for j in range(i))
    full_min, full_max, full_cond, full_det = condition_report(G)
    print(f"  max off-diagonal pairwise correlation={pairwise_max:.6f}")
    print(f"  full Gram min eigenvalue={full_min:.6e}")
    print(f"  full Gram condition={full_cond:.6e}")
    print("  Pairwise checks see only correlations; multi-jet Gram sees closure/conditioning.")


if __name__ == "__main__":
    main()
