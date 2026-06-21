#!/usr/bin/env python3
"""THE-MACHINE NODE test.

NODE: numerical discretizations can accidentally approximate a different
fractional operator on a bounded domain.

The stripped distinction is:
- regional/censored operator: interior nonlocal jumps only;
- restricted zero-exterior operator: same interior jumps plus exterior killing;
- spectral fractional Dirichlet operator: sine basis fractional powers.
"""

import numpy as np
from scipy.linalg import expm


def restricted_and_regional(N=140, frac=0.65):
    h = 1.0 / (N + 1)
    x = np.arange(1, N + 1) * h
    power = 1.0 + 2.0 * frac
    regional = np.zeros((N, N), dtype=float)
    for i in range(N):
        for j in range(N):
            if i == j:
                continue
            w = h / abs(x[i] - x[j]) ** power
            regional[i, i] += w
            regional[i, j] -= w

    restricted = regional.copy()
    exterior = (x ** (-2.0 * frac) + (1.0 - x) ** (-2.0 * frac)) / (2.0 * frac)
    restricted[np.diag_indices(N)] += exterior
    return x, restricted, regional


def spectral_dirichlet(N=140, frac=0.65):
    k = np.arange(1, N + 1)
    i = np.arange(1, N + 1)[:, None]
    q = np.sqrt(2.0 / (N + 1)) * np.sin(np.pi * i * k / (N + 1))
    lam = (np.pi * k) ** (2.0 * frac)
    return (q * lam) @ q.T


def mass(u, h):
    return h * np.sum(u)


def main():
    N = 140
    frac = 0.65
    x, L_res, L_reg = restricted_and_regional(N, frac)
    L_spec = spectral_dirichlet(N, frac)
    h = 1.0 / (N + 1)
    u0 = np.exp(-((x - 0.5) / 0.12) ** 2)
    u0 /= mass(u0, h)

    t = 0.015
    out = {}
    for name, L in [("regional", L_reg), ("restricted", L_res), ("spectral", L_spec)]:
        u = expm(-t * L) @ u0
        out[name] = {
            "mass": mass(u, h),
            "left_boundary_mean": float(np.mean(u[:8])),
            "center_mean": float(np.mean(u[N // 2 - 4 : N // 2 + 4])),
            "row_sum_edge": float(np.sum(L[0])),
            "row_sum_center": float(np.sum(L[N // 2])),
        }

    eig_reg = np.linalg.eigvalsh(L_reg)[:5]
    eig_res = np.linalg.eigvalsh(L_res)[:5]
    eig_spec = np.linalg.eigvalsh(L_spec)[:5]

    print(f"N={N} frac={frac} t={t}")
    for name, vals in out.items():
        print(
            name,
            "mass={mass:.8f} boundary={left_boundary_mean:.6f} center={center_mean:.6f} "
            "row_edge={row_sum_edge:.4g} row_center={row_sum_center:.4g}".format(**vals),
        )
    print("eig regional", " ".join(f"{v:.6g}" for v in eig_reg))
    print("eig restricted", " ".join(f"{v:.6g}" for v in eig_res))
    print("eig spectral", " ".join(f"{v:.6g}" for v in eig_spec))
    print("restricted_minus_regional_diag_edge", L_res[0, 0] - L_reg[0, 0])
    print("restricted_minus_regional_diag_center", L_res[N // 2, N // 2] - L_reg[N // 2, N // 2])


if __name__ == "__main__":
    main()
