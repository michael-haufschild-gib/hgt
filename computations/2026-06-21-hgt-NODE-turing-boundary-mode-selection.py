#!/usr/bin/env python3
import numpy as np


def growth_rate(k2, a=0.9, b=1.0, c=-1.2, d=-0.7, du=0.03, dv=0.9):
    # Linearized activator-inhibitor Jacobian plus diffusion.
    mat = np.array([[a - du * k2, b], [c, d - dv * k2]], dtype=float)
    return float(np.max(np.linalg.eigvals(mat).real))


def modes(kind, n=16, length=8.0):
    if kind == "periodic":
        return [(2 * np.pi * m / length) ** 2 for m in range(0, n)]
    if kind == "neumann":
        return [(np.pi * m / length) ** 2 for m in range(0, n)]
    if kind == "dirichlet":
        return [(np.pi * m / length) ** 2 for m in range(1, n + 1)]
    if kind == "mixed":
        return [((m + 0.5) * np.pi / length) ** 2 for m in range(0, n)]
    raise ValueError(kind)


def summarize(length):
    rows = []
    for kind in ["periodic", "neumann", "dirichlet", "mixed"]:
        rates = np.array([growth_rate(k2) for k2 in modes(kind, length=length)])
        rows.append(
            {
                "kind": kind,
                "unstable": int(np.sum(rates > 0.0)),
                "best_mode": int(np.argmax(rates)),
                "best_rate": float(np.max(rates)),
                "first_rate": float(rates[0]),
            }
        )
    return rows


def main():
    print("NODE: Turing boundary conditions select or suppress modes")
    print("length boundary unstable_modes best_mode best_rate first_admissible_rate")
    for length in [4.0, 5.5, 8.0, 12.0]:
        for row in summarize(length):
            print(
                f"{length:4.1f} {row['kind']:9s} {row['unstable']:14d} "
                f"{row['best_mode']:9d} {row['best_rate']:.6f} {row['first_rate']:.6f}"
            )


if __name__ == "__main__":
    main()
