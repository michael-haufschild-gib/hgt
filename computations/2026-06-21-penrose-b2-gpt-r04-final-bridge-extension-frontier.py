#!/usr/bin/env python3
import numpy as np


def uniform_12_moment(k):
    return (2.0 ** (k + 1) - 1.0) / (k + 1)


def hankel(moments, start, size):
    return np.array(
        [[moments[start + i + j] for j in range(size)] for i in range(size)],
        dtype=float,
    )


def min_eig(matrix):
    return float(np.linalg.eigvalsh(matrix)[0])


def extension_lower_bound(moments, d):
    # H1_d = [m_{i+j+1}]_{i,j=0..d}; only m_{2d+1} is not fixed by
    # H0_d and H1_{d-1}.  PSD forces x >= b^T A^{-1} b.
    A = hankel(moments, 1, d)
    b = np.array([moments[d + 1 + i] for i in range(d)], dtype=float)
    return float(b @ np.linalg.solve(A, b))


def main():
    print("NODE test: one spanning cluster at one scale does not certify percolation threshold")
    print("ResearchNode mutation: final bridge theorem needs projective Stieltjes extension, not isolated slabs")
    print()
    print("Base moments: uniform measure on [1,2], m_k=(2^(k+1)-1)/(k+1).")
    print("For each d, H0_d and H1_{d-1} use moments only through m_{2d};")
    print("then we set the first unseen moment m_{2d+1} just below the PSD extension frontier.")
    print()
    print("d | min_eig H0_d | min_eig H1_{d-1} | true m_next - frontier | failed next min_eig")
    print("--|--------------|------------------|------------------------|-------------------")
    for d in range(2, 8):
        moments = [uniform_12_moment(k) for k in range(2 * d + 2)]
        h0_margin = min_eig(hankel(moments, 0, d + 1))
        h1_margin = min_eig(hankel(moments, 1, d))
        frontier = extension_lower_bound(moments, d)
        true_next = moments[2 * d + 1]
        bad_next = frontier * (1.0 - 1.0e-9)
        trial = hankel(moments, 1, d + 1)
        trial[-1, -1] = bad_next
        failed_margin = min_eig(trial)
        print(
            f"{d} | {h0_margin:12.3e} | {h1_margin:16.3e} | "
            f"{(true_next - frontier):22.3e} | {failed_margin:17.3e}"
        )
    print()
    print("Finding:")
    print("  A finite positive slab can have genuine positive margins and still give no certificate")
    print("  for the first unseen Stieltjes extension. The final bridge theorem therefore needs an")
    print("  extension-frontier passport: at each scale, the completed weld must place the next")
    print("  reciprocal moment inside the projectively compatible PSD cone with controlled slack.")


if __name__ == "__main__":
    main()
