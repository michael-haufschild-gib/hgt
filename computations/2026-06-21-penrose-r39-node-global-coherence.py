#!/usr/bin/env python3
"""
R39 NODE validation: global coherence can remain when subsystems look decohered.
"""

from __future__ import annotations

import numpy as np


def partial_trace_b(rho: np.ndarray) -> np.ndarray:
    out = np.zeros((2, 2), dtype=complex)
    for a in range(2):
        for ap in range(2):
            for b in range(2):
                out[a, ap] += rho[2 * a + b, 2 * ap + b]
    return out


def purity(rho: np.ndarray) -> float:
    return float(np.real(np.trace(rho @ rho)))


def main() -> None:
    psi = np.array([1, 0, 0, 1], dtype=complex) / np.sqrt(2)
    rho = np.outer(psi, psi.conj())
    red = partial_trace_b(rho)
    print("object              purity    offdiag_l1")
    print(f"global_bell       {purity(rho):8.4f} {np.sum(np.abs(rho - np.diag(np.diag(rho)))):11.4f}")
    print(f"local_reduction   {purity(red):8.4f} {np.sum(np.abs(red - np.diag(np.diag(red)))):11.4f}")
    print("\nNODE verdict:")
    print(
        "The local subsystem is diagonal and mixed, while the global Bell state remains pure "
        "with off-diagonal coherence. Apparent local decoherence need not mean global coherence is gone."
    )


if __name__ == "__main__":
    main()
