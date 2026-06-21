#!/usr/bin/env python3
import numpy as np


def inertia(M, tol=1e-10):
    vals = np.linalg.eigvalsh(M)
    neg = int(np.sum(vals < -tol))
    zero = int(np.sum(np.abs(vals) <= tol))
    pos = int(np.sum(vals > tol))
    return neg, zero, pos, vals


def node_fusion_demo():
    # Same anyon labels: tau,tau,tau. Intermediate fusion channel differs.
    # Fibonacci rule: tau x tau = 1 + tau; then (tau x tau)_a x tau.
    channels = {
        "intermediate_1": {"dimension": 1, "total_tau_allowed": True, "total_1_allowed": False},
        "intermediate_tau": {"dimension": 1, "total_tau_allowed": True, "total_1_allowed": True},
    }
    return channels


def block(c):
    return np.array([[1.0, c], [c, 1.0]])


def research_channel_forms():
    # Same four source atoms and same diagonal reporter in both channels.
    # Channel A pairs the two high-coupling atoms together, creating one negative direction.
    A = np.zeros((4, 4))
    A[:2, :2] = block(1.25)
    A[2:, 2:] = block(0.25)

    # Channel B fuses the same atoms crosswise; both blocks stay positive.
    B = np.zeros((4, 4))
    idx1 = [0, 2]
    idx2 = [1, 3]
    for idx, c in [(idx1, 0.75), (idx2, 0.75)]:
        sub = block(c)
        for i, ii in enumerate(idx):
            for j, jj in enumerate(idx):
                B[ii, jj] = sub[i, j]

    scalar_report = {
        "diagonal": np.diag(A).tolist(),
        "trace_A": float(np.trace(A)),
        "trace_B": float(np.trace(B)),
        "fro_A": float(np.linalg.norm(A, ord="fro")),
        "fro_B": float(np.linalg.norm(B, ord="fro")),
    }
    return A, B, scalar_report


def main():
    print("NODE test: fusion channel is part of anyon state data")
    for name, info in node_fusion_demo().items():
        print(f"  {name}: {info}")
    print("  Same type list tau,tau,tau; intermediate channel changes the state space.")

    print()
    print("ResearchNode mutation: kappa_- construction needs a fusion/channel passport")
    A, B, rep = research_channel_forms()
    IA = inertia(A)
    IB = inertia(B)
    print(f"  scalar diagonal reporter A={rep['diagonal']}, B={rep['diagonal']}")
    print(f"  traces A/B={rep['trace_A']:.3f}/{rep['trace_B']:.3f}")
    print(f"  Frobenius norms A/B={rep['fro_A']:.6f}/{rep['fro_B']:.6f}")
    print(f"  channel_A inertia neg/zero/pos={IA[:3]}, eigenvalues={', '.join(f'{x:.3f}' for x in IA[3])}")
    print(f"  channel_B inertia neg/zero/pos={IB[:3]}, eigenvalues={', '.join(f'{x:.3f}' for x in IB[3])}")

    # A non-congruent reporter that keeps only diagonal and total offdiag mass erases the channel.
    off_A = float(np.sum(np.abs(A - np.diag(np.diag(A)))))
    off_B = float(np.sum(np.abs(B - np.diag(np.diag(B)))))
    print(f"  offdiag absolute mass A/B={off_A:.3f}/{off_B:.3f}")
    print()
    print("Finding:")
    print("  Same source labels and diagonal data can have different kappa_- depending on fusion/channel")
    print("  wiring. A source-built index must report the channel map from Euler/Gamma/pole/FE data into")
    print("  a congruence class of forms; marginal source labels or scalar reporters are not enough.")


if __name__ == "__main__":
    main()
