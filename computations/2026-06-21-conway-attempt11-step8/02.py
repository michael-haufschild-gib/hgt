import numpy as np


E = np.array([[1.0, 0.0], [0.0, -1.0]])
F = np.array([[0.0, 1.0], [1.0, 0.0]])


def expm2(a):
    vals, vecs = np.linalg.eigh(a)
    return (vecs * np.exp(vals)) @ vecs.T


def holonomy(a_sigma, a_tau, ds=0.01, dt=0.01):
    # Small rectangle path ordering to first nontrivial scale.
    return (
        expm2(ds * a_sigma)
        @ expm2(dt * a_tau)
        @ expm2(-ds * a_sigma)
        @ expm2(-dt * a_tau)
    )


def nonscalar_defect(h):
    scalar = np.trace(h) / 2.0 * np.eye(2)
    return float(np.linalg.norm(h - scalar, ord="fro"))


def main():
    amp = 25.0
    width = 0.012
    sigma = np.linspace(0.45, 0.55, 501)
    ridge = amp * np.exp(-((sigma - 0.5) / width) ** 2)
    visual_score = float(np.max(np.abs(np.gradient(ridge, sigma))))

    # Same ridge amplitude, different transport axis.
    commuting_weld = holonomy(amp * E, 0.8 * amp * E)
    noncommuting_positive = holonomy(amp * E, 0.8 * amp * F)

    print("Attempt 02: same visible ridge, different non-scalar transport")
    print(f"shared_visual_gradient_score={visual_score:.6g}")
    print("\ncase: commuting_weld_axis")
    print(f"  nonscalar_holonomy_defect={nonscalar_defect(commuting_weld):.12g}")
    print(f"  matrix=\n{commuting_weld}")
    print("\ncase: noncommuting_positivity_axis")
    print(f"  nonscalar_holonomy_defect={nonscalar_defect(noncommuting_positive):.12g}")
    print(f"  matrix=\n{noncommuting_positive}")
    print(
        "\nclaim_tested:",
        "axis content can live in ordered transport while the measured ridge amplitude is fixed.",
    )


if __name__ == "__main__":
    main()
