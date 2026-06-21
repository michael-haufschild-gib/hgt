import numpy as np


def fe_symmetry_residual(sigma, tau, f):
    ss, tt = np.meshgrid(sigma, tau, indexing="ij")
    return float(np.max(np.abs(f(ss, tt) - f(1.0 - ss, tt))))


def kernel_negative_index(points, kernel):
    n = len(points)
    gram = np.empty((n, n))
    for i, x in enumerate(points):
        for j, y in enumerate(points):
            gram[i, j] = kernel(x, y)
    eig = np.linalg.eigvalsh(gram)
    return int(np.sum(eig < -1e-9)), eig


def main():
    sigma = np.linspace(0.25, 0.75, 251)
    tau = np.linspace(-2.0, 2.0, 121)

    def fe_exact_carrier(ss, tt):
        return np.exp(-((ss - 0.5) / 0.08) ** 2) * np.cos(tt)

    def fe_exact_with_positive_kernel(ss, tt):
        return fe_exact_carrier(ss, tt) ** 2 + 0.2

    points = np.linspace(-1.0, 1.0, 12)

    def pd_kernel(x, y):
        return np.exp(-((x - y) ** 2) / 0.2)

    def indefinite_kernel(x, y):
        return np.exp(-((x - y) ** 2) / 0.2) - 1.2 * np.cos(2 * x) * np.cos(2 * y)

    neg_pd, eig_pd = kernel_negative_index(points, pd_kernel)
    neg_indef, eig_indef = kernel_negative_index(points, indefinite_kernel)

    print("Attempt 03: functional-equation symmetry versus faithful negativity")
    print("\ncase: fe_exact_positive_proxy")
    print(f"  fe_symmetry_residual={fe_symmetry_residual(sigma, tau, fe_exact_with_positive_kernel):.6g}")
    print(f"  negative_index={neg_pd}")
    print(f"  min_eigenvalue={eig_pd[0]:.6g}")
    print("\ncase: fe_exact_indefinite_proxy")
    print(f"  fe_symmetry_residual={fe_symmetry_residual(sigma, tau, fe_exact_carrier):.6g}")
    print(f"  negative_index={neg_indef}")
    print(f"  min_eigenvalue={eig_indef[0]:.6g}")
    print(
        "\nclaim_tested:",
        "realization/FE symmetry can be exact while positivity/localization index changes.",
    )


if __name__ == "__main__":
    main()
