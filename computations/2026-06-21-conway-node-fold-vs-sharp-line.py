import numpy as np


def ridge_score(x, intensity):
    grad = np.gradient(intensity, x)
    return float(np.max(np.abs(grad)))


def fit_log_slope(x, y, lo=1e-4, hi=2e-2):
    mask = (x > lo) & (x < hi) & (y > 0)
    coeff = np.polyfit(np.log(x[mask]), np.log(y[mask]), 1)
    return float(coeff[0])


def fold_density(x, eps=1e-7):
    y = np.zeros_like(x)
    mask = x > 0
    # Ray map X = u^2 has two preimages for x > 0, each with |dX/du| = 2 sqrt(x).
    y[mask] = 1.0 / np.sqrt(x[mask] + eps)
    return y


def gaussian_ridge(x, width=0.018):
    return 1.0 + 40.0 * np.exp(-(x / width) ** 2)


def detector_edge(x, width=0.006):
    return 1.0 + 40.0 / (1.0 + np.exp(x / width))


def classify_case(name, x, intensity, map_kind):
    if map_kind == "fold":
        preimages_left = 0
        preimages_right = 2
        min_abs_jacobian = 0.0
        second_derivative_at_singularity = 2.0
        singular_projection = True
    else:
        preimages_left = 1
        preimages_right = 1
        min_abs_jacobian = 1.0
        second_derivative_at_singularity = 0.0
        singular_projection = False

    slope = fit_log_slope(np.abs(x), intensity)
    sharp = ridge_score(x, intensity)
    fold_like_scaling = -0.65 < slope < -0.35
    preimage_jump = preimages_left != preimages_right
    structure_pass = (
        singular_projection
        and min_abs_jacobian == 0.0
        and abs(second_derivative_at_singularity) > 0
        and preimage_jump
        and fold_like_scaling
    )

    return {
        "name": name,
        "ridge_score": sharp,
        "log_slope_near_line": slope,
        "preimages_left": preimages_left,
        "preimages_right": preimages_right,
        "min_abs_jacobian": min_abs_jacobian,
        "second_derivative": second_derivative_at_singularity,
        "visual_ridge_detector": sharp > 1000.0,
        "fold_structure_detector": structure_pass,
    }


def main():
    x = np.linspace(-0.08, 0.08, 4001)
    cases = [
        classify_case("true_fold_X_equals_u_squared", x, fold_density(x), "fold"),
        classify_case("sharp_gaussian_intensity_line", x, gaussian_ridge(x), "regular"),
        classify_case("sharp_detector_edge", x, detector_edge(x), "regular"),
    ]

    print("NODE: mistaken identification of a fold with any sharp high-intensity line")
    print("Constraint tested: fold requires a singular projection, not only large intensity gradient.")
    for row in cases:
        print("\ncase:", row["name"])
        print(f"  ridge_score={row['ridge_score']:.6g}")
        print(f"  log_slope_near_line={row['log_slope_near_line']:.6g}")
        print(f"  preimages_left/right={row['preimages_left']}/{row['preimages_right']}")
        print(f"  min_abs_jacobian={row['min_abs_jacobian']:.6g}")
        print(f"  second_derivative={row['second_derivative']:.6g}")
        print(f"  visual_ridge_detector={row['visual_ridge_detector']}")
        print(f"  fold_structure_detector={row['fold_structure_detector']}")

    visual_false_positives = [
        row["name"]
        for row in cases
        if row["visual_ridge_detector"] and not row["fold_structure_detector"]
    ]
    print("\nvisual_false_positives:", visual_false_positives)
    print(
        "conclusion:",
        "sharp intensity is not a defining constraint; singular-Jacobian preimage structure is.",
    )


if __name__ == "__main__":
    main()
