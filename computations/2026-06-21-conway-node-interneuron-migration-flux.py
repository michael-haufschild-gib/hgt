import numpy as np


def normalize_density(x, y, total=1.0):
    area = np.trapezoid(y, x)
    if area <= 0:
        return y
    return total * y / area


def deposited_density_from_hazard(x, hazard, speed=1.0, total_inflow=1.0):
    # Survival of mobile cells before settling. Deposition density is hazard * survival.
    dx = x[1] - x[0]
    cumulative_hazard = np.cumsum(hazard / speed) * dx
    survival = np.exp(-cumulative_hazard)
    raw_deposit = total_inflow * hazard / speed * survival
    return normalize_density(x, raw_deposit, total_inflow)


def roughness(x, y):
    dy = np.gradient(y, x)
    return float(np.trapezoid(dy * dy, x))


def center_of_mass(x, y):
    return float(np.trapezoid(x * y, x) / np.trapezoid(y, x))


def peak_count(y):
    return int(np.sum((y[1:-1] > y[:-2]) & (y[1:-1] > y[2:])))


def main():
    x = np.linspace(0.0, 1.0, 2001)
    total_inflow = 1.0

    uniform_local_growth = np.ones_like(x)
    uniform_local_growth = normalize_density(x, uniform_local_growth, total_inflow)

    anterior_stop_zone = 0.6 + 8.0 * np.exp(-((x - 0.25) / 0.06) ** 2)
    posterior_stop_zone = 0.6 + 8.0 * np.exp(-((x - 0.75) / 0.06) ** 2)
    dual_stop_zone = 0.5 + 5.0 * np.exp(-((x - 0.25) / 0.05) ** 2) + 5.0 * np.exp(
        -((x - 0.75) / 0.05) ** 2
    )

    cases = [
        ("local_growth_only_same_total", uniform_local_growth),
        ("migration_anterior_retention", deposited_density_from_hazard(x, anterior_stop_zone)),
        ("migration_posterior_retention", deposited_density_from_hazard(x, posterior_stop_zone)),
        ("migration_dual_retention", deposited_density_from_hazard(x, dual_stop_zone)),
    ]

    print("NODE: interneuron migration affects local density and tissue organization")
    print("Constraint tested: equal total cell input does not determine local organization without flux/retention.")
    for name, density in cases:
        print("\ncase:", name)
        print(f"  total_mass={np.trapezoid(density, x):.12f}")
        print(f"  center_of_mass={center_of_mass(x, density):.6f}")
        print(f"  max_density={np.max(density):.6f}")
        print(f"  roughness={roughness(x, density):.6f}")
        print(f"  peak_count={peak_count(density)}")

    print(
        "\nconclusion:",
        "matching total density is insufficient; migratory flux plus stopping profile constrains organization.",
    )


if __name__ == "__main__":
    main()
