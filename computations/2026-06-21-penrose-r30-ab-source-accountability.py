#!/usr/bin/env python3
"""
R30: AB flux-tube source accountability -> bridge-arrow contour source tomography.

The NODE-side test checks whether exterior holonomy alone can identify the
source profile of a flux tube. The HGT-side transfer keeps the same source
accountability structure but replaces flux profiles by residues of d log xi in
the local pole model.
"""

import cmath
import math
from typing import Callable, Iterable, List, Sequence, Tuple


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def trapz_radial_flux(raw_density: Callable[[float], float], radius: float, n: int = 5000) -> Tuple[float, float, float]:
    """Return total flux, first radial moment, second radial moment."""
    dr = radius / n
    total = 0.0
    moment1 = 0.0
    moment2 = 0.0
    for k in range(n):
        r = (k + 0.5) * dr
        shell = 2.0 * math.pi * r * raw_density(r) * dr
        total += shell
        moment1 += r * shell
        moment2 += r * r * shell
    return total, moment1 / total, moment2 / total


def normalized_profile(raw_density: Callable[[float], float], radius: float, flux: float = 1.0) -> Callable[[float], float]:
    total, _, _ = trapz_radial_flux(raw_density, radius)
    scale = flux / total
    return lambda r: scale * raw_density(r)


def enclosed_flux(density: Callable[[float], float], loop_r: float, tube_r: float, n: int = 5000) -> float:
    upper = min(loop_r, tube_r)
    if upper <= 0.0:
        return 0.0
    dr = upper / n
    acc = 0.0
    for k in range(n):
        r = (k + 0.5) * dr
        acc += 2.0 * math.pi * r * density(r) * dr
    return acc


def node_flux_tube_test() -> dict:
    tube_r = 1.0
    total_flux = 1.0
    uniform = normalized_profile(lambda r: 1.0 if r <= tube_r else 0.0, tube_r, total_flux)
    annular = normalized_profile(
        lambda r: math.exp(-((r - 0.78 * tube_r) / (0.11 * tube_r)) ** 2) if r <= tube_r else 0.0,
        tube_r,
        total_flux,
    )

    loops = [0.2, 0.5, 0.8, 1.0, 1.2, 2.0]
    phase_rows = []
    for R in loops:
        fu = enclosed_flux(uniform, R, tube_r)
        fa = enclosed_flux(annular, R, tube_r)
        phase_rows.append((R, fu, fa, abs(fu - fa)))

    tu, mu1, mu2 = trapz_radial_flux(uniform, tube_r)
    ta, ma1, ma2 = trapz_radial_flux(annular, tube_r)
    outside_blind = max(row[3] for row in phase_rows if row[0] >= 1.0)
    inside_split = max(row[3] for row in phase_rows if row[0] < 1.0)
    return {
        "phase_rows": phase_rows,
        "total_flux_uniform": tu,
        "total_flux_annular": ta,
        "mean_radius_uniform": mu1,
        "mean_radius_annular": ma1,
        "second_radius_uniform": mu2,
        "second_radius_annular": ma2,
        "outside_blindness": outside_blind,
        "inside_source_split": inside_split,
    }


Source = Tuple[float, float, float]  # x=sigma-1/2, y=t-gamma, residue


def residue_field(z: complex, sources: Sequence[Source]) -> complex:
    total = 0j
    for x, y, residue in sources:
        total += residue / (z - complex(x, y))
    return total


def integrate_segment(f: Callable[[complex], complex], a: complex, b: complex, n: int) -> complex:
    dz = (b - a) / n
    acc = 0j
    for k in range(n):
        z = a + (k + 0.5) * dz
        acc += f(z) * dz
    return acc


def rectangle_charge(sources: Sequence[Source], half_width: float, half_height: float = 1.0, n: int = 400) -> complex:
    left = complex(-half_width, -half_height)
    right = complex(half_width, -half_height)
    top_right = complex(half_width, half_height)
    top_left = complex(-half_width, half_height)
    f = lambda z: residue_field(z, sources)
    integral = (
        integrate_segment(f, left, right, n)
        + integrate_segment(f, right, top_right, n)
        + integrate_segment(f, top_right, top_left, n)
        + integrate_segment(f, top_left, left, n)
    )
    return integral / (2j * math.pi)


def logistic(u: float) -> float:
    if u > 40:
        return 1.0
    if u < -40:
        return 0.0
    return 1.0 / (1.0 + math.exp(-u))


def width_profile_moments(sources: Sequence[Source], eps: float = 0.01, wmax: float = 0.35, n: int = 2000) -> Tuple[float, float, float]:
    """Moments of the derivative of smoothed strip charge as width grows."""
    dw = wmax / n
    mass = 0.0
    mean = 0.0
    second = 0.0
    peak_w = 0.0
    peak_v = -1.0
    for k in range(n + 1):
        w = k * dw
        derivative = 0.0
        for x, _y, residue in sources:
            u = (w - abs(x)) / eps
            L = logistic(u)
            derivative += residue * L * (1.0 - L) / eps
        if derivative > peak_v:
            peak_v = derivative
            peak_w = w
        weight = derivative * dw
        mass += weight
        mean += w * weight
        second += w * w * weight
    return mean / mass, second / mass, peak_w


def source_passport(sources: Sequence[Source]) -> Tuple[float, float, float]:
    count = sum(residue for _x, _y, residue in sources)
    first_x = sum(residue * x for x, _y, residue in sources)
    second_x = sum(residue * x * x for x, _y, residue in sources) / count
    return count, first_x, second_x


def hgt_bridge_transfer_test() -> dict:
    a = 0.12
    seam = [(0.0, 0.0, 1.0), (0.0, 0.15, 1.0)]
    off_seam_pair = [(-a, 0.0, 1.0), (a, 0.0, 1.0)]
    widths = [0.02, 0.05, 0.10, 0.14, 0.20, 0.30]
    rows = []
    for w in widths:
        cs = rectangle_charge(seam, w)
        co = rectangle_charge(off_seam_pair, w)
        rows.append((w, cs.real, abs(cs.imag), co.real, abs(co.imag)))
    seam_m = width_profile_moments(seam)
    off_m = width_profile_moments(off_seam_pair)
    return {
        "a": a,
        "passports": {
            "seam": source_passport(seam),
            "off_seam_pair": source_passport(off_seam_pair),
        },
        "charge_rows": rows,
        "width_profile": {
            "seam_mean_second_peak": seam_m,
            "off_mean_second_peak": off_m,
        },
    }


def transfer_choice() -> dict:
    base = """
for each loop radius R:
    holonomy[R] = integral_loop A.dot(dl)
source_profile = radial_distribution_inside_flux_tube
test: exterior holonomy equal; source moments differ
"""
    attempts = {
        "A_nested_contour_source_tomography": """
for each rectangle half_width w:
    holonomy[w] = contour_integral sum_rho residue/(s-rho) ds
source_profile = width_derivative_of_strip_charge
test: exterior contour charge equal; off_seam source moments differ
""",
        "B_phase_carrier_delta_lanes": """
for each sigma lane:
    delta = max(logabs(A), logabs(P)) - logabs(A+P)
source_profile = cross_lane_phase_memory_kernel
test: phase carrier survives finite Euler and phase random controls
""",
        "C_finite_euler_lane_covariance": """
for each finite prime cutoff N:
    lane_covariance = covariance(logabs(P_N), arg(P_N))
source_profile = sigma_lane_association_graph
test: finite lane covariance fails right-strip collapse controls
""",
    }
    distances = {name: levenshtein(base, text) for name, text in attempts.items()}
    chosen = min(distances, key=distances.get)
    return {"distances": distances, "chosen": chosen}


def apply_method_14_weaken_conjecture(hgt: dict) -> dict:
    """Method 14: weaken bridge-arrow to an insufficiency gate."""
    rows = hgt["charge_rows"]
    same_external = [row for row in rows if row[0] >= 0.14]
    max_external_charge_gap = max(abs(row[1] - row[3]) for row in same_external)
    seam_second = hgt["width_profile"]["seam_mean_second_peak"][1]
    off_second = hgt["width_profile"]["off_mean_second_peak"][1]
    return {
        "method": "14 weaken the conjecture",
        "weakened_claim": "contour charge plus affine passport is insufficient for seam confinement",
        "max_external_charge_gap": max_external_charge_gap,
        "source_second_moment_gap": off_second - seam_second,
        "same_affine_passport": hgt["passports"]["seam"][:2] == hgt["passports"]["off_seam_pair"][:2],
    }


def step12_followup() -> dict:
    """Interrogate the source-accountability gate across method-style checks."""
    separation_rows = []
    for a in [0.02, 0.05, 0.08, 0.12, 0.20, 0.30]:
        seam = [(0.0, 0.0, 1.0), (0.0, 0.15, 1.0)]
        off = [(-a, 0.0, 1.0), (a, 0.0, 1.0)]
        hgt = {
            "passports": {"seam": source_passport(seam), "off_seam_pair": source_passport(off)},
            "charge_rows": [(0.35, rectangle_charge(seam, 0.35).real, 0.0, rectangle_charge(off, 0.35).real, 0.0)],
            "width_profile": {
                "seam_mean_second_peak": width_profile_moments(seam, eps=max(0.002, a / 12.0), wmax=max(0.35, 2.0 * a)),
                "off_mean_second_peak": width_profile_moments(off, eps=max(0.002, a / 12.0), wmax=max(0.35, 2.0 * a)),
            },
        }
        method = apply_method_14_weaken_conjecture(hgt)
        separation_rows.append(
            (
                a,
                method["same_affine_passport"],
                method["max_external_charge_gap"],
                method["source_second_moment_gap"],
                hgt["width_profile"]["off_mean_second_peak"][2],
            )
        )

    smoothing_rows = []
    a = 0.12
    off = [(-a, 0.0, 1.0), (a, 0.0, 1.0)]
    for eps_ratio in [0.025, 0.05, 0.10, 0.25, 0.50, 1.00, 1.50]:
        mean, second, peak = width_profile_moments(off, eps=a * eps_ratio, wmax=0.45)
        smoothing_rows.append((eps_ratio, mean, second, peak, abs(peak - a)))

    signed_false = [(0.0, 0.0, 2.0), (-a, 0.0, 1.0), (a, 0.0, -1.0)]
    # Same total count as the seam control, but signed residues break monotonic source positivity.
    signed_profile = width_profile_moments(signed_false, eps=0.01, wmax=0.35)

    method_table = [
        ("split", "separate count, first moment, second source-width moment"),
        ("attack-false", "signed residues can defeat moment logic; xi zeros have positive multiplicity"),
        ("reverse", "with positive residues, zero second width moment forces all sources on the seam"),
        ("change-viewpoint", "differentiate nested contour charge instead of using one exterior contour"),
        ("small-cases", "two symmetric off-seam sources are the minimal positive-residue counterexample"),
        ("extreme-cases", "as a -> 0 the source moment vanishes; as smoothing eps >= a the peak location degrades"),
        ("invariant", "affine passport (count, first moment) is held fixed"),
        ("monotone", "positive-residue strip charge is nondecreasing in half-width"),
        ("nearby-false", "one-scale smoothing or exterior holonomy alone can certify a false seam"),
        ("boundary", "sources near the rectangle boundary require a guard band"),
    ]
    return {
        "separation_rows": separation_rows,
        "smoothing_rows": smoothing_rows,
        "signed_false_profile": signed_profile,
        "method_table": method_table,
    }


def main() -> None:
    node = node_flux_tube_test()
    choice = transfer_choice()
    hgt = hgt_bridge_transfer_test()
    method = apply_method_14_weaken_conjecture(hgt)
    follow = step12_followup()

    print("R30 AB_SOURCE_ACCOUNTABILITY")
    print("NODE_RESULT")
    print(f"  outside_blindness={node['outside_blindness']:.12g}")
    print(f"  inside_source_split={node['inside_source_split']:.12g}")
    print(f"  mean_radius_uniform={node['mean_radius_uniform']:.12g}")
    print(f"  mean_radius_annular={node['mean_radius_annular']:.12g}")
    print(f"  second_radius_uniform={node['second_radius_uniform']:.12g}")
    print(f"  second_radius_annular={node['second_radius_annular']:.12g}")
    for R, fu, fa, gap in node["phase_rows"]:
        print(f"  loop R={R:.2f}: uniform={fu:.9f} annular={fa:.9f} gap={gap:.9f}")

    print("STEP8_LEVENSHTEIN")
    for name, dist in sorted(choice["distances"].items(), key=lambda kv: kv[1]):
        print(f"  {name}: {dist}")
    print(f"  chosen={choice['chosen']}")

    print("HGT_TRANSFER_RESULT")
    print(f"  off_seam_half_width_a={hgt['a']}")
    print(f"  seam_passport_count_first_second={hgt['passports']['seam']}")
    print(f"  off_passport_count_first_second={hgt['passports']['off_seam_pair']}")
    for w, seam_re, seam_imag_err, off_re, off_imag_err in hgt["charge_rows"]:
        print(
            "  rectangle "
            f"w={w:.2f}: seam_charge={seam_re:.6f} "
            f"off_charge={off_re:.6f} "
            f"imag_errs=({seam_imag_err:.2e},{off_imag_err:.2e})"
        )
    print(f"  width_profile_seam_mean_second_peak={hgt['width_profile']['seam_mean_second_peak']}")
    print(f"  width_profile_off_mean_second_peak={hgt['width_profile']['off_mean_second_peak']}")

    print("STEP9_METHOD_RESULT")
    for key, value in method.items():
        print(f"  {key}={value}")

    print("STEP12_FOLLOWUP")
    print("  separation_sweep a same_passport external_gap second_moment_gap profile_peak")
    for row in follow["separation_rows"]:
        print(f"  a={row[0]:.3f} same={row[1]} external_gap={row[2]:.3e} second_gap={row[3]:.9f} peak={row[4]:.5f}")
    print("  smoothing_sweep eps_over_a mean second peak peak_error")
    for row in follow["smoothing_rows"]:
        print(f"  eps/a={row[0]:.3f} mean={row[1]:.6f} second={row[2]:.9f} peak={row[3]:.5f} peak_error={row[4]:.5f}")
    print(f"  signed_false_profile_mean_second_peak={follow['signed_false_profile']}")
    print("  method_checks")
    for name, text in follow["method_table"]:
        print(f"    {name}: {text}")

    print("INTERPRETATION")
    print(
        "  Exterior holonomy/contour charge can be identical after the source is enclosed, "
        "and the affine passport (count, first moment) can also agree. The source-inclusive "
        "width-derivative profile still separates seam-confined from symmetric off-seam sources."
    )


if __name__ == "__main__":
    main()
