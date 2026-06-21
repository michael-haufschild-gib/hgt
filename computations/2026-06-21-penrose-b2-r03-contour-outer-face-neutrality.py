#!/usr/bin/env python3
import cmath
import math


def planar_map_outer_face_demo():
    # Square with a diagonal: two triangular bounded faces and one quadrilateral face.
    # On the sphere, any face can be drawn as the outer face.
    face_degrees = [3, 3, 4]
    return face_degrees


def rectangle_points(x0, x1, y0, y1, side, n):
    if side == "bottom":
        return [complex(x0 + (x1 - x0) * k / n, y0) for k in range(n)]
    if side == "right":
        return [complex(x1, y0 + (y1 - y0) * k / n) for k in range(n)]
    if side == "top":
        return [complex(x1 - (x1 - x0) * k / n, y1) for k in range(n)]
    if side == "left":
        return [complex(x0, y1 - (y1 - y0) * k / n) for k in range(n)]
    raise ValueError(side)


def contour_integral_moment(zeros, k=2, root_side=None, root_n=5, other_n=240):
    x0, x1, y0, y1 = -0.45, 0.45, 0.35, 3.25
    sides = ["bottom", "right", "top", "left"]
    path = []
    for side in sides:
        n = root_n if side == root_side else other_n
        path.extend(rectangle_points(x0, x1, y0, y1, side, n))
    total = 0j
    for a, b in zip(path, path[1:] + path[:1]):
        mid = 0.5 * (a + b)
        ds = b - a
        g = sum(1.0 / (mid - z) for z in zeros)
        total += (mid ** k) * g * ds
    return total / (2j * math.pi)


def exact_moment(zeros, k=2):
    return sum(z ** k for z in zeros)


def main():
    print("NODE test: outer face in a finite planar map is a root/drawing choice")
    degrees = planar_map_outer_face_demo()
    print(f"  Same embedded map can report outer-face degree in {sorted(set(degrees))}.")
    print(f"  Face-degree multiset is intrinsic: {sorted(degrees)}; selected outer degree is not.")

    zeros = [0.0 + 1.0j, 0.0 + 1.8j, 0.12 + 2.85j, -0.12 + 2.85j]
    exact = exact_moment(zeros, 2)
    exact_D2 = sum((z.real) ** 2 for z in zeros)
    print()
    print("ResearchNode mutation: contour-moment source-width tomography")
    print(f"  Synthetic divisor: {zeros}")
    print(f"  exact M2={exact.real:.10f}{exact.imag:+.10f}i, exact D2={exact_D2:.6f}")
    print("  Root-side-starved quadrature: same contour, one designated side gets only 5 panels.")
    rows = []
    for side in ["bottom", "right", "top", "left"]:
        approx = contour_integral_moment(zeros, k=2, root_side=side, root_n=5, other_n=240)
        err = abs(approx - exact)
        rows.append((side, approx, err))
        print(
            f"    root_side={side:6s} approx_M2={approx.real:.10f}{approx.imag:+.10f}i "
            f"abs_error={err:.3e}"
        )
    worst = max(rows, key=lambda r: r[2])
    best = min(rows, key=lambda r: r[2])
    print(f"  side artifact ratio worst/best={worst[2] / best[2]:.2f} ({worst[0]} vs {best[0]})")

    print("  Monotone side-balanced refinement check:")
    last = None
    for n in [8, 16, 32, 64, 128, 256, 512]:
        approx = contour_integral_moment(zeros, k=2, root_side=None, other_n=n)
        err = abs(approx - exact)
        monotone = "" if last is None else ("down" if err < last else "UP")
        print(f"    panels_per_side={n:3d} abs_error={err:.3e} {monotone}")
        last = err

    print()
    print("Finding:")
    print("  Contour moments are exact outer-face/root invariant residues, but numerical/event readouts can")
    print("  acquire an artificial outer face when one side is privileged. Source-width tomography should")
    print("  carry an outer-face neutrality certificate: rotate the root side and require side-balanced")
    print("  monotone refinement before interpreting M_k/D2 as divisor geometry.")


if __name__ == "__main__":
    main()
