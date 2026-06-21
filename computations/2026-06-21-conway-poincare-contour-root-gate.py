import math
import cmath
from dataclasses import dataclass

import mpmath as mp


mp.mp.dps = 50


def principal_angle(z):
    return math.atan2(math.sin(z), math.cos(z))


def xi(s):
    s = mp.mpc(s)
    return mp.mpc("0.5") * s * (s - 1) * mp.power(mp.pi, -s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def boundary(rect, n):
    a, b, t0, t1 = rect
    pts = []
    for k in range(n):
        u = k / n
        pts.append(complex(a + (b - a) * u, t0))
    for k in range(n):
        u = k / n
        pts.append(complex(b, t0 + (t1 - t0) * u))
    for k in range(n):
        u = k / n
        pts.append(complex(b - (b - a) * u, t1))
    for k in range(n):
        u = k / n
        pts.append(complex(a, t1 - (t1 - t0) * u))
    pts.append(pts[0])
    return pts


def winding_from_points(pts):
    vals = [complex(xi(z)) for z in pts]
    angles = [math.atan2(v.imag, v.real) for v in vals]
    total = 0.0
    max_jump = 0.0
    for x, y in zip(angles, angles[1:]):
        jump = principal_angle(y - x)
        total += jump
        max_jump = max(max_jump, abs(jump))
    return total / (2 * math.pi), max_jump, min(abs(v) for v in vals), len(pts)


def xi_log_deriv(s):
    s = mp.mpc(s)
    return (
        1 / s
        + 1 / (s - 1)
        - mp.log(mp.pi) / 2
        + mp.digamma(s / 2) / 2
        + mp.diff(mp.zeta, s) / mp.zeta(s)
    )


def transport_count_from_points(pts):
    vals = [xi_log_deriv(z) for z in pts]
    total = mp.mpc(0)
    for z0, z1, f0, f1 in zip(pts, pts[1:], vals, vals[1:]):
        total += (f0 + f1) / 2 * (z1 - z0)
    return total / (2j * mp.pi)


def adaptive_segment(z0, z1, tol=0.35, depth=0, max_depth=18):
    v0 = complex(xi(z0))
    v1 = complex(xi(z1))
    jump = abs(principal_angle(cmath.phase(v1) - cmath.phase(v0)))
    logjump = abs(math.log(abs(v1) + 1e-300) - math.log(abs(v0) + 1e-300))
    if depth >= max_depth or (jump <= tol and logjump <= 1.0):
        return [z0, z1]
    mid = (z0 + z1) / 2
    left = adaptive_segment(z0, mid, tol, depth + 1, max_depth)
    right = adaptive_segment(mid, z1, tol, depth + 1, max_depth)
    return left[:-1] + right


def adaptive_boundary(rect, coarse_n=8, tol=0.35):
    coarse = boundary(rect, coarse_n)
    out = []
    for z0, z1 in zip(coarse, coarse[1:]):
        seg = adaptive_segment(z0, z1, tol=tol)
        out.extend(seg[:-1])
    out.append(out[0])
    return out


@dataclass
class NodeRow:
    dt: float
    nearest_error: float
    linear_error: float
    same_point_alias: float


def node_poincare_crossing_test():
    # True section for x(t)=cos(t), y(t)=sin(t), upward x=0 crossing:
    # t = pi/2 + 2*pi*k, y = 1.  Fixed output samples inherit phase error;
    # linear interpolation root-locates the crossing and improves it.
    rows = []
    for dt in [0.45, 0.31, 0.2, 0.11, 2 * math.pi / 17, 2 * math.pi / 41]:
        true_hits = [math.pi / 2 + 2 * math.pi * k for k in range(12)]
        nearest_errs = []
        linear_errs = []
        xs = []
        for thit in true_hits:
            j = round(thit / dt)
            t_near = j * dt
            nearest_errs.append(abs(t_near - thit))
            j0 = math.floor(thit / dt)
            t0 = j0 * dt
            t1 = (j0 + 1) * dt
            x0 = math.cos(t0)
            x1 = math.cos(t1)
            # Linear root in x; this is the minimal event-location correction.
            alpha = -x0 / (x1 - x0)
            t_lin = t0 + alpha * (t1 - t0)
            linear_errs.append(abs(t_lin - thit))
            xs.append(round(math.sin(t_lin), 10))
        same_point_alias = max(xs.count(x) for x in set(xs)) / len(xs)
        rows.append(NodeRow(dt, max(nearest_errs), max(linear_errs), same_point_alias))
    return rows


def contour_rows():
    zero1 = 14.134725141734693790457251983562
    rects = {
        "contains_zero": (0.45, 0.55, zero1 - 0.11, zero1 + 0.11),
        "off_line_close_right": (0.5005, 0.62, zero1 - 0.11, zero1 + 0.11),
        "off_line_close_left": (0.38, 0.4995, zero1 - 0.11, zero1 + 0.11),
        "off_line_far_right": (0.62, 0.82, zero1 - 0.11, zero1 + 0.11),
    }
    rows = []
    for name, rect in rects.items():
        fixed = []
        for n in [4, 6, 8, 12, 20, 32]:
            pts = boundary(rect, n)
            fixed.append((n,) + winding_from_points(pts)[:3] + (transport_count_from_points(pts),))
        adap = winding_from_points(adaptive_boundary(rect, coarse_n=6, tol=0.28))
        adap_pts_tight = adaptive_boundary(rect, coarse_n=6, tol=0.05)
        transport_adap = transport_count_from_points(adap_pts_tight)
        rows.append((name, fixed, adap, len(adap_pts_tight), transport_adap))
    return rows


def main():
    print("NODE: Poincare section aliasing / missed exact crossing interpolation")
    print("constraint: section membership is g(x(t))=0 with a crossing direction; fixed output sampling is not the same object.")
    print("missing lemma: a section statistic is admissible only if it is stable under event-location refinement.")
    print()
    for row in node_poincare_crossing_test():
        print(
            "NODE_ROW",
            f"dt={row.dt:.8f}",
            f"nearest_err={row.nearest_error:.6g}",
            f"linear_root_err={row.linear_error:.6g}",
            f"same_point_alias={row.same_point_alias:.3f}",
        )
    print()
    print("TRANSFER: ResearchNode 21 contour certification for xi(s)")
    print("minimal change: event crossing g(x(t))=0 -> boundary phase event of xi(s) along contour; root-location -> adaptive phase-event subdivision.")
    print("missing lemma: contour certificates must be invariant under boundary phase-event refinement.")
    for name, fixed, adap, transport_pts, transport_adap in contour_rows():
        print()
        print("RECT", name)
        for n, wind, max_jump, min_abs, transport in fixed:
            print(
                "FIXED",
                f"n_edge={n:02d}",
                f"winding={wind:+.6f}",
                f"round={round(wind)}",
                f"transport_count={float(mp.re(transport)):+.6f}",
                f"max_phase_jump={max_jump:.3f}",
                f"min_abs_xi={min_abs:.3e}",
            )
        awind, amax, amin, acount = adap
        print(
            "ADAPTIVE",
            f"points={acount}",
            f"winding={awind:+.6f}",
            f"round={round(awind)}",
            f"max_phase_jump={amax:.3f}",
            f"min_abs_xi={amin:.3e}",
        )
        print(
            "TRANSPORT_ADAPTIVE",
            f"points={transport_pts}",
            f"transport_count={float(mp.re(transport_adap)):+.6f}",
            f"imag={float(mp.im(transport_adap)):+.3e}",
        )


if __name__ == "__main__":
    main()
