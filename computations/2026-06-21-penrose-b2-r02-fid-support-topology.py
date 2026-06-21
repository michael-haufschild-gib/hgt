#!/usr/bin/env python3
import cmath
import math

import mpmath as mp
import numpy as np


def winding(poly, point=0j):
    total = 0.0
    for a, b in zip(poly, poly[1:] + poly[:1]):
        za = a - point
        zb = b - point
        total += cmath.phase(zb / za)
    return round(total / (2 * math.pi))


def segment_intersection(a, b, c, d):
    def orient(p, q, r):
        return ((q.real - p.real) * (r.imag - p.imag) - (q.imag - p.imag) * (r.real - p.real))

    o1 = orient(a, b, c)
    o2 = orient(a, b, d)
    o3 = orient(c, d, a)
    o4 = orient(c, d, b)
    return o1 * o2 < 0 and o3 * o4 < 0


def self_avoiding(poly):
    n = len(poly)
    for i in range(n):
        a, b = poly[i], poly[(i + 1) % n]
        for j in range(i + 1, n):
            if abs(i - j) <= 1 or (i == 0 and j == n - 1):
                continue
            c, d = poly[j], poly[(j + 1) % n]
            if segment_intersection(a, b, c, d):
                return False
    return True


def min_nonadjacent_vertex_distance(poly):
    n = len(poly)
    best = float("inf")
    for i in range(n):
        for j in range(i + 1, n):
            if abs(i - j) <= 1 or (i == 0 and j == n - 1):
                continue
            best = min(best, abs(poly[i] - poly[j]))
    return best


def hankel_min_eig(moments, offset, d):
    H = np.array([[float(moments[i + j + offset]) for j in range(d)] for i in range(d)])
    return float(np.linalg.eigvalsh(H)[0])


def integer_fid_moments(K):
    # Shifted Stieltjes moments: zeta(2k+1)=sum_m (1/m)(1/m^2)^k, k >= 1.
    return [mp.nan] + [mp.zeta(2 * k + 1) for k in range(1, K + 2)]


def zero_reciprocal_moments(K, nzeros=300):
    zeros = [mp.im(mp.zetazero(n)) for n in range(1, nzeros + 1)]
    # Pair +/-gamma. The global scalar 2 cancels in endpoint ratios and PSD sign.
    return [mp.nan] + [mp.mpf(2) * mp.fsum([g ** (-2 * k) for g in zeros]) for k in range(1, K + 2)]


def endpoint_ratios(moments, start=1, stop=10):
    return [moments[k + 1] / moments[k] for k in range(start, stop)]


def main():
    print("NODE test: local self-avoidance versus global winding/topology")
    no_wind = [2 + 2j, 4 + 2j, 4 + 4j, 2 + 4j]
    wind_one = [-2 - 2j, 2 - 2j, 2 + 2j, -2 + 2j]
    for label, poly in [("no_wind_square", no_wind), ("wind_one_square", wind_one)]:
        print(
            f"  {label}: self_avoiding={self_avoiding(poly)} "
            f"min_nonadj_vertex_dist={min_nonadjacent_vertex_distance(poly):.3f} "
            f"winding_about_origin={winding(poly)}"
        )
    print("  Local excluded-volume passes both; only winding sees the global constraint.")

    mp.mp.dps = 60
    K = 14
    fid = integer_fid_moments(K)
    zer = zero_reciprocal_moments(K, nzeros=300)
    fid_ratios = endpoint_ratios(fid, start=1, stop=11)
    zero_ratios = endpoint_ratios(zer, start=1, stop=11)

    print()
    print("ResearchNode mutation: FID integer divisor versus zero reciprocal-seam divisor")
    print("  Stieltjes PSD check (small Hankel towers):")
    for d in (3, 4, 5, 6):
        print(
            f"    d={d}: FID_min_eig={hankel_min_eig(fid, 1, d):.3e} "
            f"zero_recip_min_eig={hankel_min_eig(zer, 1, d):.3e}"
        )
    print("  Endpoint/support ratio estimates m_{k+1}/m_k:")
    print("    FID:", ", ".join(f"{float(x):.6f}" for x in fid_ratios[:8]))
    print("    zero:", ", ".join(f"{float(x):.6e}" for x in zero_ratios[:8]))
    fid_last = fid_ratios[-1]
    zero_last = zero_ratios[-1]
    gamma1 = mp.im(mp.zetazero(1))
    print(f"  FID endpoint tends to 1 because the integer divisor has support point y=1.")
    print(f"  zero endpoint tends to 1/gamma_1^2={float(gamma1**-2):.6e}.")
    print(f"  observed endpoint-compression factor at k=10: {float(fid_last / zero_last):.3f}")

    print()
    print("Finding:")
    print("  FID positivity is local excluded-volume: it verifies that the integer-divisor moments are Stieltjes.")
    print("  The zero divisor is also Stieltjes under RH, but it lives in a different support class: endpoint")
    print("  near 1/gamma_1^2 rather than 1. A successor FID route therefore needs a support-transport")
    print("  passport for the explicit-formula map, not another PSD check of zeta(odd).")


if __name__ == "__main__":
    main()
