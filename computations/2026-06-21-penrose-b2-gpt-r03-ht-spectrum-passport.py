#!/usr/bin/env python3
import itertools

import mpmath as mp


def best_relation(values, labels, H=12):
    n = len(values)
    split = n // 2
    left = []
    for coeffs in itertools.product(range(-H, H + 1), repeat=split):
        if all(c == 0 for c in coeffs):
            continue
        s = sum(c * v for c, v in zip(coeffs, values[:split]))
        left.append((s, coeffs))
    left.sort(key=lambda x: x[0])
    best = (mp.inf, None)
    for coeffs_r in itertools.product(range(-H, H + 1), repeat=n - split):
        if all(c == 0 for c in coeffs_r):
            continue
        sr = sum(c * v for c, v in zip(coeffs_r, values[split:]))
        target = -sr
        lo, hi = 0, len(left)
        while lo < hi:
            mid = (lo + hi) // 2
            if left[mid][0] < target:
                lo = mid + 1
            else:
                hi = mid
        for j in (lo - 2, lo - 1, lo, lo + 1, lo + 2):
            if 0 <= j < len(left):
                total = left[j][0] + sr
                coeffs = left[j][1] + coeffs_r
                if any(c != 0 for c in coeffs) and abs(total) < best[0]:
                    best = (abs(total), coeffs)
    residual, coeffs = best
    relation = " + ".join(f"{c}*{lab}" for c, lab in zip(coeffs, labels) if c)
    return residual, relation, coeffs


def rank2(vs, tol=1e-12):
    # Simple 2-number Q-rank proxy: no small integer relation a*x+b*y with |a|,|b|<=80.
    x, y = vs
    best = min(
        abs(a * x + b * y)
        for a in range(-80, 81)
        for b in range(-80, 81)
        if (a, b) != (0, 0)
    )
    return 2 if best > tol else 1, best


def main():
    mp.mp.dps = 80
    print("NODE test: conformal-block decomposition depends on allowed spectrum")
    print("  Same external fields can be expanded in different channels only after declaring")
    print("  the allowed internal representations; channel labels alone are not the full correlator.")

    print()
    print("ResearchNode mutation: HT/value detector spectrum passport")
    x = mp.pi
    y = x ** 2
    l2 = mp.log(2)
    l3 = mp.log(3)
    one = mp.mpf(1)

    for label, pair in [("dependent-control (pi,pi^2)", (x, y)), ("prime-log pair (log2,log3)", (l2, l3))]:
        r, best = rank2(pair)
        print(f"  degree-1 rank proxy {label}: rank={r}, best_small_linear_residual={mp.nstr(best, 8)}")

    dep_deg1 = ([one, x, y], ["1", "x", "y"])
    dep_deg2 = ([one, x, y, x * x, x * y, y * y], ["1", "x", "y", "x^2", "xy", "y^2"])
    log_deg2 = ([one, l2, l3, l2 * l2, l2 * l3, l3 * l3], ["1", "l2", "l3", "l2^2", "l2*l3", "l3^2"])

    for name, (vals, labels), H in [
        ("dependent degree-1 spectrum", dep_deg1, 20),
        ("dependent degree-2 spectrum", dep_deg2, 4),
        ("prime-log degree-2 spectrum", log_deg2, 12),
    ]:
        residual, relation, coeffs = best_relation(vals, labels, H=H)
        print(f"  {name}: H={H}, best_residual={mp.nstr(residual, 18)}, relation={relation}")

    print()
    print("Finding:")
    print("  A value/HT detector needs a spectrum-completion passport. Degree-1 rank can be identical")
    print("  for an algebraically dependent control and for the prime-log pair; the dependency appears")
    print("  only when the allowed spectrum includes the relevant monomial. Without declaring the")
    print("  spectrum closure, the detector is just a chosen-channel rank test.")


if __name__ == "__main__":
    main()
