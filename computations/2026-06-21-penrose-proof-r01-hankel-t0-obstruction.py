#!/usr/bin/env python3
import math

try:
    import mpmath as mp
except ImportError:  # pragma: no cover
    mp = None


def partial_moment(N, k):
    if k == 0:
        return float(N)
    return sum((1.0 / (n * n)) ** k for n in range(1, N + 1))


def det2(a, b, c):
    return a * c - b * b


def main():
    print("ResearchNode: prove uniform all-order PSD for [T_{i+j}]")
    print("NODE constraint: white-noise covariance can be positive only as a generalized object,")
    print("not as an ordinary trace-class/function-valued covariance.")
    print()
    print("Split subclaims for reciprocal seam moments:")
    print("  A. T_0 is finite.")
    print("  B. T_k for k>=1 are finite.")
    print("  C. shifted Hankels [T_{i+j+1}] can be ordinary finite PSD matrices.")
    print("  D. unshifted Hankels [T_{i+j}] with i,j=0 are ordinary finite PSD matrices.")
    print()
    print("Toy seam atom model y_n=1/n^2: infinite mass accumulating at 0, finite positive moments.")
    print("N | T0(N) | T1(N) | T2(N) | det [[T1,T2],[T2,T3]]")
    print("--|-------|-------|-------|-------------------------")
    for N in [10, 100, 1000, 10000]:
        T0 = partial_moment(N, 0)
        T1 = partial_moment(N, 1)
        T2 = partial_moment(N, 2)
        T3 = partial_moment(N, 3)
        print(f"{N:5d} | {T0:5.0f} | {T1:7.5f} | {T2:7.5f} | {det2(T1, T2, T3):23.12f}")
    print()
    if mp is not None:
        print("Limits for toy model:")
        print(f"  T1 -> zeta(2) = {float(mp.zeta(2)):.12f}")
        print(f"  T2 -> zeta(4) = {float(mp.zeta(4)):.12f}")
        print("  T0 -> infinity")
        print()
    print("Quadratic-form boundary:")
    print("  p(y)=1 gives sum 1 = T0 = infinity.")
    print("  p(y)=y gives sum y^2 = T2 < infinity.")
    print()
    print("Finding:")
    print("  The unshifted Hankel tower [T_{i+j}] in the proof route is not an ordinary")
    print("  finite Stieltjes moment matrix unless T0 is replaced, regularized, or the")
    print("  domain is restricted to test polynomials vanishing at 0. The natural ordinary")
    print("  finite tower is the shifted one [T_{i+j+1}], corresponding to the finite")
    print("  measure dnu=y dmu.")


if __name__ == "__main__":
    main()
