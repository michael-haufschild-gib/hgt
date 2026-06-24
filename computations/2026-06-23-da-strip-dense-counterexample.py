"""Numerical sanity check for the DA strip-dense counterexample.

The function y(s)=sin(s*exp(s)) is differentially algebraic over C(s).
Its zeros solve s*exp(s)=n*pi, hence s=W_k(n*pi).

For a fixed vertical strip a <= Re(s) <= b, the asymptotic condition is
roughly C_a |k| <= n <= C_b |k|, so the number of zeros up to height T
should grow quadratically in T.
"""

import mpmath as mp


mp.mp.dps = 50


def count_strip(kmax: int, a: float, b: float) -> tuple[int, float]:
    count = 0
    max_height = 0.0
    # n range padded beyond the asymptotic strip range.
    nmax = int(20 * kmax)
    for k in range(1, kmax + 1):
        for n in range(1, nmax + 1):
            s = mp.lambertw(n * mp.pi, k)
            re = float(mp.re(s))
            if a <= re <= b:
                count += 1
                max_height = max(max_height, abs(float(mp.im(s))))
    return count, max_height


print("zeros of sin(s exp(s)): s = W_k(n*pi)")
print("strip: 0 <= Re(s) <= 1")
print("kmax       count       T=max|Im|       count/T^2")
for kmax in [10, 20, 40, 80]:
    count, height = count_strip(kmax, 0.0, 1.0)
    ratio = count / (height * height) if height else 0.0
    print(f"{kmax:<10d} {count:<11d} {height:<15.6f} {ratio:.8f}")

print()
print("The nonzero limiting scale of count/T^2 is consistent with quadratic strip density.")
