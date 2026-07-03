#!/usr/bin/env python3.13
"""
P-B — Hermite cluster model at multiple zeros (doc 25 Thm B; task #135, MWM lane).

Pre-registered predictions (written BEFORE the first run):
  Setup: g_m(z) = (1 - z/x0)^m * cos(sqrt(z)), x0 = 9, tau = 2+3i (a=2, b=3),
    so |x0 - tau|^2 = 58. Sections A_d = J^d_g; rescaled Atilde(z) := A_d(z/d)
    = sum_j phi_d(j) c_j z^j with phi_d(j) = prod_{i<j}(1 - i/d), g = sum c_j z^j.
    sigma := x0/sqrt(d). Margin at a critical point z_c of Atilde (i.e. c = z_c/d
    of A_d):  margin = q * d^2 / (z_c^4 * E),
      q = a^2 + b^2 - 2*a*z_c + (1 - 1/d)*z_c^2,
      E = -Atilde''(z_c)/Atilde(z_c)      [exact electrostatic identity].
  Model (doc 25 Thm B): the m-fold zero splits at the SINGLE scale sigma into the
  probabilists'-Hermite configuration He_m((z - x0)/sigma).

  P-B1 (m=2): the two cluster zeros sit at x0 +- sigma:  halfgap*sqrt(d)/x0 -> 1.
  P-B2 (m=2): at the enclosed critical point (W_2 = 2 at u = 0):
      margin * 2*x0^2 / (58*d) -> 1.
  P-B3 (m=4): He_4 = u^4 - 6u^2 + 3, zeros +-0.74196, +-2.33441; critical points
      u = 0, +-sqrt(3), and W_4 = -He4''/He4 = 4 at ALL THREE. Hence at all three
      cluster critical points:  margin * 4*x0^2 / (58*d) -> 1.
  Expected convergence rate O(d^{-1/2}) in every ratio.

FAILURE of any ratio to approach 1 refutes Thm B's Hermite model; doc 25 is re-cut.
"""
from mpmath import mp, mpf, sqrt, cos, factorial

mp.dps = 200
X0 = mpf(9)
A, B = mpf(2), mpf(3)
Q0 = A * A + B * B          # |tau|^2 = 13
DIST2 = mpf(58)             # |x0 - tau|^2
JMAX = 240
DS = [100, 1000, 10000, 100000]


def coeffs(m):
    """Maclaurin coefficients c_j of (1 - z/x0)^m * cos(sqrt(z)), j <= JMAX."""
    # cos(sqrt(z)) = sum_k (-1)^k z^k / (2k)!
    cosc = [mpf(-1) ** k / factorial(2 * k) for k in range(JMAX + 1)]
    # (1 - z/x0)^m binomial coefficients
    from math import comb
    poly = [mpf(comb(m, i)) * (mpf(-1) / X0) ** i for i in range(m + 1)]
    c = [mpf(0)] * (JMAX + 1)
    for j in range(JMAX + 1):
        s = mpf(0)
        for i in range(min(m, j) + 1):
            s += poly[i] * cosc[j - i]
        c[j] = s
    return c


def section_coeffs(c, d):
    """Coefficients of Atilde(z) = sum phi_d(j) c_j z^j and its two derivatives."""
    a0 = []
    phi = mpf(1)
    for j in range(min(JMAX, d) + 1):
        a0.append(phi * c[j])
        phi *= (1 - mpf(j) / d)   # phi now = phi_d(j+1)
    a1 = [a0[j] * j for j in range(1, len(a0))]
    a2 = [a1[j] * j for j in range(1, len(a1))]
    return a0, a1, a2


def horner(a, z):
    v = mpf(0)
    for cj in reversed(a):
        v = v * z + cj
    return v


def newton(a, ap, z, steps=80):
    for _ in range(steps):
        f, fp = horner(a, z), horner(ap, z)
        dz = f / fp
        z = z - dz
        if abs(dz) < mpf(10) ** (-mp.dps + 40):
            break
    return z


def margin(z, a0, a2, d):
    E = -horner(a2, z) / horner(a0, z)
    q = Q0 - 2 * A * z + (1 - mpf(1) / d) * z * z
    return q * d * d / (z ** 4 * E)


print("== P-B1 / P-B2 : m = 2 ==")
c2 = coeffs(2)
for d in DS:
    a0, a1, a2 = section_coeffs(c2, d)
    sig = X0 / sqrt(d)
    zp = newton(a0, a1, X0 + sig)          # cluster zero right
    zm = newton(a0, a1, X0 - sig)          # cluster zero left
    zc = newton(a1, a2, X0)                # enclosed critical point
    halfgap = (zp - zm) / 2
    r1 = halfgap * sqrt(d) / X0
    r2 = margin(zc, a0, a2, d) * 2 * X0 ** 2 / (DIST2 * d)
    print(f"d={d:7d}  P-B1 gap-ratio={mp.nstr(r1, 8)}   P-B2 margin-ratio={mp.nstr(r2, 8)}")

print("== P-B3 : m = 4, three cluster critical points ==")
c4 = coeffs(4)
s3 = sqrt(mpf(3))
for d in DS:
    a0, a1, a2 = section_coeffs(c4, d)
    sig = X0 / sqrt(d)
    ratios = []
    for u in (-s3, mpf(0), s3):
        zc = newton(a1, a2, X0 + u * sig)
        ratios.append(margin(zc, a0, a2, d) * 4 * X0 ** 2 / (DIST2 * d))
    print(f"d={d:7d}  ratios(u=-sqrt3,0,+sqrt3) = "
          + "  ".join(mp.nstr(r, 8) for r in ratios))
