#!/usr/bin/env python3
"""(CR-density) decisive probe — the open core of MID-central (task #130/#163).

QUESTION reasoning cannot settle: do the zeros of the naked partial sum
F_N(s) = Σ_{n≤N} n^{-s} CONCENTRATE at σ = 1/2 at scale 1/log N (which would
make ε(c) NOT → 0, threatening CR-density), or is their σ-density bounded
near 1/2 (CR-density holds)?

PRE-REGISTERED PREDICTIONS (before run):
  P-CR1 (prior 0.70): the count of F_N zeros with β−1/2 ∈ (0, c/log N],
        γ ∈ [T,T+U], divided by U·log N, is ≈ linear in c with slope O(1) —
        i.e. ε(c) ≈ κ·c, κ bounded, NO 1/log N blow-up ⟹ CR-density HOLDS.
  P-CR2 (prior 0.55): the empirical σ-density of zeros is CONTINUOUS across
        σ=1/2 (no spike) — measured as ratio ρ(near)/ρ(far) ≈ O(1).
  P-CR3 (prior 0.40): slope κ is roughly N-independent (the ε(c) uniformity
        CR-density needs). If κ GROWS with N, CR-density's uniform form fails
        and the open core is harder than the variance route suggests.

Falsification of P-CR1/P-CR3 = CR-density is false or much harder; a genuine
negative result on the open core (publishable either way).

Carrier: F_N via mpmath; zeros by argument-principle winding on σ-strips +
Newton refine. Heights chosen so N = floor(sqrt(T/2pi)) sits in a target band.
"""
import sys
from mpmath import mp, mpc, mpf, pi, sqrt, floor, log, findroot, re, im, fabs

mp.dps = 25


def make_FN(N):
    def FN(s):
        return sum(mpf(n) ** (-s) for n in range(1, N + 1))
    return FN


def winding(g, s_lo, s_hi, t_lo, t_hi, m=200):
    """Argument-principle winding number of g over the rectangle."""
    pts = []
    for k in range(m):
        pts.append(mpc(s_lo + (s_hi - s_lo) * k / m, t_lo))
    for k in range(m):
        pts.append(mpc(s_hi, t_lo + (t_hi - t_lo) * k / m))
    for k in range(m):
        pts.append(mpc(s_hi - (s_hi - s_lo) * k / m, t_hi))
    for k in range(m):
        pts.append(mpc(s_lo, t_hi - (t_hi - t_lo) * k / m))
    pts.append(pts[0])
    tot = mpf(0)
    prev = g(pts[0])
    for p in pts[1:]:
        cur = g(p)
        # accumulate arg change
        d = cur / prev
        tot += mp.atan2(im(d), re(d))
        prev = cur
    return int(round(float(tot / (2 * pi))))


def count_zeros_in_sigma_band(FN, sig_lo, sig_hi, T, U):
    """Count zeros of FN with re in (sig_lo, sig_hi], im in [T, T+U]."""
    return winding(FN, sig_lo, sig_hi, T, T + U)


def probe(N, U=mpf(40)):
    FN = make_FN(N)
    T = mpf(2) * pi * (N + mpf('0.5')) ** 2  # matched-regime height
    L = float(log(N))
    half = mpf('0.5')
    # total zeros in a wide strip [0.2, 0.8] for normalization
    tot = count_zeros_in_sigma_band(FN, mpf('0.2'), mpf('0.8'), T, U)
    rows = []
    for cfac in [0.5, 1.0, 2.0, 4.0]:
        c = mpf(cfac)
        width = c / L
        cnt = count_zeros_in_sigma_band(FN, half, half + width, T, U)
        # normalized: cnt / (U log N)
        norm = float(cnt) / float(U * L)
        rows.append((cfac, int(cnt), norm))
    # far-band density for continuity check: same width up at sigma=0.65
    cnt_far = count_zeros_in_sigma_band(FN, mpf('0.65'),
                                        mpf('0.65') + mpf('1.0') / L, T, U)
    cnt_near = count_zeros_in_sigma_band(FN, half, half + mpf('1.0') / L, T, U)
    return T, L, tot, rows, int(cnt_near), int(cnt_far)


if __name__ == '__main__':
    print("N    T          logN   total  [c: count norm=cnt/(UlogN)]           near/far(w=1/logN)")
    slopes = []
    for N in [12, 20, 28, 40]:
        T, L, tot, rows, near, far = probe(N)
        rowstr = "  ".join(f"c={r[0]}:{r[1]}({r[2]:.4f})" for r in rows)
        # slope estimate: norm/c averaged
        kappa = sum(r[2] / r[0] for r in rows) / len(rows)
        slopes.append((N, kappa))
        print(f"{N:<4d} {float(T):<10.1f} {L:.3f}  {tot:<5d}  {rowstr}   near={near} far={far}  kappa~{kappa:.4f}")
        sys.stdout.flush()
    print("\nkappa by N (P-CR3: roughly constant ⟹ uniform CR-density):")
    for N, k in slopes:
        print(f"  N={N}: kappa={k:.4f}")
    print("done")
