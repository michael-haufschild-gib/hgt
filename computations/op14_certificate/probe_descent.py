#!/usr/bin/env python3
"""Doc-14 certificate computation, part 1 (float probe): the Koenigs edge profile
r(t) = |L_c(gamma_c(t))| on the dyadic edge annulus [t0/2, t0], t0 = 3/64, c = 1/5.

- gamma at dyadic angles m/2^K: the doubling orbit of a dyadic angle terminates at 0,
  so the pullback chain anchors EXACTLY at beta and applies K branch steps (bits of m,
  LSB first).  Branch: upper preimage = principal sqrt of (z - c) sign-fixed to
  Im >= 0; digit 1 takes the negative.
- r via the telescope r = lim lambda^n |gamma(t/2^n) - beta| (stable: lambda^n cancels
  the pullback contraction).
- Descent spectrum: (O) fails at level sigma' iff some running-max descent straddles
  sigma'; bad levels = union of (r[i], runmax[i]) over descent indices i.  We track
  the bad-level set and the clean gaps as K grows, then zoom at the widest gap's
  crossing to probe micro-descent renewal (the truth question for doc 14).
"""
import numpy as np

C = 0.2  # 1/5 up to 1 ulp; probe is float anyway
SQ = np.sqrt(1 - 4 * C)
BETA = (1 + SQ) / 2
LAM = 2 * BETA
T0_NUM, T0_LOG = 3, 6  # t0 = 3/64


def gamma_dyadic(m, K, extra=0):
    """gamma(m/2^K) then `extra` more zero-digit pullbacks; returns final z array."""
    z = np.full(m.shape, BETA, dtype=np.complex128)
    for j in range(K):
        bit = (m >> j) & 1
        s = np.sqrt(z - C)
        s = np.where(s.imag >= 0, s, -s)  # upper preimage
        z = np.where(bit == 0, s, -s)
    for _ in range(extra):
        s = np.sqrt(z - C)
        z = np.where(s.imag >= 0, s, -s)  # always upper (angles in (0,1/4))
    return z


def r_profile(m, K, N=40):
    zN = gamma_dyadic(m, K, extra=N)
    lam_pow = LAM ** N
    return np.abs(lam_pow * (zN - BETA))


def descent_analysis(r):
    runmax = np.maximum.accumulate(r)
    d = runmax - r
    bad = d > 1e-12
    intervals = []
    for lo, hi in zip(r[bad], runmax[bad]):
        intervals.append((lo, hi))
    # merge
    intervals.sort()
    merged = []
    for lo, hi in intervals:
        if merged and lo <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(merged[-1][1], hi))
        else:
            merged.append((lo, hi))
    return runmax, d, merged


def gaps_from_bad(merged, lo_all, hi_all):
    gaps = []
    prev = lo_all
    for lo, hi in merged:
        if lo > prev:
            gaps.append((prev, lo))
        prev = max(prev, hi)
    if hi_all > prev:
        gaps.append((prev, hi_all))
    return gaps


def main():
    # self-tests
    K = 20
    m14 = np.array([1 << (K - 2)], dtype=np.int64)  # angle 1/4
    g14 = gamma_dyadic(m14, K)[0]
    print(f"self-test gamma(1/4) = {g14:.12f}  vs  i*sqrt(beta+c) = {1j*np.sqrt(BETA+C):.12f}")
    mt0 = np.array([T0_NUM << (K - T0_LOG)], dtype=np.int64)
    mt0h = np.array([T0_NUM << (K - T0_LOG - 1)], dtype=np.int64)
    rt0 = r_profile(mt0, K)[0]
    rt0h = r_profile(mt0h, K)[0]
    print(f"self-test r(t0)/r(t0/2) = {rt0/rt0h:.12f}  vs  lambda = {LAM:.12f}")
    print(f"r(t0) = {rt0:.6f}   r(t0/2) = {rt0h:.6f}   lambda^2 = {LAM**2:.6f}")
    print()

    # descent spectrum vs depth on the edge annulus [3/128, 3/64]
    summary = {}
    for K in (14, 16, 18, 20, 22, 24):
        m_lo = T0_NUM << (K - T0_LOG - 1)
        m_hi = T0_NUM << (K - T0_LOG)
        m = np.arange(m_lo, m_hi + 1, dtype=np.int64)
        r = r_profile(m, K)
        runmax, d, merged = descent_analysis(r)
        gaps = gaps_from_bad(merged, r[0], r[-1])
        gaps.sort(key=lambda g: g[1] - g[0], reverse=True)
        bad_measure = sum(hi - lo for lo, hi in merged)
        summary[K] = (r.min(), r.max(), d.max(), bad_measure, gaps[:4])
        print(f"K={K:2d}  pts={len(m):7d}  Rmin={r.min():.6f} Rmax={r.max():.6f} "
              f"maxdesc={d.max():.3e} badmeas={bad_measure:.5f} "
              f"top gaps={[(round(a,5), round(b,5)) for a,b in gaps[:4]]}")

    # widest gap at deepest K
    K = 24
    m_lo = T0_NUM << (K - T0_LOG - 1)
    m_hi = T0_NUM << (K - T0_LOG)
    m = np.arange(m_lo, m_hi + 1, dtype=np.int64)
    r = r_profile(m, K)
    runmax, d, merged = descent_analysis(r)
    gaps = gaps_from_bad(merged, r[0], r[-1])
    gaps.sort(key=lambda g: g[1] - g[0], reverse=True)
    glo, ghi = gaps[0]
    print(f"\nwidest clean gap at K=24: [{glo:.6f}, {ghi:.6f}]  width {ghi-glo:.6f}")
    mid = (glo + ghi) / 2
    icross = int(np.searchsorted(runmax, mid))
    tcross_num = int(m[icross])
    print(f"upward crossing of gap-mid at t = {tcross_num}/2^{K} = {tcross_num/2**K:.8f}")

    # zoom: micro-descent renewal at the crossing
    print("\nzoom at the crossing (local descents straddling the gap):")
    for Kz in (28, 32, 36, 40):
        shift = Kz - K
        center = tcross_num << shift
        half = 8 << shift  # window +- 8 cells of level K
        mz = np.arange(center - half, center + half + 1, dtype=np.int64)
        rz = r_profile(mz, Kz)
        rmz = np.maximum.accumulate(rz)
        dz = rmz - rz
        # descents straddling the gap band
        in_gap = (rz < ghi) & (rmz > glo)
        straddle = dz[in_gap & (dz > 1e-13)]
        maxstr = straddle.max() if straddle.size else 0.0
        print(f"  Kz={Kz}: pts={len(mz)} local maxdesc={dz.max():.3e} "
              f"max gap-straddling desc={maxstr:.3e} "
              f"local r-range=[{rz.min():.6f},{rz.max():.6f}]")

    # single-band placement feasibility (doc-14 constants)
    Rmin, Rmax = summary[24][0], summary[24][1]
    print(f"\nband placement: Rmax/Rmin = {Rmax/Rmin:.4f}  vs lambda = {LAM:.4f}, "
          f"lambda^2 = {LAM**2:.4f}")
    lo_need, hi_need = Rmax / LAM, LAM * Rmin
    print(f"meta-window for single-band (Rmax/lam, lam*Rmin) = ({lo_need:.6f}, {hi_need:.6f})")
    # gaps inside the meta-window
    for glo2, ghi2 in gaps[:6]:
        a, b = max(glo2, lo_need), min(ghi2, hi_need)
        if b > a:
            sig = (a + b) / 2 / LAM
            g = (b - a) / (b + a)
            print(f"  usable gap [{a:.6f},{b:.6f}] -> sigma={sig:.6f} g={g:.5f} (k0=1)")


if __name__ == "__main__":
    main()
