#!/usr/bin/env python3
"""Part 2: structure of the bad-level set.  Porous (clean sub-bands survive at every
scale => doc-14 TRUE with small g) vs dense (a micro-dip strip at every crossing =>
no clean band => doc-14 FALSE as formulated)."""
import numpy as np
from probe_descent import gamma_dyadic, r_profile, descent_analysis, gaps_from_bad, \
    BETA, LAM, T0_NUM, T0_LOG

def merged_measure(merged):
    return sum(hi - lo for lo, hi in merged)

def main():
    # global spectrum at K=26 (1.5M points)
    for K in (26,):
        m_lo = T0_NUM << (K - T0_LOG - 1)
        m_hi = T0_NUM << (K - T0_LOG)
        m = np.arange(m_lo, m_hi + 1, dtype=np.int64)
        r = r_profile(m, K)
        runmax, d, merged = descent_analysis(r)
        gaps = gaps_from_bad(merged, r[0], r[-1])
        gaps.sort(key=lambda g: g[1] - g[0], reverse=True)
        print(f"K={K}: pts={len(m)} maxdesc={d.max():.3e} badmeas={merged_measure(merged):.6f} "
              f"nstrips={len(merged)}")
        print(f"   top gaps: {[(round(a,6), round(b,6)) for a,b in gaps[:5]]}")
        widest = gaps[0]

    # fill-fraction zooms at three crossings: mid of widest K26 gap, and quartile levels
    K = 26
    levels = [ (widest[0]+widest[1])/2,
               r.min() + 0.25*(r.max()-r.min()),
               r.min() + 0.75*(r.max()-r.min()) ]
    for lev in levels:
        icross = int(np.searchsorted(runmax, lev))
        icross = min(icross, len(m)-1)
        tc = int(m[icross])
        print(f"\ncrossing of level {lev:.6f} at t={tc}/2^{K}:")
        for Kz in (30, 34, 38):
            shift = Kz - K
            center = tc << shift
            half = 64 << shift        # +-64 cells of level K=26
            mz = np.arange(center - half, center + half + 1, dtype=np.int64)
            rz = r_profile(mz, Kz)
            rmz, dz, mergedz = descent_analysis(rz)
            lo, hi = rz.min(), rz.max()
            bm = merged_measure(mergedz)
            frac = bm / (hi - lo) if hi > lo else 0.0
            widths = [b-a for a, b in mergedz]
            print(f"  Kz={Kz}: pts={len(mz)} level-range width={hi-lo:.3e} "
                  f"badmeas={bm:.3e} fill={frac:.4f} nstrips={len(mergedz)} "
                  f"maxstrip={max(widths) if widths else 0:.3e}")

    # descent-depth distribution at K=26: are dips discrete features?
    dd = d[d > 1e-12]
    if dd.size:
        qs = np.quantile(dd, [0.5, 0.9, 0.99, 1.0])
        print(f"\nK=26 descent depths: n={dd.size} median={qs[0]:.2e} "
              f"p90={qs[1]:.2e} p99={qs[2]:.2e} max={qs[3]:.2e}")

if __name__ == "__main__":
    main()
