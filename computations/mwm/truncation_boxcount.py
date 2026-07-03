#!/usr/bin/env python3
"""
(DISC-fin) task #136 step 2: box-count off-line zeros of g_N by winding number.
Boxes: sigma in [0.53, 1.35], t in [T0,T0+5] sweeping [200, 1030].
Winding of g_N along box boundary (arg-tracking, 160 pts/side, dps 25).
Boxes with winding != 0 are refined by Muller from the box center at dps 50.
PRE-REGISTERED: PL' (prior 0.7): >= 1 box with nonzero count in the sweep.
"""
from mpmath import mp, mpc, mpf, zeta, gamma as Gamma, pi, sin, floor, sqrt, fabs, arg, findroot, re, im

mp.dps = 25
i = mpc(0, 1)


def chix(s):
    return 2 ** s * pi ** (s - 1) * sin(pi * s / 2) * Gamma(1 - s)


def make_g(N):
    def g(s):
        a = sum(mpf(n) ** (-s) for n in range(1, N + 1))
        b = sum(mpf(n) ** (s - 1) for n in range(1, N + 1))
        return a + chix(s) * b
    return g


def winding(g, s_lo, s_hi, t_lo, t_hi, m=160):
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
    prev = arg(g(pts[0]))
    for p in pts[1:]:
        a = arg(g(p))
        d = a - prev
        while d > pi:
            d -= 2 * pi
        while d < -pi:
            d += 2 * pi
        tot += d
        prev = a
    return int(mp.nint(tot / (2 * pi)))


if __name__ == "__main__":
    hits = []
    T = mpf(200)
    while T < 1030:
        N = int(floor(sqrt(T / (2 * pi))))
        g = make_g(N)
        w = winding(g, mpf('0.53'), mpf('1.35'), T, T + 5)
        if w != 0:
            print(f"T=[{T},{T+5}] N={N}: winding = {w}  <-- HIT")
            hits.append((float(T), N, w))
        T += 5
    print("hits:", hits)
    if hits:
        mp.dps = 50
        T0, N, w = hits[0]
        g = make_g(N)
        # refine: subdivide in t by 1.0 and locate
        for tt in range(int(T0), int(T0) + 5):
            ww = winding(g, mpf('0.53'), mpf('1.35'), mpf(tt), mpf(tt + 1), m=200)
            if ww != 0:
                s0 = mpc('0.7', tt + mpf('0.5'))
                try:
                    r = findroot(g, s0, solver='muller', tol=mpf('1e-30'))
                    print(f"refined zero: {mp.nstr(re(r), 12)} + {mp.nstr(im(r), 14)} i, |g| = {mp.nstr(fabs(g(r)), 3)}")
                except Exception as e:
                    print(f"refine fail in [{tt},{tt+1}]: {e}")
    print("PL'", "PASS" if hits else "FAIL")
