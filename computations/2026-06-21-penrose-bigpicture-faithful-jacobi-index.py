import math


T = 10.0
h = 0.001
steps = int(T / h)


def constant_curvature(t):
    return 0.6


def pulsed_curvature(t):
    # Same rough integral over [0,10] as constant_curvature: 0.6*10 = 6.
    return 3.0 if (1.0 <= t <= 2.0 or 5.0 <= t <= 6.0) else 0.0


def alternating_curvature(t):
    # Same integral as above, but defocusing intervals change the zero count.
    if 1.0 <= t <= 2.0 or 5.0 <= t <= 6.0:
        return 4.0
    if 2.0 < t <= 3.0 or 6.0 < t <= 7.0:
        return -1.0
    return 0.0


def solve(kfun):
    y, v = 0.0, 1.0
    prev_y = y
    zeros = []
    integ = 0.0
    l2 = 0.0

    def rhs(t, yy, vv):
        return vv, -kfun(t) * yy

    for n in range(steps):
        t = n * h
        k = kfun(t)
        integ += k * h
        l2 += k * k * h
        k1y, k1v = rhs(t, y, v)
        k2y, k2v = rhs(t + 0.5 * h, y + 0.5 * h * k1y, v + 0.5 * h * k1v)
        k3y, k3v = rhs(t + 0.5 * h, y + 0.5 * h * k2y, v + 0.5 * h * k2v)
        k4y, k4v = rhs(t + h, y + h * k3y, v + h * k3v)
        y_next = y + h * (k1y + 2 * k2y + 2 * k3y + k4y) / 6
        v_next = v + h * (k1v + 2 * k2v + 2 * k3v + k4v) / 6
        if n > 0 and prev_y * y_next < 0:
            zeros.append(t)
        prev_y = y_next
        y, v = y_next, v_next
    return {"zeros": zeros, "integral": integ, "l2": l2, "final": (y, v)}


profiles = {
    "constant": constant_curvature,
    "pulsed": pulsed_curvature,
    "alternating": alternating_curvature,
}

print("Jacobi conjugate point index vs curvature summaries")
for name, kfun in profiles.items():
    out = solve(kfun)
    print(
        f"{name:11s} intK={out['integral']:.4f} l2K={out['l2']:.4f} "
        f"conjugate_count={len(out['zeros'])} zeros={[round(z, 3) for z in out['zeros']]} "
        f"final_y={out['final'][0]:+.6f}"
    )
