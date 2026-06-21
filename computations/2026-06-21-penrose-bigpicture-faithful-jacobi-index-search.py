import math


T = 10.0
h = 0.002
steps = int(T / h)
TARGET_INTEGRAL = 6.0


def solve(kfun):
    y, v = 0.0, 1.0
    prev_y = y
    zeros = []
    integ = 0.0

    def rhs(t, yy, vv):
        return vv, -kfun(t) * yy

    for n in range(steps):
        t = n * h
        integ += kfun(t) * h
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
    return integ, zeros, y


def pulse(start, width, amp):
    return lambda t: amp if start <= t <= start + width else 0.0


cases = []
for start in [0.0, 0.5, 1.0, 2.0, 4.0]:
    for width in [0.25, 0.5, 1.0, 2.0, 4.0]:
        amp = TARGET_INTEGRAL / width
        integ, zeros, final_y = solve(pulse(start, width, amp))
        cases.append((len(zeros), start, width, amp, integ, zeros, final_y))

cases.sort()
print("Equal-integral Jacobi pulse search: int K ~= 6")
for row in cases:
    count, start, width, amp, integ, zeros, final_y = row
    print(
        f"count={count} start={start:.2f} width={width:.2f} amp={amp:.3f} "
        f"intK={integ:.4f} zeros={[round(z, 3) for z in zeros]} final_y={final_y:+.4f}"
    )
