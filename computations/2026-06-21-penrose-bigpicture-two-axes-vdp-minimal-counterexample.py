import math


h = 0.001
T = 20.0
steps = int(T / h)
mu = 1.0


def rk4(state, gain):
    x, v = state

    def f(s):
        xx, vv = s
        return vv, mu * gain(xx) * vv - xx

    k1 = f((x, v))
    k2 = f((x + 0.5 * h * k1[0], v + 0.5 * h * k1[1]))
    k3 = f((x + 0.5 * h * k2[0], v + 0.5 * h * k2[1]))
    k4 = f((x + h * k3[0], v + h * k3[1]))
    return (
        x + h * (k1[0] + 2 * k2[0] + 2 * k3[0] + k4[0]) / 6,
        v + h * (k1[1] + 2 * k2[1] + 2 * k3[1] + k4[1]) / 6,
    )


cases = {
    "vdp_sign_balance": lambda x: 1 - x * x,
    "all_negative_resistance": lambda x: 1 + x * x,
    "all_positive_resistance": lambda x: -(1 + x * x),
}

print("Minimal counterexample to 'negative resistance alone stabilizes'")
for name, gain in cases.items():
    state = (0.1, 0.0)
    max_radius = 0.0
    escaped_at = None
    net_energy = 0.0
    for n in range(steps):
        x, v = state
        radius = math.sqrt(x * x + v * v)
        max_radius = max(max_radius, radius)
        net_energy += mu * gain(x) * v * v * h
        if radius > 50 and escaped_at is None:
            escaped_at = n * h
            break
        state = rk4(state, gain)
    x, v = state
    print(
        f"{name:24s} final_radius={math.sqrt(x*x+v*v):10.6f} "
        f"max_radius={max_radius:10.6f} net_dE={net_energy:+12.6f} "
        f"escaped_at={escaped_at}"
    )
