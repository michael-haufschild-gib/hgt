import numpy as np


def simulate_kpp(lam, d=1.0, r=1.0, nx=1400, dt=0.015, steps=4800):
    x = np.linspace(-100.0, 420.0, nx)
    dx = x[1] - x[0]
    u = np.where(x < 0, 1.0, np.exp(-lam * x))
    u = np.clip(u, 0.0, 1.0)
    positions = []
    times = []

    alpha = d * dt / (dx * dx)
    if alpha > 0.5:
        raise RuntimeError("unstable explicit diffusion step")

    for n in range(steps):
        lap = np.empty_like(u)
        lap[1:-1] = u[:-2] - 2 * u[1:-1] + u[2:]
        lap[0] = 0.0
        lap[-1] = 0.0
        u += alpha * lap + dt * r * u * (1.0 - u)
        u = np.clip(u, 0.0, 1.0)
        if n % 10 == 0:
            idx = np.where(u >= 0.5)[0]
            if len(idx) and idx[-1] + 1 < len(u):
                i = idx[-1]
                denom = u[i + 1] - u[i]
                frac = (0.5 - u[i]) / denom if abs(denom) > 1e-12 else 0.0
                positions.append(x[i] + frac * dx)
                times.append(n * dt)

    times = np.array(times)
    positions = np.array(positions)
    early = np.polyfit(times[5:20], positions[5:20], 1)[0]
    late = np.polyfit(times[-25:], positions[-25:], 1)[0]
    predicted = d * lam + r / lam if lam < np.sqrt(r / d) else 2.0 * np.sqrt(d * r)
    return early, late, predicted


def main():
    print("NODE: autocatalytic front transient speed depends on initial sharpness")
    print("constraint: leading-edge tail steepness selects speed until the universal KPP speed is reached")
    print("lambda  early_speed  late_speed  selected_speed_formula")
    for lam in [0.35, 0.5, 0.75, 1.0, 1.5, 2.5]:
        early, late, predicted = simulate_kpp(lam)
        print(f"{lam:5.2f}    {early:9.4f}  {late:9.4f}       {predicted:9.4f}")


if __name__ == "__main__":
    main()
