import numpy as np


def simulate(include_hidden=True, nx=1300, dt=0.012, steps=5200):
    x = np.linspace(-100.0, 360.0, nx)
    dx = x[1] - x[0]
    u = np.where(x < 0, 1.0, np.exp(-1.8 * x))
    v = 0.04 * np.where(x < 0, 1.0, np.exp(-0.8 * x)) if include_hidden else np.zeros_like(x)

    d_u, r_u = 0.45, 0.35
    d_v, r_v = 1.00, 1.05
    k_v = 0.05
    alpha = 0.22
    max_alpha = max(d_u, d_v) * dt / (dx * dx)
    if max_alpha > 0.5:
        raise RuntimeError("unstable explicit step")

    positions = []
    v_fraction_at_front = []
    times = []
    for n in range(steps):
        lap_u = np.empty_like(u)
        lap_v = np.empty_like(v)
        lap_u[1:-1] = u[:-2] - 2 * u[1:-1] + u[2:]
        lap_v[1:-1] = v[:-2] - 2 * v[1:-1] + v[2:]
        lap_u[[0, -1]] = 0.0
        lap_v[[0, -1]] = 0.0

        u += d_u * dt / (dx * dx) * lap_u + dt * (r_u * u * (1.0 - u) + alpha * v * (1.0 - u))
        if include_hidden:
            v += d_v * dt / (dx * dx) * lap_v + dt * r_v * v * (1.0 - v / k_v)
        u = np.clip(u, 0.0, 1.2)
        v = np.clip(v, 0.0, k_v * 1.2)

        if n % 20 == 0:
            total = u + v
            idx = np.where(total >= 0.04)[0]
            if len(idx) and idx[-1] + 1 < len(total):
                i = idx[-1]
                denom = total[i + 1] - total[i]
                frac = (0.04 - total[i]) / denom if abs(denom) > 1e-12 else 0.0
                pos = x[i] + frac * dx
                positions.append(pos)
                j = min(i + 1, len(x) - 1)
                v_fraction_at_front.append(float(v[j] / max(total[j], 1e-12)))
                times.append(n * dt)

    t = np.array(times)
    pos = np.array(positions)
    early = np.polyfit(t[8:25], pos[8:25], 1)[0]
    late = np.polyfit(t[-35:], pos[-35:], 1)[0]
    return {
        "early_speed": float(early),
        "late_speed": float(late),
        "bulk_v_fraction": float(np.mean(v[x < -20] / np.maximum(u[x < -20] + v[x < -20], 1e-12))),
        "front_v_fraction": float(np.mean(v_fraction_at_front[-35:])),
        "visual_bulk_u": float(np.mean(u[x < -20])),
        "visual_bulk_v": float(np.mean(v[x < -20])),
    }


def main():
    slow_formula = 2.0 * np.sqrt(0.45 * 0.35)
    hidden_formula = 2.0 * np.sqrt(1.0 * 1.05)
    print("NODE: hidden leading eigenmode selects multicomponent pulled-front speed")
    print("constraint: speed is selected by the leading-edge eigencomponent, not by visually dominant bulk amplitude")
    print(f"single visible component formula speed={slow_formula:.4f}; hidden component formula speed={hidden_formula:.4f}")
    print("case             early_speed  late_speed  bulk_v_frac  front_v_frac  bulk_u  bulk_v")
    for label, hidden in [("visible-only", False), ("hidden-mode", True)]:
        row = simulate(include_hidden=hidden)
        print(
            f"{label:14s}  {row['early_speed']:11.4f}  {row['late_speed']:10.4f}"
            f"  {row['bulk_v_fraction']:11.4f}  {row['front_v_fraction']:12.4f}"
            f"  {row['visual_bulk_u']:6.3f}  {row['visual_bulk_v']:6.3f}"
        )


if __name__ == "__main__":
    main()
