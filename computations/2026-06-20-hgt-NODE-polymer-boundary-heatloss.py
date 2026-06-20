import numpy as np


def simulate(cooling=0.0, nx=180, ny=46, steps=6200, dt=0.012):
    ambient = 0.0
    t = np.zeros((ny, nx), dtype=float)
    cure = np.zeros_like(t)
    t[:, :8] = 1.8
    alpha = 1.15
    heat_release = 3.4
    activation = 0.48
    diffusivity = 0.70
    dx = 1.0
    stable = diffusivity * dt / (dx * dx)
    if stable > 0.24:
        raise RuntimeError("unstable explicit 2D diffusion")

    peak = t.copy()
    for _ in range(steps):
        lap = np.zeros_like(t)
        lap[1:-1, 1:-1] = (
            t[1:-1, :-2] + t[1:-1, 2:] + t[:-2, 1:-1] + t[2:, 1:-1] - 4.0 * t[1:-1, 1:-1]
        )
        lap[:, 0] = lap[:, 1]
        lap[:, -1] = lap[:, -2]
        lap[0, :] = lap[1, :]
        lap[-1, :] = lap[-2, :]

        rate = alpha * np.maximum(t - activation, 0.0) * (1.0 - cure)
        cure += dt * rate
        cure = np.clip(cure, 0.0, 1.0)
        t += diffusivity * dt * lap + dt * heat_release * rate - 0.012 * dt * (t - ambient)
        if cooling:
            t[0, :] -= cooling * dt * (t[0, :] - ambient)
            t[-1, :] -= cooling * dt * (t[-1, :] - ambient)
            t[1, :] -= 0.5 * cooling * dt * (t[1, :] - ambient)
            t[-2, :] -= 0.5 * cooling * dt * (t[-2, :] - ambient)
        peak = np.maximum(peak, t)

    center = ny // 2
    boundary_band = np.r_[0:3, ny - 3 : ny]
    middle_x = slice(nx // 3, 2 * nx // 3)
    return {
        "cooling": cooling,
        "center_peak": float(peak[center, middle_x].mean()),
        "boundary_peak": float(peak[boundary_band, middle_x].mean()),
        "center_cure": float(cure[center, middle_x].mean()),
        "boundary_cure": float(cure[boundary_band, middle_x].mean()),
        "front_reach_center": int(np.sum(cure[center, :] > 0.6)),
        "front_reach_boundary": int(np.mean(np.sum(cure[boundary_band, :] > 0.6, axis=1))),
    }


def main():
    print("NODE: polymerization front boundary heat-loss constraint")
    print("constraint: boundaries can peak cooler than centerline, causing spatially varying cure despite one front")
    print("cooling  center_peak  boundary_peak  center_cure  boundary_cure  reach_center  reach_boundary")
    for cooling in [0.0, 0.03, 0.08, 0.16, 0.28, 0.42]:
        row = simulate(cooling=cooling)
        print(
            f"{cooling:7.2f}  {row['center_peak']:11.4f}  {row['boundary_peak']:13.4f}"
            f"  {row['center_cure']:11.4f}  {row['boundary_cure']:13.4f}"
            f"  {row['front_reach_center']:12d}  {row['front_reach_boundary']:14d}"
        )


if __name__ == "__main__":
    main()
