import math
import numpy as np


def wavevectors(degrees):
    return np.array(
        [
            [math.cos(math.radians(theta)), math.sin(math.radians(theta))]
            for theta in degrees
        ],
        dtype=float,
    )


def planform(kvecs, grid=81):
    xs = np.linspace(0, 2 * math.pi, grid)
    ys = np.linspace(0, 2 * math.pi, grid)
    field = np.zeros((grid, grid))
    for i, x in enumerate(xs):
        for j, y in enumerate(ys):
            p = np.array([x, y])
            field[i, j] = sum(math.cos(float(k @ p)) for k in kvecs)
    return field


def rotation_error(kvecs, angle_deg, grid=81):
    # Compare sampled fields after rotating wavevectors rather than interpolating the grid.
    theta = math.radians(angle_deg)
    rot = np.array([[math.cos(theta), -math.sin(theta)], [math.sin(theta), math.cos(theta)]])
    f0 = planform(kvecs, grid)
    f1 = planform((rot @ kvecs.T).T, grid)
    return float(np.linalg.norm(f0 - f1) / np.linalg.norm(f0))


cases = {
    "hexagonal_120_triad": [0, 120, 240],
    "three_equal_nonclosing": [0, 90, 210],
    "roll_like_duplicate": [0, 0, 180],
}

print("Benard hexagon triad: scalar passport vs oriented closure")
for name, angles in cases.items():
    k = wavevectors(angles)
    closure = np.linalg.norm(k.sum(axis=0))
    lengths = np.linalg.norm(k, axis=1)
    energy = float(np.sum(lengths ** 2))
    avg_len = float(np.mean(lengths))
    sym60 = rotation_error(k, 60)
    sym120 = rotation_error(k, 120)
    field = planform(k)
    print(
        f"{name:24s} angles={angles!s:16s} closure={closure:.8f} "
        f"energy={energy:.3f} avg_len={avg_len:.3f} "
        f"rot60_err={sym60:.6f} rot120_err={sym120:.6f} "
        f"field_mean={field.mean():+.6f} field_std={field.std():.6f}"
    )
