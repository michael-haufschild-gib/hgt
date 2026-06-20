import argparse
import math

import mpmath as mp
import numpy as np
from scipy.ndimage import minimum_filter
from scipy.spatial import Voronoi


QC = 3.81


def zeta(s):
    return mp.fp.zeta(s)


def gamma_factor(s):
    return mp.fp.power(mp.pi, -s / 2) * mp.fp.gamma(s / 2)


def completed_zeta(s):
    return gamma_factor(s) * zeta(s)


def finite_euler(s, primes=(2, 3, 5, 7, 11, 13, 17, 19)):
    out = 1.0 + 0j
    for p in primes:
        out *= 1.0 / (1.0 - mp.fp.power(p, -s))
    return out


def sine_control(s):
    return mp.fp.sin(s)


FUNCTIONS = {
    "lambda": completed_zeta,
    "zeta": zeta,
    "gamma-factor": gamma_factor,
    "finite-euler": finite_euler,
    "sine": sine_control,
}


def logabs_field(func, sigma_min, sigma_max, t_min, t_max, grid):
    sigmas = np.linspace(sigma_min, sigma_max, grid)
    ts = np.linspace(t_min, t_max, grid)
    field = np.empty((grid, grid), dtype=float)
    for j, t in enumerate(ts):
        for i, sigma in enumerate(sigmas):
            val = complex(func(complex(float(sigma), float(t))))
            field[j, i] = math.log(abs(val) + 1e-30)
    return sigmas, ts, field


def local_well_points(field, count):
    footprint = minimum_filter(field, size=3, mode="nearest")
    candidates = np.argwhere(field <= footprint + 1e-14)
    if len(candidates) < count:
        flat = np.argsort(field.ravel())[:count]
        candidates = np.column_stack(np.unravel_index(flat, field.shape))
    else:
        order = np.argsort(field[candidates[:, 0], candidates[:, 1]])
        candidates = candidates[order[:count]]

    height, width = field.shape
    pts = np.column_stack(
        [
            (candidates[:, 1] + 0.5) / width,
            (candidates[:, 0] + 0.5) / height,
        ]
    )
    # Jitter exact pixel ties without changing the geometric signal.
    return (pts + 1e-6 * np.arange(len(pts))[:, None]) % 1.0


def polygon_area_perimeter(poly):
    x = poly[:, 0]
    y = poly[:, 1]
    area = 0.5 * abs(np.dot(x, np.roll(y, -1)) - np.dot(y, np.roll(x, -1)))
    perimeter = np.linalg.norm(poly - np.roll(poly, -1, axis=0), axis=1).sum()
    return area, perimeter


def shape_index_and_edges(points):
    images = []
    ids = []
    central = []
    n = len(points)
    for sx in (-1, 0, 1):
        for sy in (-1, 0, 1):
            start = len(images)
            images.extend((points + np.array([sx, sy])).tolist())
            ids.extend(range(n))
            if sx == 0 and sy == 0:
                central = list(range(start, start + n))

    images = np.array(images)
    ids = np.array(ids)
    central_set = set(central)
    vor = Voronoi(images)

    q = np.zeros(n, dtype=float)
    for local_id, image_idx in enumerate(central):
        region = vor.regions[vor.point_region[image_idx]]
        if -1 in region or len(region) == 0:
            raise RuntimeError("periodic replication was insufficient for a bounded central cell")
        poly = vor.vertices[region]
        area, perimeter = polygon_area_perimeter(poly)
        q[local_id] = perimeter / np.sqrt(max(area, 1e-18))

    edges = set()
    for a, b in vor.ridge_points:
        if a not in central_set and b not in central_set:
            continue
        u = int(ids[a])
        v = int(ids[b])
        if u != v:
            edges.add((u, v) if u < v else (v, u))
    return q, edges


def jaccard_churn(edges_a, edges_b):
    union = edges_a | edges_b
    if not union:
        return 0.0
    return 1.0 - len(edges_a & edges_b) / len(union)


def cloud(func, args, t_offset):
    _, _, field = logabs_field(
        func,
        args.sigma_min,
        args.sigma_max,
        args.t_min + t_offset,
        args.t_max + t_offset,
        args.grid,
    )
    return local_well_points(field, args.wells)


def ascii_field(field, bins=36):
    chars = " .:-=+*#%@"
    small = field[:: max(1, field.shape[0] // bins), :: max(1, field.shape[1] // bins)]
    lo, hi = np.quantile(small, [0.05, 0.95])
    scaled = np.clip((small - lo) / max(hi - lo, 1e-12), 0.0, 1.0)
    rows = []
    for row in scaled:
        rows.append("".join(chars[int(x * (len(chars) - 1))] for x in row))
    return "\n".join(rows)


def run_one(name, args):
    func = FUNCTIONS[name]
    _, _, base_field = logabs_field(func, args.sigma_min, args.sigma_max, args.t_min, args.t_max, args.grid)
    base = local_well_points(base_field, args.wells)
    q, edges = shape_index_and_edges(base)

    rows = []
    for kick in args.kicks:
        kicked = cloud(func, args, kick)
        _, kicked_edges = shape_index_and_edges(kicked)
        rows.append((kick, float(q.mean()), float(np.mean(q > QC)), jaccard_churn(edges, kicked_edges)))
    return rows, base_field


def main():
    parser = argparse.ArgumentParser(description="Visual shape-index jamming probe on HT continuum log|f(s)| wells.")
    parser.add_argument("--functions", default="lambda,zeta,gamma-factor,finite-euler,sine")
    parser.add_argument("--sigma-min", type=float, default=0.15)
    parser.add_argument("--sigma-max", type=float, default=0.85)
    parser.add_argument("--t-min", type=float, default=14.0)
    parser.add_argument("--t-max", type=float, default=84.0)
    parser.add_argument("--grid", type=int, default=90)
    parser.add_argument("--wells", type=int, default=48)
    parser.add_argument("--kicks", type=float, nargs="*", default=[0.0, 0.2, 0.5, 1.0, 2.0, 3.5, 5.0])
    parser.add_argument("--show-ascii", action="store_true")
    args = parser.parse_args()

    names = [name.strip() for name in args.functions.split(",") if name.strip()]
    print("STEP8/9 HT landscape jamming probe")
    print("NODE constraint kept: shape-index q=P/sqrt(A) and edge churn of local packing")
    print("HT change: tissue cell centers -> local wells of continuum log|f(s)| on a complex window")
    print("method #5 applied: make it visual via scalar field wells and optional ASCII field")
    print(f"window: sigma=[{args.sigma_min},{args.sigma_max}], t=[{args.t_min},{args.t_max}], grid={args.grid}, wells={args.wells}")
    print()

    for name in names:
        rows, field = run_one(name, args)
        print(f"function={name}")
        print("kick    mean_q  frac_q>qc  edge_churn")
        for kick, mean_q, frac, churn in rows:
            print(f"{kick:5.2f}  {mean_q:6.3f}   {frac:7.3f}    {churn:7.3f}")
        if args.show_ascii:
            print("visual log|f| field:")
            print(ascii_field(field))
        print()


if __name__ == "__main__":
    main()
