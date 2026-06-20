import numpy as np
from scipy.spatial import Voronoi


QC = 3.81


def triangular_lattice(nx=9, ny=9):
    pts = []
    for j in range(ny):
        for i in range(nx):
            pts.append(((i + 0.5 * (j % 2)) / nx, j / ny))
    return np.array(pts, dtype=float)


def jitter(points, amp, rng):
    return (points + rng.normal(scale=amp, size=points.shape)) % 1.0


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
        q[local_id] = perimeter / np.sqrt(area)

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


def trial(base, disorder, kick, rng):
    pts = jitter(base, disorder, rng)
    q, edges = shape_index_and_edges(pts)
    kicked = jitter(pts, kick, rng)
    _, edges_kicked = shape_index_and_edges(kicked)
    return float(q.mean()), float(np.mean(q > QC)), jaccard_churn(edges, edges_kicked)


def main():
    rng = np.random.default_rng(2246186626221576586)
    base = triangular_lattice()
    kick = 0.012
    disorders = [0.0, 0.01, 0.02, 0.03, 0.04, 0.055, 0.07, 0.09, 0.115]
    reps = 12

    print("NODE: local jamming/unjamming in tissue remodeling")
    print(f"constraint: mean shape index q=P/sqrt(A) crosses q_c≈{QC}; edge churn proxies T1 susceptibility")
    print("disorder  mean_q  frac_cells_q>qc  edge_churn_after_small_kick")
    rows = []
    for amp in disorders:
        vals = np.array([trial(base, amp, kick, rng) for _ in range(reps)])
        mean = vals.mean(axis=0)
        rows.append((amp, *mean))
        print(f"{amp:7.3f}  {mean[0]:6.3f}      {mean[1]:6.3f}                 {mean[2]:6.3f}")

    qs = np.array([r[1] for r in rows])
    churns = np.array([r[3] for r in rows])
    cross_idx = int(np.argmin(np.abs(qs - QC)))
    slope_idx = int(np.argmax(np.diff(churns)))
    print()
    print(f"nearest q_c crossing: disorder={rows[cross_idx][0]:.3f}, mean_q={rows[cross_idx][1]:.3f}")
    print(
        "largest churn jump: "
        f"{rows[slope_idx][0]:.3f}->{rows[slope_idx + 1][0]:.3f}, "
        f"churn {rows[slope_idx][3]:.3f}->{rows[slope_idx + 1][3]:.3f}"
    )


if __name__ == "__main__":
    main()
