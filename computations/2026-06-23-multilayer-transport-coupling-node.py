#!/usr/bin/env python3
"""Workflow W7: multilayer transport coupling missed by single-layer metrics."""

from __future__ import annotations

import argparse
import math
import random
from collections import deque

import mpmath as mp


Graph = dict[int, set[int]]


def add_edge(g: Graph, a: int, b: int) -> None:
    g.setdefault(a, set()).add(b)
    g.setdefault(b, set()).add(a)


def make_layer(n: int, hubs: list[int], seed: int) -> Graph:
    rng = random.Random(seed)
    g: Graph = {i: set() for i in range(n)}
    for i in range(n):
        hub = rng.choice(hubs)
        add_edge(g, i, hub)
        if rng.random() < 0.35:
            add_edge(g, i, rng.randrange(n))
    for a in hubs:
        for b in hubs:
            if a < b:
                add_edge(g, a, b)
    return g


def reachable_count(g: Graph, start: int, removed: set[int]) -> int:
    if start in removed:
        return 0
    seen = {start}
    q: deque[int] = deque([start])
    while q:
        node = q.popleft()
        for nxt in g.get(node, ()):
            if nxt not in removed and nxt not in seen:
                seen.add(nxt)
                q.append(nxt)
    return len(seen)


def giant_fraction(g: Graph, removed: set[int]) -> float:
    active = [node for node in g if node not in removed]
    if not active:
        return 0.0
    best = 0
    checked: set[int] = set()
    for node in active:
        if node in checked:
            continue
        count = reachable_count(g, node, removed)
        best = max(best, count)
        # Cheaply mark by a second BFS.
        q = deque([node])
        checked.add(node)
        while q:
            cur = q.popleft()
            for nxt in g.get(cur, ()):
                if nxt not in removed and nxt not in checked:
                    checked.add(nxt)
                    q.append(nxt)
    return best / len(active)


def degree_scores(g: Graph) -> dict[int, int]:
    return {node: len(neigh) for node, neigh in g.items()}


def coupled_failure(
    road: Graph,
    rail: Graph,
    dependencies: dict[int, int],
    initial_road_removed: set[int],
    initial_rail_removed: set[int],
    steps: int = 12,
) -> tuple[set[int], set[int]]:
    road_removed = set(initial_road_removed)
    rail_removed = set(initial_rail_removed)
    for _ in range(steps):
        changed = False
        for road_node, rail_node in dependencies.items():
            if rail_node in rail_removed and road_node not in road_removed:
                road_removed.add(road_node)
                changed = True
            if road_node in road_removed and rail_node not in rail_removed:
                rail_removed.add(rail_node)
                changed = True
        if not changed:
            break
    return road_removed, rail_removed


def node_simulation(n: int, seed: int) -> None:
    road = make_layer(n, hubs=[0, 1, 2, 3, 4], seed=seed)
    rail = make_layer(n, hubs=[n - 1, n - 2, n - 3], seed=seed + 1)
    rng = random.Random(seed + 2)
    dependencies: dict[int, int] = {}
    # Low-degree peripheral road nodes depend on rail hubs and vice versa.
    for node in range(n):
        if rng.random() < 0.18:
            dependencies[node] = rng.choice([n - 1, n - 2, n - 3, rng.randrange(n)])
    road_deg = degree_scores(road)
    rail_deg = degree_scores(rail)
    top_road = set(sorted(road_deg, key=road_deg.get, reverse=True)[:8])
    top_rail = set(sorted(rail_deg, key=rail_deg.get, reverse=True)[:8])
    low_dep = set(sorted(dependencies, key=lambda x: road_deg[x])[:8])

    scenarios = [
        ("road_top_degree", top_road, set()),
        ("rail_top_degree", set(), top_rail),
        ("low_degree_dependency", low_dep, set()),
    ]
    print("NODE: multilayer coupling defeats single-layer hub metrics")
    print(f"n={n} dependencies={len(dependencies)}")
    print("scenario road_removed rail_removed road_giant rail_giant total_active")
    for name, r0, l0 in scenarios:
        rr, lr = coupled_failure(road, rail, dependencies, r0, l0)
        road_g = giant_fraction(road, rr)
        rail_g = giant_fraction(rail, lr)
        total_active = (n - len(rr)) + (n - len(lr))
        print(f"{name:22s} {len(rr):12d} {len(lr):12d} {road_g:10.4f} {rail_g:10.4f} {total_active:12d}")


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def first_primes(n: int) -> list[int]:
    primes: list[int] = []
    candidate = 2
    while len(primes) < n:
        ok = True
        for p in primes:
            if p * p > candidate:
                break
            if candidate % p == 0:
                ok = False
                break
        if ok:
            primes.append(candidate)
        candidate += 1 if candidate == 2 else 2
    return primes


def gamma_part(s: complex) -> complex:
    return complex(-0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0))


def dlog_zeta(s: complex, h: float = 2e-4) -> complex:
    z0 = mp.fp.zeta(s)
    return complex((mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300)))


def dlog_finite_euler(s: complex, primes: list[int]) -> complex:
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def coupled_defect(g: complex, p: complex) -> tuple[float, float, float]:
    gamma_amp = math.log(abs(g) + 1e-300)
    prime_amp = math.log(abs(p) + 1e-300)
    weld = math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300)
    return gamma_amp, prime_amp, weld


def corr(xs: list[float], ys: list[float]) -> float:
    mx = sum(xs) / len(xs)
    my = sum(ys) / len(ys)
    vx = sum((x - mx) ** 2 for x in xs)
    vy = sum((y - my) ** 2 for y in ys)
    if vx <= 1e-30 or vy <= 1e-30:
        return 0.0
    return sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / math.sqrt(vx * vy)


def ht_transfer(samples: int, prime_count: int, seed: int) -> None:
    node_sig = "multilayer transport coupling missed by single layer metrics"
    candidates = [
        "gamma prime weld coupling missed by single layer metrics",
        "finite euler layer coupling missed by phase metrics",
        "archimedean prime dependency missed by separate amplitudes",
    ]
    print("\nSTEP8 Levenshtein transfer candidates")
    best: tuple[int, int, str] | None = None
    for idx, cand in enumerate(candidates, 1):
        dist = levenshtein(node_sig, cand)
        ratio = dist / max(len(node_sig), len(cand))
        print(f"{idx} distance={dist} ratio={ratio:.4f} {cand}")
        if best is None or dist < best[0]:
            best = (dist, idx, cand)
    assert best is not None
    print(f"selected={best[1]} {best[2]}")

    primes = first_primes(prime_count)
    rng = random.Random(seed)
    print("\nSTEP9 method=2 attack false: HT layer-coupling diagnostic")
    print("kind sigma corr_gamma_weld corr_prime_weld high_gamma_rate high_prime_rate high_weld_rate overlap_all")
    for sigma in [0.3, 0.5, 1.2]:
        for kind in ["true", "finite", "random"]:
            gs: list[float] = []
            ps: list[float] = []
            ws: list[float] = []
            for i in range(samples):
                t = 80.0 + 0.08 * i
                s = complex(float(sigma), t)
                g = gamma_part(s)
                z = dlog_zeta(s)
                f = dlog_finite_euler(s, primes)
                theta = rng.uniform(-math.pi, math.pi)
                r = abs(z) * complex(math.cos(theta), math.sin(theta))
                p = z if kind == "true" else f if kind == "finite" else r
                ga, pa, wd = coupled_defect(g, p)
                gs.append(ga)
                ps.append(pa)
                ws.append(wd)
            gq = sorted(gs)[int(0.85 * (samples - 1))]
            pq = sorted(ps)[int(0.85 * (samples - 1))]
            wq = sorted(ws)[int(0.85 * (samples - 1))]
            high_g = [x >= gq for x in gs]
            high_p = [x >= pq for x in ps]
            high_w = [x >= wq for x in ws]
            overlap = sum(a and b and c for a, b, c in zip(high_g, high_p, high_w)) / samples
            print(
                f"{kind:6s} {sigma:.1f} {corr(gs, ws):15.5f} {corr(ps, ws):15.5f} "
                f"{sum(high_g)/samples:15.5f} {sum(high_p)/samples:15.5f} "
                f"{sum(high_w)/samples:14.5f} {overlap:11.5f}"
            )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=220)
    parser.add_argument("--samples", type=int, default=900)
    parser.add_argument("--prime-count", type=int, default=80)
    parser.add_argument("--seed", type=int, default=3677919641956617035 % (2**32))
    args = parser.parse_args()
    node_simulation(args.n, args.seed)
    ht_transfer(args.samples, args.prime_count, args.seed + 3)


if __name__ == "__main__":
    main()
