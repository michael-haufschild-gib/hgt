#!/usr/bin/env python3
"""Task #136 pre-certification: is ball x rho \\ K_c connected at the beta fixed point,
for real c, across log-periodic scales?

At beta the multiplier lambda = 2*beta is real > 1, so the Julia germ is log-periodic in
scale: fjords (extra components of the ball complement) recur periodically in log(rho) if
they occur at all.  We rasterize B(beta, rho), mark K by bounded-orbit test, and count
4-connected components of the complement inside the disk.

Two targets:
  (A) OneSidedAt (all small scales connected)  -- needs count == 1 at EVERY phase;
  (B) cofinal variant (arbitrarily small good scales) -- needs count == 1 at SOME phase
      in each period (then good radii recur at every depth by self-similarity).

Component counts are checked for stability across grid resolution and iteration depth
(slow-escape pixels near J are conservatively marked K, which can seal thin fjords; a
fake seal thins out as maxit grows, so stable counts across maxit are trustworthy).
"""
import numpy as np
from collections import deque
import sys


def k_mask(c, center, rho, n, maxit, bail=9.0):
    xs = np.linspace(center.real - rho, center.real + rho, n)
    ys = np.linspace(center.imag - rho, center.imag + rho, n)
    X, Y = np.meshgrid(xs, ys)
    Z = X + 1j * Y
    W = Z.copy()
    alive = np.ones_like(X, dtype=bool)
    for _ in range(maxit):
        W_alive = W[alive]
        W_alive = W_alive * W_alive + c
        W[alive] = W_alive
        escaped = np.abs(W_alive) > bail
        idx = np.where(alive)
        alive[idx[0][escaped], idx[1][escaped]] = False
        if not alive.any():
            break
    return alive, Z  # alive == True  <=>  treated as K


def component_count(kmask, Z, center, rho, min_size):
    """Count 4-connected components of (not K) within the open disk; return sizes."""
    n = kmask.shape[0]
    in_disk = np.abs(Z - center) < rho
    free = (~kmask) & in_disk
    seen = np.zeros_like(free, dtype=bool)
    sizes = []
    for i0 in range(n):
        for j0 in range(n):
            if free[i0, j0] and not seen[i0, j0]:
                q = deque([(i0, j0)])
                seen[i0, j0] = True
                sz = 0
                while q:
                    i, j = q.popleft()
                    sz += 1
                    for di, dj in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                        a, b = i + di, j + dj
                        if 0 <= a < n and 0 <= b < n and free[a, b] and not seen[a, b]:
                            seen[a, b] = True
                            q.append((a, b))
                sizes.append(sz)
    sizes.sort(reverse=True)
    return [s for s in sizes if s >= min_size], sizes


def run(c, n=601, maxit=1200, periods=5, per_period=6, rho0=0.25):
    beta = (1 + np.sqrt(1 - 4 * c)) / 2
    lam = 2 * beta
    print(f"c={c}  beta={beta:.6f}  lambda={lam:.6f}")
    bad_phases = []
    for k in range(periods * per_period + 1):
        rho = rho0 * lam ** (-k / per_period)
        kmask, Z = k_mask(c, beta + 0j, rho, n, maxit)
        big, all_sizes = component_count(kmask, Z, beta + 0j, rho, min_size=25)
        tag = "OK " if len(big) == 1 else "SPLIT"
        if len(big) != 1:
            bad_phases.append((k, rho, [s for s in all_sizes[:6]]))
        print(f"  k={k:2d} rho={rho:.5f}  significant_components={len(big)} "
              f"sizes={big[:4]}{'...' if len(big) > 4 else ''}  [{tag}]")
    return bad_phases


if __name__ == "__main__":
    cs = [0.2, -0.5, -0.9, -1.0, 0.24]
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 601
    maxit = int(sys.argv[2]) if len(sys.argv) > 2 else 1200
    print(f"grid {n}x{n}, maxit {maxit}")
    summary = {}
    for c in cs:
        summary[c] = run(c, n=n, maxit=maxit)
        print()
    print("==== SUMMARY (phases with component count != 1) ====")
    for c, bad in summary.items():
        print(f"c={c}: {'ALL CONNECTED' if not bad else bad}")
