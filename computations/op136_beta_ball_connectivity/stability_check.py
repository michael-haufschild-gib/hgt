#!/usr/bin/env python3
"""Stability check for the c=-0.9 split phases: genuine fjords vs raster artifacts.

If the mirror-pair components are genuine, their AREA (pixel count / total) is stable as
resolution and maxit grow, and their position is fixed.  If they are artifacts (slow-escape
pixels sealing a thin fjord mouth), they shrink or vanish as maxit grows.
"""
import numpy as np
from collections import deque

def k_mask(c, center, rho, n, maxit, bail=9.0):
    xs = np.linspace(center.real - rho, center.real + rho, n)
    ys = np.linspace(center.imag - rho, center.imag + rho, n)
    X, Y = np.meshgrid(xs, ys)
    Z = X + 1j * Y
    W = Z.copy()
    alive = np.ones_like(X, dtype=bool)
    for _ in range(maxit):
        Wa = W[alive]
        Wa = Wa * Wa + c
        W[alive] = Wa
        esc = np.abs(Wa) > bail
        idx = np.where(alive)
        alive[idx[0][esc], idx[1][esc]] = False
        if not alive.any():
            break
    return alive, Z

def components(kmask, Z, center, rho):
    n = kmask.shape[0]
    free = (~kmask) & (np.abs(Z - center) < rho)
    seen = np.zeros_like(free, dtype=bool)
    comps = []
    for i0 in range(n):
        for j0 in range(n):
            if free[i0, j0] and not seen[i0, j0]:
                q = deque([(i0, j0)]); seen[i0, j0] = True
                sz = 0; cx = 0.0; cy = 0.0
                while q:
                    i, j = q.popleft(); sz += 1
                    cx += Z[i, j].real; cy += Z[i, j].imag
                    for di, dj in ((1,0),(-1,0),(0,1),(0,-1)):
                        a, b = i+di, j+dj
                        if 0 <= a < n and 0 <= b < n and free[a, b] and not seen[a, b]:
                            seen[a, b] = True; q.append((a, b))
                comps.append((sz, cx/sz, cy/sz))
    comps.sort(reverse=True)
    return comps

c = -0.9
beta = (1 + np.sqrt(1 - 4*c)) / 2
lam = 2 * beta
print(f"c={c} beta={beta:.6f} lambda={lam:.6f}")

# scan finely around phase k=5 (rho ~ 0.0962) to find the worst rho
print("\n-- fine phase scan around k=5 (n=401, maxit=1500) --")
for frac in np.linspace(4.0, 6.5, 11):
    rho = 0.25 * lam ** (-frac / 6.0)
    km, Z = k_mask(c, beta+0j, rho, 401, 1500)
    cs = components(km, Z, beta+0j, rho)
    big = [(s, round(x,5), round(y,5)) for s, x, y in cs if s >= 10]
    print(f"  frac={frac:.2f} rho={rho:.5f} comps>=10px: {big[:5]}")

# stability at the worst phase: resolution x maxit matrix
print("\n-- stability matrix at rho of frac=5.0 --")
rho = 0.25 * lam ** (-5.0/6.0)
for n in (401, 801, 1601):
    for maxit in (800, 3200):
        km, Z = k_mask(c, beta+0j, rho, n, maxit)
        cs = components(km, Z, beta+0j, rho)
        tot = sum(s for s, _, _ in cs)
        big = [(s, round(s/tot, 6), round(x,5), round(y,5)) for s, x, y in cs if s >= 10]
        print(f"  n={n} maxit={maxit}: {len(big)} comps>=10px  "
              f"(size, frac, cx, cy) = {big[:4]}")
