#!/usr/bin/env python3
"""
Diagnosis of the Newton-vs-winding mismatch in mollified_dip_cert.py (doc 56 §9
FLAG). N=200: dense 3-line seeding + jittered adaptive winding; per-box
comparison; corrected X_of_c profile.
"""
import numpy as np, json
from math import log, pi

N, U, T0 = 200, 2000.0, 2 * pi * (200.25) ** 2
logN = log(N)

def F_and_dF(s_arr):
    n = np.arange(1, N + 1, dtype=float)
    lg = np.log(n)
    E = np.exp(-np.outer(np.atleast_1d(s_arr), lg))
    return E.sum(1), -(E * lg[None, :]).sum(1)

def newton(seeds_s):
    s = np.array(seeds_s, dtype=complex)
    for _ in range(60):
        F, dF = F_and_dF(s)
        dF = np.where(np.abs(dF) < 1e-14, 1.0, dF)
        step = F / dF
        step = np.where(np.abs(step) > 0.3, step / np.abs(step) * 0.3, step)
        s = s - step
    F, _ = F_and_dF(s)
    return s[np.abs(F) < 1e-10]

def winding(b_lo, b_hi, t_lo, t_hi, ds):
    nt = max(16, int((t_hi - t_lo) / ds)); nb = max(16, int((b_hi - b_lo) / ds))
    pts = np.concatenate([
        b_lo + 1j * np.linspace(t_lo, t_hi, nt),
        np.linspace(b_lo, b_hi, nb) + 1j * t_hi,
        b_hi + 1j * np.linspace(t_hi, t_lo, nt),
        np.linspace(b_hi, b_lo, nb) + 1j * t_lo])
    F, _ = F_and_dF(pts)
    ph = np.unwrap(np.angle(F))
    return (ph[-1] - ph[0]) / (2 * pi)

# dense 3-line seeding
tg = np.arange(T0, T0 + U, 0.004)
roots = []
for frac in (0.2, 0.5, 0.9):
    sig = 0.5 + frac / logN
    Fl, _ = F_and_dF(sig + 1j * tg)
    a = np.abs(Fl)
    mins = np.where((a[1:-1] < a[:-2]) & (a[1:-1] < a[2:]))[0] + 1
    roots.extend(newton(sig + 1j * tg[mins]))
ded = {}
for z in roots:
    ded[(round(z.real, 7), round(z.imag, 5))] = z
allr = list(ded.values())
sliver = [z for z in allr if T0 <= z.imag <= T0 + U
          and 0 < z.real - 0.5 <= 1.2 / logN]
cv = sorted((z.real - 0.5) * logN for z in sliver)
Xc = {round(c, 2): sum(1 for v in cv if v <= c) for c in np.arange(0.1, 1.05, 0.1)}
print("dense X_of_c:", Xc)
print("dense slope/UlogN:", {k: round(v / (U * logN), 5) for k, v in Xc.items()})

# jittered adaptive winding on 30 boxes, integer-quality enforced
rng = np.random.default_rng(7)
mism = []
tot_w = tot_n = 0
for _ in range(30):
    tl = T0 + rng.uniform(0, U - 2)
    for attempt in range(5):
        j = rng.uniform(-0.05, 0.05)
        w = winding(0.5 + 1e-4, 0.5 + 1.0 / logN, tl + j, tl + j + 2, 0.0003)
        if abs(w - round(w)) < 0.05:
            break
    inb = sum(1 for z in allr if tl + j < z.imag < tl + j + 2
              and 0.5 + 1e-4 < z.real < 0.5 + 1.0 / logN)
    tot_w += round(w); tot_n += inb
    if abs(round(w) - inb) > 0:
        mism.append({"t": tl + j, "w": round(w), "newton": inb})
print(f"boxes 30: winding_total {tot_w} newton_total {tot_n} mismatches {len(mism)}")
for m in mism[:10]: print("  ", m)
json.dump({"Xc": Xc, "mismatches": mism, "tot_w": tot_w, "tot_n": tot_n,
           "n_sliver": len(sliver), "n_all": len(allr)},
          open("winding_verify.json", "w"), indent=1)
