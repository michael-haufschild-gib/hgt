# Twin LP and W_d dimension (2026-10-03)

## What was computed
- **AFE.** Smoothed approximate functional equation for `Λ(s) = q^{s/2}Γ_ℝ(s)^d L(s)` with the rotated weight `g(w) = exp(a w² − i(dπ/4)w)`. The rotation cancels the Gamma decay, so there is no catastrophic cancellation.
  - Validated on `L(s,χ₅)³`: error ≤ 1e-13 for `t ≤ 60` at `a = 0.02`.
  - Up to `t = 120`, two weights `a` agree to 1e-9 relative.
- **Approximate W_d** (entire part, `q = 1`) = null space of the FE defect `D(3+it)` (Dirichlet series minus AFE) for `t ≤ T + 60`, with `N = 4(T_c/2π)^{d/2}` coefficients.
  - **Visible part:** the SVD of the Z-evaluation on `[0,T]`, per unit ℓ² coefficient norm.
  - **Certification:** a direction counts only if its Z-values agree under two AFE weights (to 1e-11).
- **Twin LPs** for `F = ζ^d + E`:
  - (i) Gram's law at all degree-`d` Gram points, `dϑ(g_j) = jπ`;
  - (ii) L1 minimization of Gram violations over the certified directions, with `|e_n| ≤ CB·d_d(n)`, then sign changes of `Z_F` counted on a 0.01 grid.

## Results
- **Controls:**
  - `d = 1`: no FE-null directions.
  - `d = 2`: visible singular values ≤ 3e-4, none certified.
  - Both consistent with Hamburger and Kaczorowski–Perelli.
- **Visible `dim W_d` on `[0,T]`** (RMS > 0.01 per unit norm), against the L399 phase-space count `(d−2)(T/2π)(log(T/2π)−1)`:

  | d | T | visible | L399 |
  |---|---|---|---|
  | 3 | 40, 80, 120, 160, 220 | 0, 4, 10, 19, 32 | 5, 20, 37, 57, 90 |
  | 4 | 40, 70, 100 | 1, 9, 22 | 11, 31, 56 |
  | 5 | 30, 50, 70 | 2, 10, 23 | 8, 26, 47 |

  - The freedom switches on above an onset height (about 45 for `d = 3`).
  - At large T it grows at roughly 0.4–0.6 of the L399 density.
  - The spectrum is a plateau of equal singular values, then a cliff. The plateau is the Dirichlet-polynomial mean-value theorem.
- **Gram-law twin LP (d = 3):** infeasible at `T = 30, 50, 80`, even with unbounded coefficients.
- **Real-zero deficit (d = 3, certified directions):**

  | T | CB | sign changes of ζ³+E | ζ³ alone | expected count | sign changes of E alone (expected count) |
  |---|---|---|---|---|---|
  | 50 | 10 | 8 | 10 | 28 | 1 (25) |
  | 50 | 1000 | 10 | 10 | 28 | 3 (25) |
  | 80 | 10 or 1000 | 21 | 21 | 62 | 5–9 (59) |
  | 120 | 10 | 40 | 38 | 114 | 14 (111) |
  | 120 | 1000 | 41 | 38 | 114 | 15 (111) |

  - W cannot split ζ³'s triple zeros into real ones: about two thirds of all zeros stay off the line.
  - Entire W elements are far from real-rooted.
- **Pitfall:** without certification and bounds, the LP exploits rounding noise along directions with singular values ~1e-12 (coefficients up to 1e13, fake sign patterns).

## Interpretation
- Numerical evidence for C329 (no real-rooted twins of ζ³) at heights ≤ 120, with coefficients ≤ 1000·d₃(n).
- L399's count overestimates the low-height freedom of `W_d`; the true density is roughly half, after an onset height.
- With C329, the twin door for producers is closed (producer exists ⟺ RH).

## Correction (window-local count, computations/2026-10-03-w3-window-density)
- The "about half the L399 density" claim came from cumulative counts with an onset lag.
- Window-local `dim W₃` (40-unit windows, threshold 0.01·top) equals ζ's zero count `ϑ/π` in the window above height ≈ 180 (22/22.0, 23/23.2, 24/24.2). L399 is asymptotically exact.
