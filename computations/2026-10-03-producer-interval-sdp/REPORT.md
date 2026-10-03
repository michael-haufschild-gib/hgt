# Producer intervals from finite-support Weil positivity (2026-10-03)

## What was computed
- **Weil form.** Cubic B-spline span (knot spacing hk = 0.05 or 0.025) over `[−L/2, L/2]`:
  `Q_λ(f) = h(i/2)+h(−i/2) − g(0)log π + (1/2π)∫h Re ψ(1/4+ir/2) − 2Σ_{n≤e^L} λ(n)n^{−1/2}g(log n)`, with `g = f*f̃`, `h = |f̂|²`.
  - Validated: `Q_Λ = Σ_γ h(γ)` (2000 zeros) to 1e-13 for `L ≤ 5`.
- **SDP.** Projection of `W_L = {λ on n ≤ e^L : Q_λ ⪰ 0}` onto single coordinates.
  - Preconditioned in the eigenbasis of `Q_Λ`, with variables rescaled.
  - Control: extra support points at half-integers.

## Results

Feasible `δ = λ(2) − log 2`:

| L | hk = 0.05 | hk = 0.025 |
|---|---|---|
| 0.8 | [−5.2, 2.1] | [−0.54, 0.21] |
| 0.9 | [−0.13, 0.021] | [−0.043, 0.0062] |
| 1.0 | [−9.9e-3, 6e-4] | [−3.2e-3, 2.0e-4] |
| 1.1 | [−2.3e-3, 9.5e-5] | [−3.2e-4, 1.9e-5] |
| 1.2 | [−9.4e-5, 3.7e-6] | [−2.6e-5, 7.8e-7] |
| 1.3 | [−8.8e-8, 7.3e-8] | [−1.4e-9, 2.8e-8] |
| ≥ 1.4 | below double precision | below double precision |

- **Other weights.**
  - `λ(3)` is pinned once `L > log 3 + 0.3`: width 6e-3 at `L = 1.3`, 8e-6 at `L = 1.5`.
  - `λ(4)` is pinned once `L > log 4 + 0.2`.
- **Half-integer control:** the ranges widen only about tenfold.
- **Smallest eigenvalue of `Q_Λ`** (G-normalized): 6.3e-3, 8.9e-4, 1.2e-4, 7.9e-6, 3.7e-7, 1.1e-8, 4.2e-10 for `L = 0.7, …, 1.3`. It then hits the basis floor: ~1e-11 at hk = 0.05, ~1e-13 at hk = 0.025.

## Interpretation
- Every integer-supported Weil-positive weight system for ζ's archimedean datum agrees with `Λ` on `n ≤ e^{L−0.3}`, to precision that improves super-exponentially in `L`.
- So W is numerically `{Λ}` (or empty): uniqueness, (N1) and (N2), holds numerically.
- Combined with C329 numerics, RH ⟺ PBAP (prime-free positivity) is the remaining content.
- These ranges are outer bounds, since they use fewer tests than the full problem. With interval arithmetic, `|λ(2) − log 2| ≤ 1e-7` for every producer would become a theorem.
