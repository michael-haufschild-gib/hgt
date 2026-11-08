# Review-0811 §2.2 open obstacles: contribution loop

- **ID:** review-0811-open-obstacles-loop
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (loop)
- **Source:** docs/reports/review-0811/obstacles-summary.md §2.2
- **Statement:** Conjecture, prove and formalize contributions that move problems of §2.2 (Σ, Π, Γ); target 250.

## Contributions (formalized)

| # | Problem | Result | Lean |
|---|---|---|---|
| 1 | B115, B88 | The archimedean Frobenius kernel `min/(1−(min/max)²)` is `2π√(mn)·G_{1/2}(d)`, `G_s(d)=e^{−(s−1)d}/(4π sinh d)` the Green function of `Δ−s(2−s)` on `ℍ³`, `d=|log(n/m)|` the distance of `z_m=(0,0,m)`, `z_n`; radial equation; Newtonian pole `4πd·G_s→1` (the diagonal is a Coulomb self-energy); `Δ=½` propagator = `Δ=3/2` propagator + complementary-series `1/(2cosh(d/2))`; damped kernels `√(mn)e^{−d/2}/(1−r²e^{−2d})` PSD (Ornstein–Uhlenbeck), lossless off the diagonal, diagonal `n/(1−r²)→∞`; Weil's archimedean-plus-pole weight `= 4πG_{1/2}(u)−4cosh(u/2)` | `SurfaceOfSpecZ/TheArchimedeanFrobeniusIsAHyperbolicGreenFunction` |

## Conjecture log
- C1 (proved, #1): the jets carrier is hyperbolic three-space with dilations as translations along a geodesic.

## Log
- 2026-11-08 — created; #1 formalized and wired.
