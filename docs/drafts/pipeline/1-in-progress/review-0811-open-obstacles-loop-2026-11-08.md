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
| 2 | B115, B17, B88 | Every square block of `archKernel` on rows below columns is a scaled Cauchy matrix, hence nonsingular; on pairwise coprime orders the archimedean Frobenius agrees with no kernel of finite rank (no finite-dimensional fibre carries the jets). `√(mn)C_∞(m,n)=(n³−nm²−m³)/(n²−m²)`: the compensation is negative iff `n/m` is below the plastic number `ρ³=ρ+1`, positive above, never zero (`ρ` irrational) — the `log ρ` aperture is where the archimedean compensation changes sign | `SurfaceOfSpecZ/TheArchimedeanFrobeniusHasInfiniteRank` |
| 3 | B87, B95 (F15 C15.1) | The Krein squares of the integer probes are not all integers, unconditionally; no `ℤ`-valued count and no integral trace form `Tr(T_mT_nᵗ)` equals `Q` on integer probes. Proof: integer squares at `e_i`, `e_i+e_j` put `2Re F(log(m/n))∈ℤ` for the spline series `F`; density + continuity make `Re F` constant; bounded orbit ⇒ RH; under RH `Re F(0)−Re F(π/γ₁)≥2m|B̂(γ₁)|²>0` at a zero the spline sees | `CountingHolography/TheIntegerProbesAreNotIntegerValued` |

## Conjecture log
- C1 (proved, #1): the jets carrier is hyperbolic three-space with dilations as translations along a geodesic.
- C2 (proved, #2): every carrier of the jets on coprime orders is infinite-dimensional; the sign of `C_∞` is the plastic cubic.
- C3 (proved, #3): C15.1 — integer probes are not integer-valued; integrality would force RH and then a constant Bohr series.

## Log
- 2026-11-08 — created; #1–#3 formalized and wired.
