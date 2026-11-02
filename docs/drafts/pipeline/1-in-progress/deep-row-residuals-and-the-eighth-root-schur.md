# Deep-row conductor residuals and the eighth-root Schur synthesis

- **ID:** deep-row-residuals-and-the-eighth-root-schur
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** T3 and T4 of `off-pole-nonratio-cross-and-one-eighth-weil-positivity.md`
- **Statement:** For every `0 < α < 1/8`, eventually in `N` and uniformly in `1 ≤ c ≤ (log N)^α`,
  `completeWeilMatrix tiltedUnitSpline c N` is positive definite.

## Notation
`L = log N`, `q = α + 1/4`, `Q₁ = ⌊L^q⌋`, `R₀ = ⌊exp √L⌋`, `R₁ = ⌊N^{θ₁}⌋`, `X₀ = ⌊exp √L⌋`.
Deep rows `D = {n ≤ N/X₀}`, top rows `Dᶜ`. `r_m = W v_m − E_m v_m`, `E'_m = E_m − κ/(2c⁷)`
(spectral floor), `E_m ≥ κ min(1, (m/c)⁷)`.

## Paper proof

**T3.1 Deep residual.** For `1 ≤ m ≤ Q₁`,
`‖r_m 1_D‖² ≤ K m (1 + log m)² / L + (terms ≤ c^{10} L^{-3})`, with the eight residual channels
(`completeWeilMatrix_ramanujan_residual_eq_at_every_overlap`) treated as follows:
- prime residual: total `≤ C m(1 + log m)²/L`, independent of `c`;
- self error `≤ C m c²/N²` and pole error `≤ C m c^{10}(L/N)²` (totals);
- center: `Collar(n,j) = √(nj)/(2N)·(1/|n−j| + 1/(n+j))`, so `|α Collar v_m(n)| ≤ C α √(nm)(2+L)/(N√L)`;
  the pole part leaves `(α/N)(√n S_m + T_m/√n)` minus `α[m=1]v_m`. On `D` both are
  `O(α² m L²/X₀²)` in square sum;
- separated: per row `≤ C(m c² n/N² + m c⁴/N²)` (corpus row bound), so `O(m c²/X₀²)` on `D`;
- near-Gamma-downward and near-center: supported on rows with near pairs (`N ≤ 2ce² n`), zero on `D`;
- upward: `√n · row = (log − lin) + (lin − rec) + (rec − c_m shell)`. The first is
  `≤ D·mertens(N+B)/N`, the second `≤ 4Bφ(m)·primeIndexBoundaryMass B (N/n)`, the third
  `≤ C c/(log Y)^k` with `Y = X₀/(2c)` (affine shell rate). On `D` the square sum is
  `O(c²(1 + L)/(log Y)^{2k}) + o(1/L)`.

**T3.2 Top mass.** For `u ∈ V_{R₀}`, `‖u 1_{Dᶜ}‖² ≤ 2(log 2X₀ + 3)/L ‖u‖²`
(`sum_quotient_tail_sq_le_of_mem_conductorSubspace`, `R₀² X₀ ≤ N`).

**T3.3 Pairing.** With `z = u₀ + u₁ + w` (three-band split of `z ∈ V_{Q₁}^⊥`),
`Φ(z) = Σ_{m ≤ Q₁} ⟨r_m, z⟩²/E'_m ≤ 8Ψ ρ_top ‖u₀‖² + 8Ψ_D ‖u₀‖² + 4Ψ(‖u₁‖² + ‖w‖²)`,
`Ψ = Σ ‖r_m‖²/E'_m ≲ (c⁷ + Q²(1+log Q)²) c²(1+log c)³ L^{1/k}/L` (corpus),
`Ψ_D = Σ ‖r_m 1_D‖²/E'_m ≲ (c⁷ + Q²(1+log Q)²)/L`, `ρ_top = 2(√L + 4)/L`.
Below `1/8`: `Ψρ_top, Ψ_D = o(1)`, `Ψ = o(L^{1/2})`, `Ψ c⁷/L = o(1)`.

**T4.1 Complement coercivity with reserves.** On `V_{Q₁}^⊥`,
`E(z) ≥ (κ₀ + 2)‖z‖² + λ₀‖u₀‖² + λ₁‖u₁‖² + λ_S‖w‖²` with `λ₀ ≍ log Q₁`, `λ₁ ≍ log R₀`,
`λ_S ≍ θ₁L/c⁷`: the 1/9 three-band assembly with the far reserve below 1/8 (T1), the band–far
cross below 1/8 (T2) and the corpus band coercivities, keeping half of each block reserve.

**T4.2 Schur.** `2|⟨W'y, z⟩| ≤ (1/8)S_y + 8Φ(z)`, `8Φ(z) ≤ λ₀‖u₀‖² + λ₁‖u₁‖² + λ_S‖w‖²`
eventually; with the corpus polylog floor `⟨W'y, y⟩ ≥ (1/4)S_y` (`α + 2q < 1`) this gives
`⟨W'x, x⟩ > 0` for `x ≠ 0`, hence `W ≻ 0`.

## Lean modules
- `CriticalArithmeticCorrelationTheory.TheConductorResidualsAreSmallOnTheDeepRows` — T3.1:
  `exists_deepMass_conductorResidual_le` (deep rows `nX ≤ N`, `X > max(2ce², 2c, 2⌈ce⌉+3)`;
  budget `deepResidualBudget`, upward rate `ρ` as hypothesis). Made public for it: the prime,
  self and pole quadratic bounds in `QuadraticOverlapConductorResiduals`.
