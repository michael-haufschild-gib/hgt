# The heat detection rate is quadratic in the depth

- **ID:** heat-detect-quadratic
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `reboot-programme-conjecture-loop-2026-10-30.md` #1; `reboot-final.md` §4.B, WP-B3, WP-A3
- **Statement:** There is an absolute `c > 0` such that for `δ₀ ∈ (0, ½]` and `t ≥ t₁(δ₀)`, an
  off-line zero `½ + δ + it` with `δ ≥ δ₀` makes some heated slice coefficient
  `T_n(κ/log t, 0, t)` negative for every `κ ∈ (0, cδ₀²]`.

## Goal
Replaces the corpus rate `κ₀(δ₀) = δ₀²/(200(log(3/δ₀)+1))`
(`RHTower.re_xiSliceHeatTransfer_neg_of_slice_zero`) by `cδ₀²`. Together with head repair at
`32R²/N(t,R)` this makes the cluster-limited detection rate `≍ δ²` two-sided in order of magnitude.
Consequences: `Λ ≥ cδ²/log Im ρ` for every off-line zero; every-height heat positivity at rate `κ`
excludes `Re ρ ≥ ½ + √(κ/c)`.

## Gates
- [x] 0 → 1  in-progress: well-posed, unconditional, attack idea below
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Approach
Paper proof. Let `a_n = Re T_n(λ, 0, t) ≥ 0`, `H(y) = Σ a_n yⁿ`, `F = f_t(3/2)`, `A = log t + K₀`,
`M = ⌈(3A + 20 + 2A²λ)/log 2⌉`.

1. **Log-convexity.** `log H(e^s)` is convex: for `0 < r₁ ≤ r ≤ r₂`, `r = r₁^{1−θ}r₂^θ`,
   `H(r) ≤ H(r₁)^{1−θ}H(r₂)^θ` (weighted AM–GM termwise).
2. **Endpoints.** Three radii: `H(δ/2) ≥ (δ/3)^M F/4`. Envelope: `H(3/2) ≤ E·F`,
   `E = √2 e^{3A/2 + 9/2 + 2A²λ}`. So `H(3/2)/H(δ/2) ≤ 4E(3/δ)^M`.
3. **Local degree.** For `δ/2 ≤ R ≤ 3/2`, `θ = log(2R/δ)/log(3/δ)` and `(3/δ)^{Mθ} = (2R/δ)^M`, so
   `H(R) ≤ 4E (2R/δ)^M H(δ/2)`. For `R ≥ 3/2` the envelope and `3/δ ≤ 2R/δ` give the same bound with
   the factor `e^{AR + 2R² + 2A²λ}`. Hence for `R ≥ 2δ`, using `2R/δ ≤ 4e^{(R−2δ)/(2δ)}`:
   `H(R) ≤ C H(δ/2) e^{α R + 2R²}`, `α = A + M/(2δ)`, `log C = O(A)`, for all `R > 0`
   (monotonicity of `H` below `2δ`).
4. **Hermite tail** (`re_xiSliceHeatTransfer_neg_of_relative_growth`): contradiction once
   `log(6C) + 2αδ + 16δ² + 32α²λ < (δ²/(4λ)) log(3/2)`. With `λ = κ/L`, `M ≈ 4.33A`, the left side is
   `≈ 14A + 230Aκ/δ²`, the right side `≈ 0.1 δ²A/κ`: holds for `κ ≤ δ²/200` and `L` large.

The `log(3/δ)` of the corpus rate came from comparing `H(δ/2)` with `F` at radius `3/2`; log-convexity
transfers the deficit at `δ/2` to every radius `O(δ)`, so the loss depends only on `R/δ`.

## Log
- 2026-10-30 — created in 1-in-progress.
