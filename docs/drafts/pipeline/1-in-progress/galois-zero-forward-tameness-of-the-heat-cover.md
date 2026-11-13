# Forward tameness of the heat cover: no zero escapes over times with `Re τ > 0`

- **ID:** gtz-forward-tameness
- **Stage:** 1-in-progress
- **Type:** theorem (analytic), open item 1 of Q5 on `gtz-galois-theory-of-zeros-programme.md`
- **Lean:** `formal/GaloisForLFunctions/GaloisTheoryOfZeros/` (modules F1–F6 below);
  reusable facts on `ξ` in `RHTower/`

## Target

`K ⊂ {Re τ > 0}` compact (`t₀ ≤ Re τ`, `‖τ‖ ≤ T₀`). Then:

1. There are `R, Y` such that every zero `z` of `H_τ`, `τ ∈ K`, with `‖z‖ ≥ R` has
   `|Im z| < Y`, is simple, and two such zeros at one time are equal or `≥ c/log‖z‖` apart.
2. No zero escapes along a path of times in `{Re τ > 0}`: every zero lifts along every path
   that avoids the branch times.
3. The branch times are discrete in `{Re τ > 0}` (finitely many in `K`).

Contrast (module 12): at the time `0` branch times accumulate or zeros escape.

## Objects

- `g_τ(w) = (4πτ)^{-1/2} exp(−w²/(4τ))`, `w ∈ ℂ`, `Re τ = t > 0`, `τ = t + iβ`.
  `|g_τ(v)| ≤ κ₀ e^{−λv²}` for real `v`, `κ₀ = (4πt₀)^{-1/2}`, `λ = t₀/(4T₀²)`; `∫_ℝ g_τ = 1`.
- `H_τ(z) = ∫_ℝ g_τ(u) ξ(s₀ + u) du`, `s₀ = ½ + iz`.
- Half transform `𝒜(τ, z) = ∫_0^∞ g_τ(u) ξ(s₀ + u) du`; holomorphic in `τ` and in `z`.
  `H_τ(z) = 𝒜(τ, z) + 𝒜(τ, −z)`; `𝒜(τ, −z) = ∫_0^∞ g_τ(u) ξ(s₀ − u) du = conj 𝒜(τ̄, z̄)`.
- Slope `xiSlope(s) = (Log s − log 2π)/2`; for `Re s ≥ 5`:
  `‖ξ'/ξ(s) − xiSlope(s)‖ ≤ 4/‖s‖ + 2^{5−Re s}/12` (four-factor formula, Stirling for `ψ`,
  `Λ(n) n^{−σ} ≤ Λ(n) n^{−5} 2^{5−σ}`).
- `a = xiSlope(s₀ + κ)` with a fixed real `κ ≥ Y + 5` (so `Re(s₀ + κ) > 0`); `a = α + iφ`,
  `|φ| < π/4`, `α = ½ log(‖s₀+κ‖/2π) → ∞`. Saddle `2τa = w₀ + ic`, `p = s₀ + 2τa`,
  main term `M(τ, z) = ξ(p) e^{−τa²}`.

## Identities

- `g_τ(u + ic) e^{ua} = e^{−ica + τa²} g_τ(u − w₀)` (completing the square).
- Corner shift (Cauchy on `[u₂, N] × [0, c]`), `u₂ = max(0, 5 − Re s₀)`:
  `𝒜 = J₁ + J₂ + J₃`, `J₁ = ∫_0^{u₂} g_τ(u) ξ(s₀+u) du`,
  `J₂ = i ∫_0^c g_τ(u₂+iv) ξ(s₀+u₂+iv) dv`,
  `J₃ = ∫_{u₂}^∞ g_τ(u+ic) ξ(s₀+ic+u) du = M ∫_{u₂}^∞ g_τ(u − w₀) ψ(u) du`,
  `ψ(u) = ξ(s₀+ic+u) e^{−(u−w₀)a}/ξ(p)`, `ψ(w₀) = 1`.
- `αw₀ − φc = 2 Re(τa²)`; `t c²/(4‖τ‖²) − φc − Re(τa²) = −t w₀²/(4‖τ‖²)`.
- With `τ' = τ̄` and the same `a`: `2τ̄a = w' + ic'`, and
  `c'φ + Re(τ̄a²) − (y'+9/2)α − α(y'+w₀−9/2) + 4βαφ + Re(τa²) = −2α(y' − 2βφ)`.

## Estimates

**(R1) saddle value.** For `X = Re z ≥ 0`, `Im z ≤ Y`, `‖z‖ ≥ R(t₀, T₀, Y, ε)`:
`‖𝒜(τ, z) − M(τ, z)‖ ≤ ε ‖M(τ, z)‖`, `M ≠ 0`.
- `J₃/M − 1`: Grönwall (`HTGeometry.norm_sub_mul_exp_le`) gives
  `‖ψ(u) − 1‖ ≤ e^{η|u−w₀|} − 1`, `η` the supremum of `‖ξ'/ξ − a‖` on the segment; `η → 0` on
  `|u − w₀| ≤ L`, and `η ≤ C + λ|u−w₀|/2` on the whole ray. Abstract Gaussian lemma:
  `‖∫_{−W}^∞ g ψ − 1‖ ≤ κ₀(√(π/λ)(e^{εL} − 1) + 16/(λL))`.
- `J₂/M`: exponent convex in `v`, values `−Re(τa²)` at `v = 0` and `−t w₀²/(4‖τ‖²)` at `v = c`,
  up to `O(α)`.
- `J₁/M`: strip comparison (`RHTower.norm_xi_horizontal_le_mul_norm_xi_five`) and a two-point
  comparison from `5 + iX` to `p`; exponent `−Re(τa²) + O(α)`.

**(D) the reflected transform is dominated.** There are `Y₁, R`: for `X ≥ 0`, `Im z = −y'`,
`y' ≥ Y₁`, `‖z‖ ≥ R`: `‖𝒜(τ, −z)‖ ≤ ε ‖M(τ, z)‖`.
- deep, `2λ(2y') ≥ α + C`: no shift; `‖ξ(s₀ − u)‖` bounded by `‖ξ(s₀)‖` times
  `e^{C₅u}` (right region), `C(1+X)e^{C₅σ₀}` (strip), the mirror growth beyond; then
  `‖ξ(s₀)‖ ≤ ‖ξ(p)‖ e^{−2Re(τa²)+O(α)}`.
- strip-like, `Y₁ ≤ y' ≤ κ₂α + C`: reflected transform `conj 𝒜(τ̄, z̄)` with corner at
  `u₂ = y' + 9/2` and shift `c' = Im(2τ̄a)`; crude slope bound `1/8`; total exponent
  `−2α(y' − 2βφ) + y'/8 + Cα`.

**Zero-free regions.** (R1) + (D): `H_τ(z) ≠ 0` for `‖z‖ ≥ R`, `|Im z| ≥ Y₁` (symmetries
`z ↦ −z`, `(τ, z) ↦ (τ̄, z̄)`).

**Local exponential model.** In the far strip, `h = 𝒜/M − 1` is holomorphic with `‖h‖ ≤ ε`
on unit discs in `z` and in `τ`, so (Schwarz) it is Lipschitz with constant `2ε`. With the
two-point comparison for `ξ` near `p`:
`𝒜(τ, z) = 𝒜(τ₀, z₀) exp(ia₀(z−z₀) + a₀²(τ−τ₀)) (1 + θ)`, `‖θ‖ ≤ ε(‖z−z₀‖ + ‖τ−τ₀‖)`,
and the same for `B(τ, z) = 𝒜(τ, −z)` with rates `−ib̄₀`, `b̄₀²`, `b₀ = a(τ̄₀, z̄₀)`.

**Consequences at zeros.** If `(τ₀, z₀)`, `(τ, z)` are zeros in one box,
`E = i(a₀+b̄₀)(z−z₀) + (a₀²−b̄₀²)(τ−τ₀)` satisfies `‖e^E − 1‖ ≤ ε'(‖z−z₀‖+‖τ−τ₀‖)`.
- Same time, `E` small: `z = z₀` (separation); `H_τ'(z₀) ≠ 0` (simple).
- Along a lift `E(s)` is continuous and near `2πiℤ`, so it stays near `0`:
  `‖z(s) − z(s₀)‖ ≤ (π/2 + o(1))‖γ(s) − γ(s₀)‖ + o(1)`. A lift cannot leave a box: no escape.
- Multiple zeros over `K` lie in a compact set and are isolated: finitely many branch times.

## Modules

| # | Module | Content | Status |
|---|---|---|---|
| F1 | `RHTower/XiSlopeInTheRightHalfPlane` | `xiSlope`, slope lemma, variation, two-point comparison, growth, strip bound at all heights | |
| F2 | `TheHeatFamilyAtForwardTimesIsAComplexGaussianAverageOfXi` | `g_τ`, representation, half transform, symmetries, corner shift | |
| F3 | `TheHalfTransformIsXiAtTheSaddlePoint` | (R1) | |
| F4 | `TheReflectedHalfTransformIsDominated` | (D), zero-free regions | |
| F5 | `FarZerosAtForwardTimesAreSimpleAndSeparated` | local exponential model, simplicity, separation, velocity | |
| F6 | `NoZeroEscapesOverForwardTimes` | non-escape, lifting, discreteness of branch times | |

## Log
- 2026-11-13 — plan fixed; soft routes (barriers, counting, traces, normal families at fixed
  scale) excluded: zeros move farther than their spacing, and the family varies on the time
  scale `1/log²`.
