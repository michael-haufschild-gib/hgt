# Even slice coefficients are positive-definite functions of the height

- **ID:** slice-coefficients-positive-definite-in-height
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/wd-la-sign-producer-loop-2026-10-25.md`, rows 1, 2, 7
- **Statement:** Every even-order heated `Ξ`-slice coefficient `T_{2k}(λ, x₀, t)` (`λ ≥ 0`, any
  abscissa `x₀`) and every even slice moment of a super-exponential kernel (including the
  de Bruijn–Newman slices of `H_μ`) is a positive-definite function of the height `t`, with
  `|T(t)| ≤ T(0)` and `T(0) > 0`. At `λ = 0`: `|c_{2k}(t)| ≤ c_{2k}(0)`, and the first Laguerre
  expression of `Ξ` is maximal at the origin.

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 `RHTower/XiSliceHeatHeightPositiveDefinite`, standard axioms, wired into `RHTower.lean`
- [ ] 3 → 4

## Paper proof
Each coefficient is `∫∫ w(u,v) e^{it(u+v)}` with `w ≥ 0` integrable
(`w = Φ(u)Φ(v)e^{λ(u−v)²/2}e^{x₀(u−v)}(u−v)^{2k}/(2k)!`). Hermitian forms:
`Σ a_i conj(a_j) T(t_i − t_j) = ∫ w |Σ_i a_i e^{it_i(u+v)}|² ≥ 0`; `|T(t)| ≤ ∫ w = T(0)`;
`T(0) > 0` because `w` is continuous and positive near `(a, 0)` with `Φ(a) > 0`, `a ≠ 0`.

## Lean
`heightTransform` laws (`sum_sum_mul_heightTransform_nonneg`, `norm_heightTransform_le_central`,
`heightTransform_central_pos`); instances `sum_sum_mul_xiSliceHeatTransfer_nonneg`,
`norm_xiSliceHeatTransfer_le_central`, `sum_sum_mul_kernelSliceMoment_nonneg`,
`norm_kernelSliceMoment_le_central`, `sum_sum_mul_xiSliceCoeff_nonneg`,
`norm_xiSliceCoeff_le_central`, `norm_laguerre_XiC_le_central`.

## Position
RH asks each coefficient function to lie in the positive cone; it always lies in the Bochner
cone. Equivalently RH asks the `u+v` weight of each coefficient to be itself positive definite.
Fibrewise (Wigner) positivity is false at every real zero ordinate (loop row 1).

## Log
- 2026-10-25 — proved and formalized.
