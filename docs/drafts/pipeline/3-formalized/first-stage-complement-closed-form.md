# The first-stage complement in closed form

- **ID:** first-stage-complement-closed-form
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** review-0511 §2.1, A7.
- **Statement:** for `A = log 2 + ε` and collar data `x_L, x_R`,
  `inf_y F(x_L, y, x_R) = Q(x_L) + Q(x_R) + Φ_ε(μ(x_L), ν(x_R))`, with
  `Φ_ε(μ, ν) = 2⟨μ, ν⟩ − sup_y ℓ_{μ,ν}(y)²/Q(y)` and `ℓ_{μ,ν}(y) = ⟨μ, ν(y)⟩ + ⟨μ(y), ν⟩`.
- **Lean:** `GaloisForLFunctions/GrowingWindowsOfSpecZ/TheFirstStageComplementIsASchurComplement.lean`:
  `twoCollarForm_firstStage_eq`, `firstStageDual_le`, `two_mul_momentPairing_sub_le`,
  `stageTests_nonneg_iff_firstStageComplement`; standard axioms only.

## Proof

`firstStage_frozenTwoCollar_eq` gives `F = Q(x_L) + Q(x_R) + 2⟨μ, ν⟩ + Q(y) + 2ℓ(y)`. Since `Q` is
homogeneous of degree two and `ℓ` of degree one, minimizing along each ray `ty` gives `−ℓ(y)²/Q(y)`.

Cauchy–Schwarz for `Q` on `x_L + ty` and `ty + x_R`, both of support length `log 2`, where `Q ≥ 0`, gives
`ℓ(y)² ≤ (√Q(x_L) + √Q(x_R))² Q(y)`. So the dual norm is finite, `Q(y) = 0` forces `ℓ(y) = 0`, and
`inf_y F ≥ 2⟨μ, ν⟩ − 2√(Q(x_L)Q(x_R))`.

The race at the first prime becomes: Weil's form is nonnegative on stage tests iff
`2w₂⟨x_L, J x_R⟩ ≤ Q(x_L) + Q(x_R) + Φ_ε(μ, ν)` for all collar data.

## Limit

`Φ_ε` is a Schur complement: the dual norm is not expanded in an explicit Gram matrix of the
exponential moments on the interior.
