# Coupled-load endpoint gap

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ6
- **Statement:** One explicit positive cross-load repairs the complete fifth even source at zero and `x₇=½log(7/π)`.

Write `H₀,H₇` for the complete native fifth even source matrices and `G₀,G₇`
for their center compensation. Use kernel columns `e₀,e₁,(0,0,−420,1,−1/1568)`
and load complement `e₂,e₃−420e₂`. Their complementary Schur forms are `S₀,S₇`.
A positive common repair implies the endpoint gap `S₀/G₀+S₇/(−G₇) ≻ 0`.
The intervening source interval remains open.

## Explicit candidate

The exact origin moments are `Mₖ(X)/(3M₀(X))`, where
`X=thetaCuspSelfDualModularScale² ∈ (191/10,96/5)`.
The complete-source normalization identity is formalized as
`EvenFiveOrigin.native_normalized_zero` (canonical and standard-axiom audits passed).

Put `f₇=thetaCuspSourceTerm x₇ 1`,
`γ=2(401/1000)(1000001/1000000)(1791/200)−3`, and
`r=19/25000000000`. Let `S*(X)` be the normalized origin Schur form,
`Uret` the Schur form of the retained moments
`[Pₖ(49,14)+8rPₖ(196,35)+16r²Pₖ(784,56)]/121`, divided by `γ`.
Define

`Δ*=S*(191/10)+Uret`, `V=Uret−5Δ*/32`.

Both leading minors of `V` have kernel-checked strict rational certificates.
The candidate correction is `LᵀVL`, with rows
`L₁=(0,0,1,420,0)`, `L₂=(0,0,0,1,1568)`.

## Certified bounds; remaining assembly

- `G₇≥−γf₇²`: `EvenFiveBoundary.scaleSeven_compensation_lower`.
- With `l=3/4000000000≤exp(−21)≤r`, the complete retained-model bilinear error is bounded by
  `[8(r−l)|P₁₉₆|+16(r²−l²)|P₇₈₄|]/121` plus the polarized Cauchy tail,
  times `f₇²`: `EvenFiveBoundary.scaleSeven_retained_bilinear_error`.
  Both complete-source bounds passed canonical and standard-axiom audits.
- In Schur coordinates normalized by the three retained kernel pivots and the two pivots of `Δ*`,
  all 45 scalar error contributions are **strictly** below `1/96` (squared bounds off diagonal).
  All five pivot positivities and all strict scalar bounds are kernel-checked.
- The first numerator minor of `S*(X)+V` is positive throughout `[191/10,96/5]`.
  Its determinant factors through the positive common-kernel determinant; the remaining
  degree-30 polynomial is positive throughout the interval. After `z=10X−191`, its positive
  constant exceeds the sum of all negative coefficients, and all remaining coefficients are
  nonnegative. Both polynomial sign certificates and the factorization are kernel-checked.

The retained matrix minus `V` should have normalized diagonal
`(1,1,1,5/32,5/32)`. Strict entry errors below `1/32` then leave a positive
complete matrix, so `V` needs no shrinking. The coordinate identities and the
complete-source matrix positivity assembly remain unproved in Lean.
