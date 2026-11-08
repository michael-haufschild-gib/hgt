# The vertical trace of rational zero relocation

- **ID:** the-vertical-trace-of-zero-relocation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Although ordinary mean spectra erase rational zero relocation, a quadratic or quartic vertical rescaling detects every off-line quartet.

## Exact result

For the literal monic relocation factor, write `δ=Re ρ−1/2`, `η=Im ρ`, `z=s−1/2`,

`A=2(η²−δ²)−γ₁²−γ₂²`,
`B=(η²+δ²)²−γ₁²γ₂²`.

Its numerator minus denominator equals `Az²+B`. For every fixed real `σ`,

`t²(R(σ+it)−1) → −A`.

If `A=0`, then

`t⁴(R(σ+it)−1) → B`.

When `A=0`, the exact positive decomposition is

`B=4δ⁴+2δ²(γ₁²+γ₂²)+(γ₁²−γ₂²)²/4`.

Consequently `B≥4δ⁴>0` when `δ≠0`. Thus every off-line quartet has a nonzero quadratic trace or a positive quartic trace.

## Proof

Expand the two monic quartics in `z=s−1/2`. Reflection symmetry cancels odd powers; the leading fourth powers cancel in the difference, leaving `Az²+B`. Along every fixed vertical line, `z/t→i` and `D(σ+it)/t⁴→1`. Dividing the exact difference by `D` gives the quadratic limit. If `A=0`, the difference is constant and gives the quartic limit.

The equation `A=0` gives `η²=δ²+(γ₁²+γ₂²)/2`. Substitution into `B` yields the displayed sum of nonnegative terms. Its first term is strictly positive for an off-line target. The limits need no restriction on `σ`: the denominator is eventually nonzero even on the critical line.

## Relevance

This is a positive invariant left after the mean-square obstruction: high-height averages lose the transient, but suitably rescaled high-height data retain it. The statement does not decide AAL or prove that planted poles are cancelled by actual zeta zeros.

## Lean certificate

Module: `ArithmeticPositiveDuality/TheVerticalTraceOfZeroRelocation.lean`.
Capstones: `zeroRelocationNum_sub_den`,
`tendsto_quadratic_vertical_relocation_error`,
`tendsto_quartic_vertical_relocation_error`,
`quarticCoefficient_eq_of_quadratic_zero`,
`quarticCoefficient_ge_of_quadratic_zero`,
`zeroRelocation_has_nonzero_vertical_trace`.

The final direct `lake --old env lean` check passed without warnings.
All six capstones have exactly `propext`, `Classical.choice`, `Quot.sound`.
The module is imported by its umbrella. Together with
[mean-spectrum invariance](zero-relocation-is-invisible-to-besicovitch-averages.md),
this distinguishes information erased by ordinary averaging from information
retained by rescaled vertical limits.
