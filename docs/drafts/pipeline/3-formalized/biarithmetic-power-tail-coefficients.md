# Power-tail differences have an exact square-energy threshold

- **ID:** biarithmetic-power-tail-coefficients
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Critical continuum defect](../1-in-progress/biarithmetic-critical-payment-has-continuum-defect.md)
- **Statement:** For every positive `α`, coefficients `g(0)=-1` and `g(n+1)=(n+1)^(-α)-(n+2)^(-α)` have absolute sum two, total sum zero, and inclusive partial sum `-(M+1)^(-α)`. Their partial sums are square summable exactly when `α>1/2`.

Monotonicity gives nonnegative tail differences. Finite telescoping gives
both signed and absolute partial sums; the power-tail limit identifies
their infinite sums. Squaring reduces the energy to the classical shifted
power series with exponent `-2α`.

Lean: `BiarithmeticGeometry/PowerTailCoefficients.lean`.
Audited declarations: `criticalPowerCoeff_partialSum`,
`summable_abs_criticalPowerCoeff`, `tsum_abs_criticalPowerCoeff`,
`tsum_criticalPowerCoeff`, and `summable_sq_criticalPowerCoeff_partialSum_iff`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/PowerTailCoefficients.lean`.
- [x] All five transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Umbrella import wired; umbrella not compiled.

Finite independence modulo square sums and the actual Wiener quotient
dimension require their separate formalizations.
