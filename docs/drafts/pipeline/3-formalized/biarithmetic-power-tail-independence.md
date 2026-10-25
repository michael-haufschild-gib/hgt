# Power tails remain independent modulo square partial sums

- **ID:** biarithmetic-power-tail-independence
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Critical continuum defect](../1-in-progress/biarithmetic-critical-payment-has-continuum-defect.md)
- **Statement:** Every nonzero finite complex combination of distinct tails `(M+1)^(-α)`, with all active exponents at most one half, has divergent square energy. Consequently their coefficient differences are linearly independent modulo the square-partial-sum domain.

Divide by the tail with the smallest active exponent. Each larger exponent
vanishes in the ratio limit, leaving the nonzero coefficient of that
smallest exponent. Eventually the combination's norm is at least half
that coefficient norm times its tail. Square summability would therefore
force summability of a divergent power series. Filtering zero coefficients
and taking a minimum proves the assertion for every finite family.

Lean: `BiarithmeticGeometry/PowerTailIndependence.lean`.
Audited declarations: `powerTailCombination_ratio_tendsto`,
`not_summable_sq_powerTailCombination_of_min`,
`not_summable_sq_powerTailCombination`,
`criticalPowerCoeff_independent_mod_squareSums`, and
`criticalPowerCoeff_interval_independent_mod_squareSums`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/PowerTailIndependence.lean`.
- [x] All five transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Umbrella import wired; umbrella not compiled.

The actual Wiener closure-defect dimension requires the separate lifted
family and quotient comparison.
