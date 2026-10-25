# Exact signed moments of base-five digit blocks

- **ID:** biarithmetic-weighted-digit-moments
- **Stage:** 3-formalized
- **Type:** CLASSICAL FINITE-MOMENT CALIBRATION
- **Parent:** [Digital energy and tower payment](../1-in-progress/biarithmetic-digital-energy-and-prime-tower-payment.md)
- **Statement:** Every signed linear readout of all base-five words has exact first and second moments. Restricting the leading digit to one through four gives an exact block moment and a lower bound independent of the lower coefficients.

## Paper proof

For arbitrary real `x_i`, a digit uniformly ranging over zero through four has mean two
and variance two. The finite product of digit choices therefore gives

`sum_d (sum_i d_i*x_i)^2 = 5^M [2 sum_i x_i^2+4(sum_i x_i)^2]`.

This is an exact finite expansion. Independence here means only that every digit word
is enumerated once; it is not a hypothesis about the arithmetic source.
For a nonzero leading digit, the mean and variance are `5/2` and `5/4`. Hence

`sum_(a=1)^4 sum_d (a*z+sum_i d_i*x_i)^2
 =4*5^M[(5/4)z^2+2 sum_i x_i^2+((5/2)z+2 sum_i x_i)^2]`.

Dropping the two nonnegative terms proves the lower bound `5^(M+1)z^2` for
arbitrary signs of every coefficient. No lower-digit cancellation can remove the
leading-digit variance. Lean proves the formulas by splitting one digit and induction,
using exact kernel-checked arithmetic for the five possible digit values.

## Lean and scope

Module: `formal/GaloisForLFunctions/BiarithmeticGeometry/WeightedDigitMoments.lean`.
Main declarations: `sum_fiveDigitReadout`, `sum_sq_fiveDigitReadout`,
`sum_sq_fiveDigitBlock`, `fiveDigitBlock_leading_lower`.
The complete scratch and direct repository checks passed. Five declaration audits
report only `propext`, `Classical.choice`, and `Quot.sound`.

The result is classical digit-moment algebra. Its use in the exact ordinary-pronic
norm equivalence and the complete prime-tower payment domain remains on the parent
card; these later results are not claimed formalized by this moment identity alone.

- [x] Dependency-closed paper proof.
- [x] Lean proof, direct repository check, and transitive axiom audit.
- [x] Umbrella import; no umbrella compilation.
