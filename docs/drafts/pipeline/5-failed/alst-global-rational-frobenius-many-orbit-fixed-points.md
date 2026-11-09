# New prime variables do not create rational Frobenius maps

- **ID:** alst-global-rational-frobenius-many-orbit-fixed-points
- **Stage:** 5-failed
- **Type:** NO-GO WITH POSITIVE CLASSIFICATION
- **Retired claim:** A nonidentity rational self-map of the full prime-variable algebra can preserve the whole prime orbit and fix two distinct orbit points by introducing new primes in successive coordinates.

## Obstruction and positive survivor
Every rational coordinate family defined on and preserving the full orbit
is uniquely `X_p↦p^(−ib)X_p^n`, with `n∈ℤ`, `b∈ℝ`. No common finite
invariant prime set is required. All dependence on other prime variables
cancels in the exact cross-polynomial identities.

Six exponentials forces an algebraic clock slope; Baker independence on
one coordinate's finite frequency support makes that slope an integer.
This removes the finite-lattice premise from rational orbit rigidity.
Real or integer coefficients force `b=0`. Fixed points satisfy exactly
`(n−1)t+b=0`, so two distinct fixed orbit points force the identity.
Every translated Laurent Adams map occurs, including constants and
negative exponents.

The scope is preservation of the entire orbit with denominators nonzero
there. The theorem does not classify maps satisfying only selected orbit
incidences.

## Proof status
The [dependency-closed paper proof and four-module Lean audit](../3-formalized/alst-global-rational-orbit-preservers-are-laurent-adams.md)
are complete. Core declarations: `globalRationalPreservesPrimeOrbit_iff`,
`globalRationalPreservesPrimeOrbit_laurentAdams`,
`globalLaurentAdamsRelation_parameters_unique`,
`globalLaurentAdamsRelation_fixed_iff`,
`global_rational_preserver_two_fixed_points`,
`global_real_rational_preserver_is_laurentAdams`,
`global_integer_rational_preserver_is_laurentAdams`.
All final plain checks passed; transitive axioms are only `propext`,
`Classical.choice`, and `Quot.sound`.
