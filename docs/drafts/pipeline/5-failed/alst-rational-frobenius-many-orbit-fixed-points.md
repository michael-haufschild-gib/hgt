# No nonidentity rational orbit preserver fixes two orbit points

- **ID:** alst-rational-frobenius-many-orbit-fixed-points
- **Stage:** 5-failed
- **Type:** NO-GO WITH POSITIVE CLASSIFICATION
- **Retired claim:** On a finite prime set containing two distinct primes, a nonidentity rational self-map defined on the entire prime orbit can preserve that orbit and fix two distinct orbit points.

## Obstruction and positive survivor
Every such complex rational map is uniquely `X_p↦p^(−ib)X_p^n`, with
`n∈ℤ`, `b∈ℝ`, inducing `t↦nt+b`. Arbitrary denominators add negative
integer powers, including time reversal, but no nonlinear clocks.
The polynomial cross-identities handle arbitrary common factors.

Fixed points satisfy exactly `(n−1)t+b=0`. Nontrivial translations have
none; every other nonidentity map has exactly one. Real or integer
coefficients force `b=0`. The positive survivor classifies every map in
this category, including constants and all negative exponents.

The scope is preservation of the whole orbit, with denominators nonzero
there. Maps satisfying only finitely many orbit incidences are not covered.

## Proof status
The [dependency-closed paper proof and eight-module Lean audit](../3-formalized/alst-rational-orbit-preservers-are-laurent-adams.md)
are complete. Core declarations: `rationalPreservesPrimeOrbit_iff`,
`rationalPreservesPrimeOrbit_laurentAdams`,
`laurentAdamsRelation_parameters_unique`, `laurentAdamsRelation_fixed_iff`,
`rational_preserver_two_fixed_points`,
`real_rational_preserver_is_laurentAdams`,
`integer_rational_preserver_is_laurentAdams`.
All final plain checks passed; transitive axioms are only `propext`,
`Classical.choice`, and `Quot.sound`.
