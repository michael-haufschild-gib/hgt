# No nonidentity polynomial orbit preserver fixes two orbit points

- **ID:** alst-polynomial-frobenius-many-orbit-fixed-points
- **Stage:** 5-failed
- **Type:** NO-GO WITH POSITIVE CLASSIFICATION
- **Retired claim:** On a finite prime set containing two distinct primes, a nonidentity polynomial self-map can preserve the whole prime orbit and fix two distinct points of that orbit.

## Obstruction and positive survivor
Every complex polynomial orbit preserver is uniquely
`X_p↦p^(−ib)X_p^n`, with `n∈ℕ`, `b∈ℝ`, inducing `t↦nt+b` without any
assumed clock regularity. Fixed points satisfy `(n−1)t+b=0`: nontrivial
translations have none, other nonidentity maps have exactly one.
Over `ℤ`, the translation vanishes and every endomorphism is exactly Adams.
The survivor classifies the entire family, including constant maps.

The orbit-preservation condition is global: every orbit point must map to
an orbit point. This is the category excluded by the theorem.

## Proof status
The [dependency-closed paper proof and six-module Lean audit](../3-formalized/alst-orbit-preserving-endomorphisms-are-adams.md)
are complete. Core declarations: `preservesPrimeOrbit_iff`,
`translatedAdams_eq_iff`, `translatedAdams_fixed_iff_of_ne_one`,
`translatedAdams_translation_fixed_iff`,
`preservesPrimeOrbit_two_fixed_points`, `integer_endomorphism_is_adams`.
All final plain checks passed; transitive axioms are only `propext`,
`Classical.choice`, and `Quot.sound`.
