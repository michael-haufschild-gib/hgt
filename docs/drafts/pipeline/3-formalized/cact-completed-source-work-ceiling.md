# A logarithmic ceiling for completed arithmetic source work

- **ID:** cact-source-work-ceiling
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../../../reports/review-2910/astra.md, sections 3 and 7
- **Statement:** The actual completed source work and its compact arithmetic tapers admit a
  uniform ceiling of order `R (log R)^2`, retaining multiplicity and all exterior fields.

## Goal

Replace the quartic product majorant used to admit the completed work by a scale-sensitive
arithmetic bound. This does not prove finite support: the required annular bound is a constant.
The contribution is an actual upper estimate and a uniformly summable comparison for the signed
source, with no finite-support or critical-line premise.

## Gates

- [x] Source-defined target and existing dependencies identified through corpus search.
- [x] Complete analytic argument formalized in the new programme namespace.
- [x] Individual module audited with `lake --old env lean`, umbrella imports wired.

## Approach

Let `K = xiLineTwoLogDerivConstant`, `L_R = K + log(R+4)`, and
`h_R(t) = R^4 / (R^2+t^2)^2`. Reflection gives

`pairWork(R,p,q) ≤ 2 (h_R(γp)+h_R(γq)) / (1+(γp−γq)^2)`.

The existing arithmetic Lorentzian mass bound is
`Σq 1/(1+(t−γq)^2) ≤ 8 (K+log(|t|+4))`. The elementary logarithmic comparison
`log(|t|+4) ≤ log(R+4)+|t|/R` and `2R|t| ≤ R^2+t^2` give

`h_R(t)(K+log(|t|+4)) ≤ R^2 (L_R+1)/(R^2+t^2)`.

The width-`R` Lorentzian theorem bounds the sum of the final denominator by `8 L_R/R`.
After the exact factor `1/4` in completed work and symmetry of the two rows, the proposed ceiling
is `64 R L_R (L_R+1)`. The compact taper has twice the same majorant; its bound must be independent
of the taper index. Every exchange of the two zero sums must have an explicit summability proof.

## Novelty and boundary

The corpus already proves the two Lorentzian mass bounds, pointwise reflected-work domination,
and completed source identification. Searches located no composition paying the full source by
the width-adapted logarithmic envelope. The new content is the complete summable comparison and
its application to the actual work, not a new finite-support receiver.

The positive envelope includes critical zeros. It cannot be presented as the needed selective
constant estimate. Further progress must retain more signed arithmetic cancellation.

## Formalization

Module: `GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompletedSourceWorkHasALogarithmicCeiling`.

The complete comparison above is proved by `tsum_dampedLorentzRow_le`,
`xiDampedSourceWork_le_logarithmic_ceiling`, and
`abs_xiTaperedSourceWork_le_logarithmic_ceiling`. The scalar estimates, product summability,
Fubini step, reflection comparison, and taper uniformity are proved in the same module.

Individual final audit: `lake --old env lean GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheCompletedSourceWorkHasALogarithmicCeiling.lean`.
Exit status zero; both capstones report only `propext`, `Classical.choice`, and `Quot.sound`.
The programme umbrella and `MainTheorems.lean` import the finished contribution. No umbrella build.
