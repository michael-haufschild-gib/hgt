# Uniform geometric refinement of the base-five digit profile

- **ID:** biarithmetic-uniform-digit-refinement
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Quantitative digital covariance](../1-in-progress/biarithmetic-digital-profile-bounded-covariance-error.md)
- **Statement:** For every `a>1`, the grids `H_M(x)=a^(-M) D_a(floor(5^M x))` increase to a profile `F_a` uniformly on the whole real axis, with `0<=F_a(x)-H_M(x)<=4 a^(-M)/(a-1)`.

One refinement appends one base-five digit between zero and four. Its
renormalized increment is therefore bounded by a geometric term. Order
completeness constructs the limit with the exact common tail bound.
The limit is right continuous, satisfies `F_a(5x)=a F_a(x)`, and retains
the exact digit values at integers and all base-five rationals.

Lean: `BiarithmeticGeometry/DigitRefinement.lean`.
Audited declarations: `fiveDigitGrid_increment`, `fiveDigitGrid_monotone`,
`fiveDigitGrid_refinement_bound`, `fiveDigitProfile_sub_grid_bounds`,
`fiveDigitGrid_tendstoUniformly`, `fiveDigitProfile_natCast`,
`fiveDigitProfile_mul_five`, `fiveDigitProfile_continuousWithinAt_right`,
and `fiveDigitProfile_fiveAdic`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/DigitRefinement.lean`.
- [x] All nine transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Umbrella import wired; umbrella not compiled.

This classical refinement argument does not by itself establish covariance
asymptotics, the golden module classification, or the bilateral profile bridge.
