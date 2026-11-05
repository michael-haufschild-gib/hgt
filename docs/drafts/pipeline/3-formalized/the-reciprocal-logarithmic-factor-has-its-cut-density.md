# The reciprocal logarithmic factor has its cut density

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** After removing its unique pole, the reciprocal logarithmic factor has a bounded analytic remainder `H(z)=1/κ(z)-R/(z+b)`. Its upper representative is continuous on the closed upper half-plane, including `H(-1)=-R/(b-1)`. The upper-minus-lower jump at `-t`, `t>1`, is `-2πiρ(t)`, where `ρ(t)=2κ(t)/((2+log(t²-1))²+π²)>0` is bounded. The jump vanishes above the cut.

## Proof

Let `p=-b` and `g(z)=(κ(z)-κ(p))/(z-p)`, with its derivative value at `p`.
The unique simple zero makes `g` analytic and nowhere zero. Its inverse has
value `R` at `p`; the divided difference of `1/g` is precisely `H`.
Thus the pole subtraction has an actual analytic value at the pole.

On the upper cut, reflection gives
`κ(-t)=(1+(1/2)log(t²-1)+iπ/2)/κ(t)`.
Subtracting the conjugate reciprocal gives the stated density; the real pole
term cancels. At `-1`, the reflected numerator stays bounded while the real
part of its logarithmic denominator tends to minus infinity. Hence
`1/κ(z)→0` from every direction, fixing the continuous branch-end value.

Uniform decay of the reciprocal and the pole term controls the remainder at
infinity. Continuity bounds its upper representative on the remaining compact
set; conjugation controls the lower side. Taking norms of the exact jump
then bounds `ρ`.

## Lean

Module `CanonicalSystemOfTheWindowTower/TheReciprocalLogarithmicFactorHasItsCutDensity.lean`.
Namespace `GaloisForLFunctions.CanonicalSystemOfTheWindowTower`.

- `analyticOnNhd_regularLogReferenceReciprocal`
- `tendsto_inv_continuedLogReferenceFactor_at_neg_one`
- `continuousOn_upperRegularLogReferenceReciprocal`
- `exists_bound_regularLogReferenceReciprocal`
- `upperRegularLogReferenceReciprocal_jump`
- `logarithmicFactorCutDensity_bounded`

Production plain audit passed. Transitive axioms are exactly
`[propext, Classical.choice, Quot.sound]`; the umbrella imports the module.
The unsubtracted Stieltjes identity remains on the
[half-line kernel card](../1-in-progress/the-half-line-logarithmic-green-kernel.md).
