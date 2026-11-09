# Parity of ordinate relations and the unit mass infimum

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Obstacles:** B13, B112; simultaneous positive annihilation at fixed ordinates.
- **Novelty:** Odd integer relations are the complete obstruction to near-unit exact annihilation. When none occurs, every exact mass above one is attained.

## Theorem

Fix a nonempty finite family `gamma : I → ℝ` and any real abscissa `beta`. The following are equivalent:

1. For every `delta>0`, a positive two-prime polynomial with constant coefficient one annihilates every `beta+i gamma_i` and has tail mass below `1+delta`.
2. Every integer relation `sum n_i gamma_i=0` has even coefficient sum `sum n_i`.

Under condition 2, every prescribed tail mass `H>1` is attained exactly.

## Proof

Let `D` be the simultaneous phases of nonconstant monomials, with logarithmic frequency `L_d=d_0 log 2+d_1 log 3`.

Compact group recurrence identifies the closure of nonnegative powers of the two prime phases with the closure of their integer powers. Density of the integer span of `log 2, log 3` then identifies this with the continuous phase-line hull. Translating the monomial semigroup by a nonconstant monomial shows that removing the constant monomial preserves this closure.

The corpus theorem `screwHull_eq_screwAnnihilator` characterizes the hull by its integer relations. At the all-half-period point, a character evaluates to `(-1)^(sum n_i)`. Hence the all-minus-one complex phase belongs to `closure D` exactly under condition 2. Multiplication by that phase makes the hull centrally symmetric.

For a nonempty set with symmetric closure in finite dimension, work in its linear span. Symmetry puts zero in its affine span, so its convex hull has nonempty interior there. Symmetry of the closure puts zero in the interior of the closed convex hull; the convex interior-closure identity puts it in the interior of the convex hull itself. Every strict radial contraction of a closure point therefore belongs to the convex hull of the original set.

For `H>1`, express the constant vector `-1/H` as a finite convex combination of actual nonconstant monomial phases. Multiply the weights by `H` and the coefficient at exponent `d` by `exp(beta L_d)`. Adding the constant term one gives exact simultaneous annihilation and tail mass exactly `H`.

Conversely, exact cancellation at each target gives total weighted squared phase defect `2 N (H-1)`, where `N=card I`. Cancellation also forces `H>=1`. If every supported monomial had some coordinate defect at least `epsilon`, total defect would be at least `epsilon^2 H>=epsilon^2`. Taking `H-1<epsilon^2/(2N)` contradicts this. Thus the antipodal point lies in `closure D`, forcing condition 2.

## Lean certificates

Owner: `formal/GaloisForLFunctions/ArithmeticPositiveDuality/`.

- `ParityClassifiesNearUnitAnnihilation.lean`: `near_unit_annihilation_iff_even_relations` and `exists_exact_mass_annihilator_of_even_relations`.
- `TwoPrimePhaseHull.lean`: exact nonconstant phase closure.
- `SymmetricPhaseConvexity.lean`: exact convex correction from symmetric closure.
- `PhaseHullParity.lean`: character parity and antipodal convex representations.
- `PositivePhaseCombinations.lean`: positive polynomial realization with exact mass.

All five modules pass direct `lake --old env lean` audits and are wired into the owner umbrella. Capstone axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`. The classification, exact-mass strengthening, and supporting lemmas count as one contribution.

