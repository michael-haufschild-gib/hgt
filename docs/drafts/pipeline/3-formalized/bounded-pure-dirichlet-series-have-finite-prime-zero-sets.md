# Bounded pure Dirichlet series have finite-prime zero sets

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Closure tasks](fable-route-closures.md).

## Statements

Let `F` be a bounded holomorphic function on `Re s>x`, represented far right
by an absolutely convergent ordinary Dirichlet series with a nonzero positive-index
coefficient. Suppose all its zeros in the half-plane lie on `Re s=c`, with `x<c`.
For every cutoff `N₀`, there is `N≥N₀` such that deleting coefficients whose
indices are not `N`-smooth gives a bounded holomorphic function on the same
half-plane, with the original bound and exactly the same zero set.

Consequently, if every zero of `F` is a zero of `ξ`, then `F` has no zero.
There is no restriction on `x`.

## Proof

1. Kronecker approximation realizes each unitary prime twist as a limit of
   vertical translates. Montel supplies its bounded holomorphic continuation;
   absolute convergence identifies it far right. Three-lines propagates
   continuity from the far-right line to compact subsets of the half-plane.
   Hurwitz preserves purity, and coefficient uniqueness excludes zero fibres.
2. Choose real anchors `a∈(x,c)` and `b>c`. Their values are nonzero. Continuity
   at the identity of the prime torus gives a finite cutoff such that twists
   fixing those primes remain within half the original modulus at both anchors.
   Enlarge the cutoff to exceed `N₀` and retain a nonzero coefficient.
3. Give every omitted prime the same parameter `w`. On the circle this is a
   unitary twist. Poisson averaging extends the family to the closed disc with
   its original bound and joint continuity. Far right it equals the damped
   Dirichlet series and its Cauchy integral. The identity theorem propagates
   this equality, proving holomorphy in `w` throughout the half-plane.
4. The maximum principle makes both anchor discs zero-free. The argument
   principle then excludes off-line zeros in every disc fibre. Hurwitz in
   each variable shows that all closed-disc fibres have the same zero set.
5. At `w=0`, the multiplier is exactly the indicator of smooth indices.
   This is the asserted finite-prime representative.
6. For a constituent of `ξ`, the existing purity theorem puts every zero on
   the critical line. A hypothetical zero therefore gives `x<1/2`. The
   representative retains a nonzero coefficient, and its zeros are still
   zeros of `ξ`. The existing finite-prime constituent obstruction excludes it.

## Lean

Namespace `GaloisForLFunctions.ConstituentTheoryOfTheZeros`:

- `ABoundedConstituentHasNoZeros.lean`:
  `exists_smooth_zero_set_representative_of_bounded_pure`,
  `bounded_dirichlet_constituent_ne_zero`.
- `BoundedDirichletTwists.lean`: `exists_bounded_pure_primeTorus_lift`.
- `PrimeCutoffMultipliers.lean`: `primeCutoffMultiplier_zero`.
- `PoissonExtensionOfHolomorphicFamilies.lean`:
  `continuousOn_circlePoissonExtension_family`,
  `differentiableOn_circlePoissonExtension_parameter`.
- `PrimeContractionOfBoundedDirichletSeries.lean`: `exists_primeCutoff_family`.
- `PureDivisorsAreConstantInADisc.lean`:
  `unitDisc_zero_iff_center_of_boundary_and_anchors`.

All modules pass direct Lean checking and are wired into the constituent umbrella.
The assertion concerns zero sets; it does not assert a finite exponential
polynomial divisor or equality of multiplicities.
