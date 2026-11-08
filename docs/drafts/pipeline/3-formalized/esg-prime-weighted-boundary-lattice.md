# Exact integral boundary lattice for prime weights

- **ID:** esg-prime-weighted-boundary-lattice
- **Stage:** 3-formalized
- **Type:** FILTERED INTEGRAL BOUNDARIES

## Theorem

Let `O_k(t)` be the odd-face lattice in exterior degree `k` and product
cutoff `t`. Give each prime vertex boundary coefficient equal to that prime.
In positive degree, the natural cycle coordinates
`Q=O+e₃∧δ₂` send actual boundaries at height `N` exactly onto

`D_k(N)=O_k(⌊N/3⌋)+2O_k(⌊N/2⌋)+(O_k(⌊N/2⌋)∩ker(e₃∧·))`.

In empty degree the coordinate map is the identity and the same boundary
formula holds. The last summand is the span of bounded odd faces containing
three, hence zero in empty degree.
The joint projection onto integral coefficients on `m≤N<2m` and parity
coefficients on `2m≤N<3m` for odd faces omitting three is surjective, with
kernel exactly `D_k(N)`. The coefficient criterion holds in every exterior
degree. The actual categorical comparison remains a separate proof obligation.

## Proof

Split a filling as `y=o+e₂∧v`, with `o` odd at height `N` and `v` odd at
height `⌊N/2⌋`. Weighted Cartan gives

`Q(dy)=do+2v−e₃∧dv`.

The odd differential lowers height by three, so the first term is in the
low summand. The last term has half height and is killed by adjoining three
again. This proves the forward containment.

For the reverse containment, put `P=d((e₃−e₂)∧·)`. A low odd chain `z` is
the coordinate of the boundary filled by `(e₃−e₂)∧Pz`. A doubled half-height
chain is filled by `e₂∧Pz`. If `z` has half height and `e₃∧z=0`, then
`Pz=−d(e₂∧z)`. All three fillings lie below `N`; `QPz=z` supplies their
coordinates.

The empty-degree Cartan identity gives the same decomposition without a
lower differential. Coordinate contraction is a left inverse to a prime cone
on empty chains, so its kernel vanishes. The low and doubled fillings remain
valid in this degree.

Contraction by a prime coordinate recovers the projection onto faces
omitting that prime. Consequently its cone kernel consists exactly of faces
containing the prime, including inside each odd cutoff.

For the coefficient criterion, the lattice is contained in the half cutoff
and has zero parity in the torsion window. Conversely, expand a half-height
chain in the exterior basis. Each term is low, contains three, or lies in the
torsion window. In the last case its even coefficient puts it in the doubled
summand. Free and torsion windows are disjoint; lifting each finitely supported
parity coefficient to an integer proves joint surjectivity.

The coefficient height map retains the old free part in the new free window
and restricts `cast₂(old free)+old parity` to the new torsion window. For a
born face with nonzero coefficient, the source height lies either below `2m`
or at least `2m`; exactly one source component contributes. This proves
compatibility with odd-chain inclusions. Surjectivity transfers identity and
composition to these explicit coefficient maps.

The prime divisors of a face product are exactly its vertices. Omitting two
and three is therefore equivalent to coprimality with six. The existing
squarefree product equivalence reindexes parity coefficients without changing
their values or exterior degree.

## Lean and audit

[PrimeWeightedBoundaryCoordinates.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeWeightedBoundaryCoordinates.lean)
proves `primeValueBoundaryCoordinates_eq_lattice`.
[PrimeConeKernel.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeConeKernel.lean)
proves `primeOddConeKernel_eq_span_basis`.
[PrimeWeightedParityCoordinates.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeWeightedParityCoordinates.lean)
proves `primeValueCoordinateLattice_iff`,
`primeValueHomologyProjection_eq_zero_iff` and
`primeValueHomologyProjection_surjective`.
[PrimeWeightedAugmentedBoundary.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeWeightedAugmentedBoundary.lean)
proves `primeValueZeroBoundary_eq_lattice`.
[PrimeWeightedCoordinatePersistence.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeWeightedCoordinatePersistence.lean)
proves `primeValueHomologyProjection_natural` and defines the verified
`primeValueCoordinatePersistence` functor.
[PrimeWeightedSquarefreeIndices.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeWeightedSquarefreeIndices.lean)
proves `primeFaceProduct_coprime_six_iff` and `primeTorsionArithmeticEquiv`.
All pass direct `lake --old env lean` audits; printed capstones use exactly
`[propext, Classical.choice, Quot.sound]`.

## Scope

The integral cycle equivalence is essential: arbitrary coefficient rings
with two-torsion need not have the same cycle coordinates. Weighted homology
itself is classical; this theorem identifies the exact prime-product boundary
lattice. Transport of this coefficient functor to actual augmented homology remains
the [classification target](../1-in-progress/esg-prime-weighted-torsion-classification.md).
