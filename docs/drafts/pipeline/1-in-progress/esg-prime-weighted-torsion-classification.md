# Torsion of the prime-valued boundary

- **ID:** esg-prime-weighted-torsion-classification
- **Stage:** 1-in-progress
- **Type:** INTEGRAL HOMOLOGY

## Exact targets

Let the vertex boundary coefficient be the prime itself. Every torsion class
of actual integral augmented homology is killed by two; this and the exact
boundary-saturation law are formalized below. The remaining target is the
full group classification together with its persistence maps.

The proposed full classification in exterior degree `k` is

`H_k(N;ℤ) ≅ ℤ^b ⊕ (ℤ/2)^t`,

where `b` counts odd squarefree `m` with `ω(m)=k` and `m≤N<2m`, and `t` counts
squarefree `m` coprime to six with `ω(m)=k` and `2m≤N<3m`.
The torsion subfunctor should have intervals `[2m,3m)` with coefficient `ℤ/2`.
An integral natural splitting of the entire homology functor is not asserted.

## Boundary saturation argument

Every weighted boundary lowers prime-product height by at least two.
The cutoff submodule is saturated in the free exterior lattice: if a nonzero
integer multiple of a chain lies below a cutoff, its basis coefficients show
that the chain itself lies below that cutoff. Thus a cycle with a nonzero
multiple bounding at `N` lies below `⌊N/2⌋`.

Conversely, Cartan's identity for prime two gives `d(2∧x)=2x` on weighted
cycles. A cycle below `⌊N/2⌋` therefore has its double bounding at `N`.
The same argument includes the empty augmented degree.
[PrimeWeightedBoundarySaturation.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeWeightedBoundarySaturation.lean)
formalizes this exact chain-level saturation and exponent-two criterion:
`primeValueCycle_saturation_iff`, `primeValueZero_saturation_iff`,
`primeValueCycle_torsion_iff_double_boundary`,
`primeValueZero_torsion_iff_double_boundary`. Its direct Lean audit passes;
printed capstones use exactly `[propext, Classical.choice, Quot.sound]`.
[PrimeWeightedHomologyTorsion.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeWeightedHomologyTorsion.lean)
proves `primeValueHomology_torsion_iff` for actual categorical homology and
`primeValueHomology_two_torsion_nontrivial` at height two. Both pass the direct
Lean audit with the same three standard axioms.

## Stronger persistence target and direct basis route

Let `u=e₃−e₂`, `z=3e₂−2e₃`, and `w_p=e_p−pu` for primes `p≥5`.
The prime-valued boundary sends `u` to one and kills `z,w_p`; these vectors
form a unimodular basis of the integral vertex lattice. For a prime support
`S` avoiding two and three, put `m=∏S` and `w_S=∧_{p∈S}w_p`.
The proposed cycle basis consists of `w_S` at height `m` and `z∧w_S` at
height `3m`. The proposed boundary lattice at `N` is generated diagonally by

- `2w_S` when `2m≤N`;
- `w_S` when `3m≤N`;
- `z∧w_S` when `6m≤N`.

This would give the full integral persistence functor: one summand is `ℤ`
on `[m,2m)`, then `ℤ/2` on `[2m,3m)`, with reduction modulo two at the
transition; the other is `ℤ` on `[3m,6m)` in exterior degree `|S|+1`.
Thus an objectwise free-plus-torsion classification would not split naturally
into those two parts.

The boundary identities are `d(e₂∧w_S)=2w_S`,
`d(e₃∧w_S)=3w_S`, and `d(e₂∧e₃∧S)=−z∧w_S`.
The last identity uses `w_S=S−u∧dS`. Lower terms have product at most
`6m/p` with `p≥5`, so they fit below the required cutoff.
The exact cutoff cycle basis is formalized through the projection below.
Its wedge description and the full diagonal boundary lattice still require
a dependency-closed proof and Lean audit. This stronger full
persistence statement remains a conjecture.

A direct cycle-coordinate construction uses the Bézout projection
`P=d((e₃−e₂)∧·)` and corrected odd projection `Q=O+e₃∧δ₂`.
For an integral weighted cycle, its two-deletion lies below `⌊N/3⌋`:
`d(Ox)+2δ₂x=0`, the first term has that height, and the coordinate cutoff
is saturated. Both inverse maps preserve the original height; the actual
natural cycle-coordinate equivalence and basis are now formalized.

In positive exterior degree, the formalized exact boundary lattice in those odd coordinates is

`O(⌊N/3⌋) + 2O(⌊N/2⌋) + (O(⌊N/2⌋) ∩ ker(e₃∧·))`.

Splitting a filling into its odd part and its two-cone gives the forward
containment. The three reverse fillings use respectively the Bézout cone,
the two-cone of a projected cycle, and the negative two-cone of a chain
annihilated by adjoining three. Identifying the last kernel with coordinates
containing three supplies its coordinate description.
[PrimeWeightedBoundaryCoordinates.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeWeightedBoundaryCoordinates.lean)
proves `primeValueBoundaryCoordinates_eq_lattice`; its direct audit passes with
`[propext, Classical.choice, Quot.sound]`.
[PrimeWeightedParityCoordinates.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeWeightedParityCoordinates.lean)
proves the joint free/parity projection is surjective with exactly this lattice
as kernel, in every exterior degree; its direct audit uses the same axioms.
[PrimeWeightedAugmentedBoundary.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeWeightedAugmentedBoundary.lean)
proves the actual empty-degree boundary formula `primeValueZeroBoundary_eq_lattice`,
with the same direct audit and axioms. Actual homology persistence remains
unformalized.

## Formal tools for the classification

[PrimeOddCutoffComplex.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeOddCutoffComplex.lean)
constructs the actual prime-two-deleted subcomplex for every vertex functional.
`primeOddDifferential_third_cutoff` proves its factor-three height decrease;
`primeOddPersistenceToFull` gives its natural inclusion in the full complex.
[PrimeTwoChainSplitting.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeTwoChainSplitting.lean)
proves `primeCutoffTwoSplit`, the actual decomposition into odd chains and
half-height prime-two cones. Both direct audits pass with the three standard
axioms.
[PrimeWeightedCycleHeight.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeWeightedCycleHeight.lean)
proves `primeValueCycle_twoDeletion_third`, the sharper factor-three height
bound for the even component of integral weighted cycles. Its direct audit
passes with the same standard axioms.
[PrimeWeightedCycleCoordinates.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeWeightedCycleCoordinates.lean)
proves `primeValueCycleOddEquiv`, its height naturality, and the actual basis
`primeValueCutoffCycleBasis`. Its direct audit passes with the same standard
axioms. The [cycle-coordinate theorem](../3-formalized/esg-prime-weighted-cycle-coordinates.md)
is closed; the boundary lattice and full persistence classification remain open.

[PrimeConeKernel.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeConeKernel.lean)
proves `primeOddConeKernel_eq_span_basis`: inside each odd cutoff, adjoining
any prime has kernel exactly the coordinate span of faces containing that
prime. Its direct audit passes with the three standard axioms. This identifies
the third summand of the exact boundary lattice.

## Existing theory and scope

Weighted simplicial homology and weighted path torsion are classical
[Ren–Wu–Wu](https://arxiv.org/abs/1708.06722). General torsion structure theorems
for weighted simplicial complexes over formal power-series discrete valuation
rings are developed by [Li–Reidys](https://arxiv.org/abs/2205.03435) and
[Bura–Dutta–Li–Reidys](https://arxiv.org/abs/2206.04612).
No novelty claim is made for weighted homology or its general structure theory.
The proposed arithmetic result is the exact prime-product torsion window and
its actual persistence maps. The full classification remains a conjecture.
