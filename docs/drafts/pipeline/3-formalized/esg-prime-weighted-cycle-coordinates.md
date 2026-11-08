# Natural integral coordinates for prime-weighted cycles

- **ID:** esg-prime-weighted-cycle-coordinates
- **Stage:** 3-formalized
- **Type:** FILTERED INTEGRAL CYCLE LATTICES

## Theorem

In every positive exterior degree, integral cycles for the prime-valued
boundary at height `N` are naturally isomorphic to the free lattice on odd
prime faces of product at most `N`. The representative of an odd chain is

`P(y)=d((e₃−e₂)∧y)`.

The inverse is `Q(x)=O(x)+e₃∧δ₂(x)`, where `O` discards faces containing two
and `δ₂` contracts the prime-two coordinate. Both maps preserve the original
height and commute with all height inclusions. They give an actual integral
basis of the cycle module.

## Proof

The coordinate Cartan identity splits every chain as `Ox+e₂∧δ₂x`.
The odd subcomplex has minimum prime three, so its boundary lowers product
height by a factor of three. For an integral weighted cycle,
`d(Ox)+2δ₂x=0`; saturation of the coordinate cutoff lattice therefore places
`δ₂x` below `⌊N/3⌋`. Hence the correction in `Q` fits within `N`.

The Bézout identity `3−2=1` gives `P(y)=y−(e₃−e₂)∧dy`.
For odd `y`, the second term also fits within `N`. The projector fixes cycles
and kills every cone of `e₃−e₂`, whose square is zero. Since
`Q(x)=x+(e₃−e₂)∧δ₂x`, this proves `PQ=id` on cycles.
For odd `y`, the displayed expansion of `P` gives
`OPy=y−e₃∧dy` and `δ₂Py=dy`, proving `QP=id`.
The maps use the same ambient formulas at every height, so naturality is literal.

## Lean and audit

- [PrimeOddCutoffComplex.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeOddCutoffComplex.lean):
  actual odd subcomplex and `primeOddDifferential_third_cutoff`.
- [PrimeTwoChainSplitting.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeTwoChainSplitting.lean):
  `primeCutoffTwoSplit`.
- [PrimeWeightedCycleHeight.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeWeightedCycleHeight.lean):
  `primeValueCycle_twoDeletion_third`.
- [PrimeWeightedCycleCoordinates.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeWeightedCycleCoordinates.lean):
  `primeValueCycleOddEquiv`, `primeValueCycleToOdd_natural`,
  `primeValueCutoffCycleBasis_val`.

All pass direct `lake --old env lean` audits. Printed capstones use exactly
`[propext, Classical.choice, Quot.sound]`.

## Scope

This identifies cycles and their height maps. The
[boundary lattice](esg-prime-weighted-boundary-lattice.md) is also formalized;
actual homology persistence remains in the
[weighted torsion target](../1-in-progress/esg-prime-weighted-torsion-classification.md).
The inverse height bound uses integer saturation and is not asserted over
rings with two-torsion.
