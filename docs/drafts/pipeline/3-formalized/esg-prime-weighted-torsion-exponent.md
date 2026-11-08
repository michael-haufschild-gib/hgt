# Sharp torsion exponent for prime-valued homology

- **ID:** esg-prime-weighted-torsion-exponent
- **Stage:** 3-formalized
- **Type:** INTEGRAL HOMOLOGY

## Theorem

For the actual augmented prime-product cutoff complex over `ℤ`, with vertex
boundary coefficient `p` at prime `p`, a homology class is torsion if and only
if twice that class is zero. This holds at every height and exterior degree.
At height two the empty-face class is nonzero of order two.

More precisely, the saturation of the boundary lattice at height `N` is
exactly the weighted cycle lattice below `⌊N/2⌋`, including augmented degree zero.

## Proof

Every deleted prime is at least two, so a boundary lies below half the height
of its filling. Coordinate cutoffs in the free exterior lattice are saturated:
a nonzero integer multiple cannot erase a nonzero coefficient outside a cutoff.
Thus every cycle with a bounding nonzero multiple already lies below `⌊N/2⌋`.
Conversely, the prime-two Cartan identity fills twice that cycle within `N`.
Representing actual homology classes by cycles transfers this statement to
categorical homology. At height two the empty chain cannot be a boundary,
since every available vertex boundary has even coefficient, while its double
is the boundary of prime two.

## Lean and audit

- [PrimeWeightedBoundarySaturation.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeWeightedBoundarySaturation.lean):
  `primeValueCycle_saturation_iff`, `primeValueZero_saturation_iff`.
- [PrimeWeightedHomologyTorsion.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeWeightedHomologyTorsion.lean):
  `primeValueHomology_torsion_iff`, `primeValueHomology_two_torsion_nontrivial`.

Both pass direct `lake --old env lean` audits. Printed capstones depend on
exactly `[propext, Classical.choice, Quot.sound]`.

## Scope

The theorem determines the possible torsion exponent, not the number or
persistence of torsion classes. Those are determined by the
[full classification](esg-prime-weighted-torsion-classification.md).
No Euler-cancellation or height-positivity estimate follows from this result.
