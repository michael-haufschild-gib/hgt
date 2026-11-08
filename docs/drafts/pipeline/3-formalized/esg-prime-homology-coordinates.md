# Arithmetic barcode of actual prime-cutoff homology

- **ID:** esg-prime-homology-coordinates
- **Stage:** 3-formalized
- **Type:** CATEGORICAL HOMOLOGY PERSISTENCE

## Exact statement

Over any commutative ring, actual augmented prime-cutoff homology in exterior
degree `k` is naturally isomorphic to finitely supported coefficients on odd
squarefree integers `m` with `ω(m)=k` and `m≤N<2m`. Height inclusions retain each
coefficient until `2m`. The empty support gives precisely the interval `[1,2)`.

This is an isomorphism of the existing categorical homology persistence
functor. On actual cycle classes, the concrete short-complex comparison takes
the unchanged odd exterior coefficients. Integer labels are the products of
those prime supports; the inverse takes the prime divisor set.

## Proof

The restricted differential's kernel is the ambient cycle submodule within
the cutoff. Odd projection identifies it with bounded odd chains. Projecting
further onto surviving coordinates is surjective, and the exact boundary-height
law identifies its kernel with the actual boundary range.

The first isomorphism theorem and the canonical module-homology quotient
comparison give the objectwise equivalence. Every homology element has an actual
cycle representative. Homology maps take its class to the class of the same
inclusion image, and odd coordinate projection commutes with these inclusions.
This proves naturality.

Finally, the explicit three-term complexes are naturally isomorphic to the
adjacent-degree complexes of the original chain functor. The comparison is
identity on all three chain modules. Applying the homology functor gives the
claimed natural isomorphism for the original persistence object. In degree
zero, every chain is a cycle and the augmented boundary-image identity gives
the same quotient proof. The empty product is one, so its lifetime is `[1,2)`.

Unique prime factorization identifies supports of cardinality `k` with squarefree
integers having `k` distinct prime factors. The product is odd exactly when two
is absent. Reindexing coefficients through this equivalence preserves the
critical windows and commutes with all coefficient restrictions.

## Lean realization

[PrimeHomologyCoordinates.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeHomologyCoordinates.lean),
namespace `GaloisForLFunctions.EffectiveScalingGeometry`:

- `primeCycleCriticalProjection_ker` identifies actual boundaries.
- `primeShortHomologyEquiv_class` identifies actual cycle-class coordinates.
- `primeShortHomologyEquiv_natural` controls actual homology maps.
- `primeHomologyCriticalIsoSucc` is the natural persistence isomorphism.

[PrimeAugmentedHomology.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeAugmentedHomology.lean):

- `primeCriticalFaces_zero_iff` gives the empty-face lifetime.
- `primeHomologyCriticalIsoZero` covers augmented degree zero.
- `primeHomologyCriticalIso` combines every degree.

[PrimeSquarefreeIndices.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeSquarefreeIndices.lean):
`primeFaceSquarefreeEquiv`, `primeFaceSquarefreeEquiv_critical`.

[PrimeArithmeticPersistence.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeArithmeticPersistence.lean):
`primeCriticalArithmeticEquiv_natural`, `primeHomologySquarefreeIntervalIso`.

All four direct `lake --old env lean` audits pass. Printed capstones use exactly
`[propext, Classical.choice, Quot.sound]`. Imported by the programme umbrella.

## Scope

The Betti-rank formula is classical; see
[Björner, Theorem 3.1](https://arxiv.org/abs/1101.5704). This construction supplies
the actual maps and natural integral comparison, over every commutative ring.
Compatibility with canonical coefficient extension is proved in the
[integral persistence card](esg-integral-prime-persistence.md).
No Euler-cancellation estimate is claimed.
