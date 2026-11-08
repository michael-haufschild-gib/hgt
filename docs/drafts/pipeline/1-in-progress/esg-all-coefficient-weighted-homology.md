# Actual prime-weighted homology over every coefficient ring

- **ID:** esg-all-coefficient-weighted-homology
- **Stage:** 1-in-progress
- **Type:** ARITHMETIC PERSISTENCE CLASSIFICATION
- **Status:** Natural truncated block homology formalized; global homology comparison pending

## Target

For every commutative ring `R`, identify actual augmented prime-weighted
homology persistence by cores of squarefree product `m` coprime to six.
A core of cardinality `k` should contribute two branches:

- Degree `k`: `R[m,2m)→R/2R[2m,3m)`, with reduction at the transition.
- Degree `k+1`: `Ann_R(2)[2m,3m)→R[3m,6m)`, with inclusion at the transition.

All other transitions retain the same coefficient until its branch dies.
The comparison must use actual chain-induced classes, commute with height
maps and identify canonical integral coefficient extension. Over `𝔽₂`, the
predicted intervals are `[m,3m)` and `[2m,6m)` in consecutive degrees.

## Available chain comparison

The [two-prime normal form](../3-formalized/esg-two-prime-weighted-normal-form.md)
constructs the actual natural chain isomorphism, transformed bounded basis,
core/tag partition and exact row `(2,3)` and column `(-3,2)`. It does not by
itself identify the actual homology quotient with the displayed branches.

The truncated block classification is formalized. `PrimeTwoPrimeBlockAlgebra`
gives the row kernel, top image and annihilator inclusion.
`PrimeTwoPrimeTruncatedBlocks` constructs exact birth submodules and height
maps. `PrimeTwoPrimeBlockHomology` identifies original categorical cycle
classes with scalar quotient classes; `PrimeTwoPrimeBlockPersistence` makes
these identifications natural. `PrimeTwoPrimeBlockWindows` proves the four
coefficient windows above and vanishing outside them. All modules pass direct
Lean audits; transitive axioms are subsets of `propext`, `Classical.choice`
and `Quot.sound`.

`PrimeTwoPrimeBlockEmbeddings` realizes the truncated upper blocks inside
the original adjacent cutoff complexes, naturally in height. Both actual
boundary matrices commute with this realization. `PrimeTwoPrimeCoreProjections`
constructs orthogonal idempotent endomorphisms of the original chain
persistence, with exact finite sum equal to every chain. Both modules pass
direct audits with the same standard axioms. Identifying each core's actual
homology contribution with its truncated block remains open.

`PrimeTwoPrimeHomologyProjections` passes this decomposition through the
original cycle-class maps: actual homology has natural orthogonal
idempotent core projections, and every class is their finite sum. Its direct
audit uses only the same standard axioms.

`PrimeTwoPrimeHomologyCoreSum` identifies original augmented homology with
the direct sum of these actual projection ranges. Its inverse coordinate
is precisely the original core projection, naturally for every height map.
Direct Lean and axiom audits pass. The remaining comparison identifies
each range with its lower or upper truncated-block quotient, including
vanishing in other degrees and canonical integer coefficient maps.

## Paper block calculation

Before `2m`, only the bottom generator survives. On `[2m,3m)`, multiplication
by two gives bottom `R/2R` and next-degree `Ann_R(2)`. On `[3m,6m)`, the row
`(2,3)` is surjective because `3−2=1`. Its kernel is uniquely
`{(3c,−2c):c∈R}`: from `2a+3b=0`, take `c=a+b`. At `6m`, the top
differential injectively fills this kernel.

Bottom inclusion gives reduction modulo two. Middle inclusion sends
`a∈Ann_R(2)` to the same kernel coefficient because `(a,0)=(3a,−2a)`.
Partitioning the actual coordinate basis by core should transfer these
calculations to the original complex. That transfer and its quotient maps
are the remaining proof obligations; no analytic input is assumed.

For the transfer, project the transformed basis onto one core. The boundary
deletes only two and three, so these projections commute with it. They
preserve cutoffs, are pairwise orthogonal idempotents and sum to the identity
on each chain's finite core support. Coordinate extraction is inverse to
each tagged realization. Passing these identities through actual cycle
classes should establish the global decomposition. The chain projection
identities are formalized; their actual homology quotient comparison remains open.

## Existing work and boundary

The integral case, including free-to-parity transitions, is already
[formalized](../3-formalized/esg-prime-weighted-torsion-classification.md).
The new requirement is arbitrary-ring annihilator contributions and their
actual persistence maps. This is a coefficient-sensitive topological
classification; it gives no signed Euler cancellation or arithmetic height sign.
