# Actual prime-weighted homology over every coefficient ring

- **ID:** esg-all-coefficient-weighted-homology
- **Stage:** 1-in-progress
- **Type:** ARITHMETIC PERSISTENCE CLASSIFICATION
- **Status:** Actual all-ring and binary persistence formalized; integer coefficient comparison pending

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

## Established mathematics

The [two-prime normal form](../3-formalized/esg-two-prime-weighted-normal-form.md)
preserves the actual height filtration and canonical integral coefficients.
Its transformed basis partitions uniquely by core and tag, with births
`m,2m,3m,6m`, row `(2,3)` and column `(-3,2)`.

The isolated truncated blocks have the coefficient windows in the target,
with zero homology outside those windows. Their categorical cycle classes
are the corresponding scalar cosets, naturally for every height inclusion.
Crossing the two-tag birth reduces the lower free coefficient modulo two;
crossing the three-tag birth includes the upper annihilator coefficient
into the ring. All within-window maps retain their coefficient
(`twoPrimeLower_free_modTwo_transition`,
`twoPrimeUpper_annihilator_free_transition`).

The original chain complex has cutoff-preserving orthogonal idempotent
core projections commuting with the boundary. Their finite sum recovers
every chain. The induced original homology projections give the canonical
linear equivalence

`Hₖ(C(N);R) ≃ ⨁c range(Pₖ,c)`.

Its coordinate at `c` is exactly `Pₖ,c`, and each coordinate commutes with the
original height map (`twoPrimeHomologyCoreEquiv`,
`twoPrimeHomologyCoreEquiv_natural`). Scalar and middle block realizations
have literal coordinate-extraction left inverses, so both are injective
(`twoPrimeBlockScalarExtraction_realization`,
`twoPrimeBlockMiddleExtraction_realization`). In the bottom, middle and top
degrees, realization after extraction equals the full original core projection.
The upper adjacent block is therefore an actual short-complex retract
(`twoPrimeUpperBlock_section`, `twoPrimeUpperBlock_projection`). Passing its
actual cycle classes through extraction and realization identifies the
middle-degree range with the upper scalar quotient
(`twoPrimeUpperCoreCoefficientEquiv`). Bottom representatives are actual
cycles, including the empty core; their original class maps identify the
bottom range with the lower scalar quotient (`twoPrimeLowerCoreCoefficientEquiv`).
Outside bottom and middle degrees,
core homology is zero: unsupported tags give zero chains, and top cycles
vanish by injectivity of `(-3,2)` (`twoPrimeCoreHomologyProjection_supported`).
Both quotient comparisons preserve every original height map
(`twoPrimeLowerCoreCoefficientEquiv_natural`,
`twoPrimeUpperCoreCoefficientEquiv_natural`).

Over `𝔽₂`, the actual core ranges are one-dimensional on exactly `[m,3m)`
and `[2m,6m)`, in consecutive degrees; all internal height maps retain their
coefficient (`twoPrimeBinaryLowerCoreEquiv_natural`,
`twoPrimeBinaryUpperCoreEquiv_natural`). Both ranges vanish outside their
stated intervals.

These statements pass direct Lean audits with transitive axioms contained
in `propext`, `Classical.choice`, `Quot.sound`.

## Remaining comparison

Identify canonical integer coefficient extension. A plain tensor-homology
base-change claim would miss the new annihilator classes over rings with
2-torsion.

## Paper block calculation

Before `2m`, only the bottom generator survives. On `[2m,3m)`, multiplication
by two gives bottom `R/2R` and next-degree `Ann_R(2)`. On `[3m,6m)`, the row
`(2,3)` is surjective because `3−2=1`. Its kernel is uniquely
`{(3c,−2c):c∈R}`: from `2a+3b=0`, take `c=a+b`. At `6m`, the top
differential injectively fills this kernel.

Bottom inclusion gives reduction modulo two. Middle inclusion sends
`a∈Ann_R(2)` to the same kernel coefficient because `(a,0)=(3a,−2a)`.
Partitioning the actual coordinate basis by core transfers these
calculations to the original homology through the verified range comparisons.
Their height diagrams and binary interval specialization are formalized;
canonical coefficient extension remains to be audited. No analytic input is assumed.

For the transfer, project the transformed basis onto one core. The boundary
deletes only two and three, so these projections commute with it. They
preserve cutoffs, are pairwise orthogonal idempotents and sum to the identity
on each chain's finite core support. Coordinate extraction is inverse to
each tagged realization. Passing these identities through actual cycle
classes establishes the direct-sum decomposition and both core quotient
comparisons, naturally in height. The remaining coefficient diagram must
identify actual integer extension with the canonical scalar map.

## Existing work and boundary

The integral case, including free-to-parity transitions, is already
[formalized](../3-formalized/esg-prime-weighted-torsion-classification.md).
The new requirement is arbitrary-ring annihilator contributions and their
actual persistence maps. This is a coefficient-sensitive topological
classification; it gives no signed Euler cancellation or arithmetic height sign.
