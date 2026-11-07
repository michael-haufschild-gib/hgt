# Bianchi reduction and compact core

- **ID:** bianchi-reduction-and-compact-core
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [cubic theta residue](../1-in-progress/cubic-theta-residue-and-gauss-coefficients.md)
- **Statement:** Every point of `SL₂(ℂ)/SU₂` has an Eisenstein integral translate with horizontal squared norm at most `1/3` and height at least `√(2/3)`. Every finite-index integral subgroup has a finite cusp cover with compact truncations.

Iwasawa factorization identifies the quotient with upper half-space. Height
is the inverse squared norm of the bottom row. Integral rows have finite
bounded-energy sublevels, hence every orbit attains maximal height. Translate
horizontally to a nearest Eisenstein integer; the hexagonal lattice has squared
covering radius `1/3`. Inversion and height maximality force `|z|²+v²≥1`,
so `v²≥2/3`. Finite coset representatives transfer this cover to any finite-index
subgroup; truncation yields a finite union of compact coordinate images.

Source: external OpenAI `Eisenstein/Rows.lean`, `HyperbolicSpace.lean`,
`QuadraticSieve/HighKernelGeometry.lean`, and `Eisenstein/QuotientTopology.lean`.
Lean modules: `HyperbolicThreeSpace`, `EisensteinNearestPoint`, and
`BianchiReductionAndCompactCore` in `MetaplecticMobiusDescent/`.
Endpoints: `upperCoordinatesHomeomorph`, `exists_eisenstein_distance_sq_le_third`,
`exists_maximal_integral_height`, `bianchi_ford_cover`,
`bianchi_reduction_height_floor`, `finiteIndex_compact_core_cusp_cover`, and
`globalKubotaKernel_compact_core_cusp_cover`. All three direct Lean checks
pass; twelve transitive endpoint audits use only `propext`, `Classical.choice`,
and `Quot.sound`. Umbrella wired.

Sobolev compactness, finite invariant quotient volume, and the cubic residual
function remain separate obligations.
