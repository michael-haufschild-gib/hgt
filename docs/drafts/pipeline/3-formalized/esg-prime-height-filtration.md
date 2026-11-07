# Prime-height filtration and geometric persistence maps

- **ID:** esg-prime-height-filtration
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** review-0611 §2.11; review-0711 §2.11
- **Statement:** The inclusion of the prime nerve at height `N≥1` into height
  `2N` is explicitly nullhomotopic. Its complementary facet spheres
  have exact birth and death thresholds, with explicit persistence maps.

## Exact target

Let `K_N` have faces the finite sets of primes with product at most `N`.
Coning every face to vertex 2 takes `K_N` into `K_{2N}`. Barycentric
interpolation gives a continuous homotopy from the actual filtration inclusion.
The geometric persistence maps have the interval law `[m,2m)`, indexed by
odd squarefree support products `m>1`. A surviving boundary sphere is preserved
up to homotopy; an expired sphere maps constantly to the basepoint. A separate
persistent homology object and barcode isomorphism are not constructed.

## Mechanism and scope

The contraction is barycentric interpolation with vertex 2. Multiplying a
face product by 2 costs at most a factor 2. The existing bouquet theorem at
each height does not by itself establish compatibility with inclusions;
the additional result here is precisely that compatibility.

This constructs a height-filtration tool. It neither removes the linear
Betti mass at a fixed height nor bounds its alternating sum. Section spaces,
divisors, winding, curvature and ampleness remain separate open targets.

## Dependencies

`HodgeTheoryWithoutVarieties.TheNerveOfTheStarCover` supplies the arithmetic
face family. `FiniteConeComplexesHaveSphereBouquets` supplies barycentric
realizations, vertex contractions and the levelwise bouquet coordinates.

## Persistence argument

Fix a finite ambient set of prime labels containing every vertex under
consideration. At height `N≥2`, write `A_N` for the star of 2 in `K_N`.
Every face outside `A_N` is an odd support `S` of product `m` satisfying
`m≤N<2m`. Every proper subface lies in `A_N`: deleting a prime divides
the product by at least 3, so adjoining 2 remains below the height.

The existing explicit bouquet equivalence uses the boundaries of the
simplices `2*S` as sphere summands. Let `F_N` be its forward map and `G_N`
its inverse up to homotopy. For `N≤M`, put
`P_NM=F_M ∘ inclusion ∘ G_N`. On the summand indexed by `S`:

- If `M<2m`, the same face is complementary at height `M`. The boundary
  formula for `F_M` says that `P_NM` is its inclusion followed by the
  terminal map of the canonical sphere homotopy. That map is homotopic
  to the identity.
- If `2m≤M`, `S` has entered `A_M`. Its whole surrounding boundary lies
  in `A_M`: the part in `A_N` remains in `A_M`, and the remaining facet
  is `S` itself. Hence `F_M` sends the whole summand to the basepoint.

Thus the actual maps between the bouquet coordinates retain precisely the
intervals `[m,2m)`. The common logarithmic lifespan is `log 2`; weights
depending only on lifespan cannot distinguish homological parities. Birth
locations retain arithmetic information, so this does not rule out more
general height weights. The theorem describes persistence maps as well as
the complementary facets at individual heights.

## Lean formalization

All declarations are in `GaloisForLFunctions.EffectiveScalingGeometry`.

- `PrimeHeightFiltration.lean`: `primeHeightDoublingHomotopy` and
  `primeHeightDoublingHomotopy_natural`: actual inclusion and compatible coning.
- `ConeFiltrationPersistence.lean`: `conePersistenceMap_surviving`,
  `conePersistenceMap_dead`, `survivingSummandHomotopy`, and
  `survivingSummandHomotopy_base`: map-level classification through conical stars.
- `PrimePersistenceIntervals.lean`: `prime_complement_lifetime`,
  `prime_complement_arithmetic`, `primePersistence_survival_iff`,
  `primePersistenceSurvivingHomotopy`, and `primePersistence_on_summand`:
  arithmetic thresholds and explicit maps, with all geometric premises discharged.
- `primeSets_iff_exists_heightFace_of_le`: faithfulness to the full prime nerve
  in any sufficiently large ambient simplex.

All three modules pass direct `lake --old env lean` checks. The capstone axiom
closures contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Comparison

Björner, [A cell complex in number theory](https://arxiv.org/abs/1101.5704),
establishes the levelwise bouquet and Betti laws. Those results already
exist in the corpus. The additional result is the explicit inclusion
map between those bouquets and its arithmetic survival threshold; no
external priority claim is made.
