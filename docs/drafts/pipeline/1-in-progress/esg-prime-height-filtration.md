# Prime-height filtration and geometric contraction

- **ID:** esg-prime-height-filtration
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** review-0611 §2.11; review-0711 §2.11
- **Statement:** The inclusion of the prime nerve at height `N` into height
  `2N` is explicitly nullhomotopic. Its sphere generators have arithmetic
  birth and death thresholds, which should determine the persistence maps.

## Exact target

Let `K_N` have faces the finite sets of primes with product at most `N`.
Coning every face to vertex 2 takes `K_N` into `K_{2N}`. Construct the
continuous homotopy, with the actual filtration inclusion at one endpoint.
The stronger target is the persistence decomposition into intervals `[m,2m)`
indexed by odd squarefree `m>1`, in degree `ω(m)−1`.

## Mechanism and scope

The contraction is barycentric interpolation with vertex 2. Multiplying a
face product by 2 costs at most a factor 2. The existing bouquet theorem at
each height does not by itself establish compatibility with inclusions;
that compatibility must be proved to claim the interval decomposition.

This constructs a height-filtration tool. It neither removes the linear
Betti mass at a fixed height nor bounds its alternating sum. Section spaces,
divisors, winding, curvature and ampleness remain separate open targets.

## Dependencies

`HodgeTheoryWithoutVarieties.TheNerveOfTheStarCover` supplies the arithmetic
face family. `FiniteConeComplexesHaveSphereBouquets` supplies barycentric
realizations and vertex contractions. Corpus novelty and dependency audits
must distinguish the new filtration maps from the known levelwise bouquet.
