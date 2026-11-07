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
intervals `[m,2m)`. The common logarithmic lifespan is `log 2`; it supplies
no distinction between even- and odd-dimensional spheres. This describes
persistence maps, not merely the dimensions at isolated heights.

The doubling homotopy and its naturality have passed direct Lean checks
with only `propext`, `Classical.choice`, `Quot.sound`. The persistence-map
extensions require their own checks before the full card is formalized.

## Comparison

Björner, [A cell complex in number theory](https://arxiv.org/abs/1101.5704),
establishes the levelwise bouquet and Betti laws. Those results already
exist in the corpus. The proposed contribution is the explicit inclusion
map between those bouquets and its arithmetic survival threshold; no
external priority claim is made.
