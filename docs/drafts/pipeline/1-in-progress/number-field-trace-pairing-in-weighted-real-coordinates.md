# Number-field trace pairing in weighted real coordinates

- **ID:** hecke-weighted-trace-coordinates
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Hecke L-functions HL7; arithmetic normalization of lattice Poisson summation
- **Statement:** Split each complex mixed coordinate into real and imaginary parts and
  multiply both by `√2`. If `S` is this real-coordinate equivalence and `C` is coordinatewise
  complex conjugation on mixed space, then
  `⟨S(ι(a)), S(C(ι(b)))⟩ = Tr_(K/ℚ)(ab)` for every `a,b ∈ K`.

## Goal

Identify the metric and conjugation required to transport Euclidean Poisson summation to
ideal lattices. The subsequent equality of the Euclidean dual ideal lattice with the
embedded inverse-different ideal, and its covolume normalization, remain separate targets.

## Gates

- [x] 0 → 1: statement fixed; reusable sources located and inspected.
- [ ] 1 → 2: complete dependency-closed proof.
- [ ] 2 → 3: exact Lean theorem, direct source audit, transitive axiom audit.

## Dependency audit

- `HTGeometry/NumberFieldMixedRealCoordinates.lean` gives the unweighted real-coordinate
  linear equivalence, with index set `real places ⊕ (complex places × Fin 2)`.
- `HTGeometry/NumberFieldUnitPlaceLog.lean`, `numberFieldEmbeddingSum_eq_placeSum`, supplies
  the finite-fiber summation method and `InfinitePlace.card_filter_mk_eq`.
- Mathlib `InfinitePlace.embedding_mk_eq` says the chosen place embedding is either the
  original embedding or its complex conjugate. Real parts are therefore constant on each fiber.
- Mathlib `trace_eq_sum_embeddings` expresses field trace as the sum over algebra
  embeddings. `RingHom.equivRatAlgHom` converts these to the complex ring embeddings.
- `HTGeometry/DualZLatticeCovolume.lean` will later convert perfectly paired bases into
  exact dual lattices.
- Mathlib `mixedEmbedding.covolume_idealLattice` gives
  `absNorm(I) * 2^(−r₂) * sqrt(abs(discr K))`; weighting contributes `2^r₂`.
- Mathlib `FractionalIdeal.mem_dual`, `dual_eq_mul_inv`, `dual_mul_self`, and `dual_dual`
  give the algebraic trace dual. No Euclidean/arithmetic identification is assumed.

## Approach

1. Regroup real parts of complex embeddings by `InfinitePlace.mk`.
2. Apply the trace-as-sum formula and split multiplicities into real and complex places.
3. Construct the positive diagonal weight on existing real coordinates and the resulting
   Euclidean continuous linear equivalence.
4. Compute its inner product after conjugating the second mixed vector. At real places
   this is multiplication; at complex places it is twice the real part of multiplication.
5. Specialize to field embeddings and apply step 2.

## Status

`/tmp/HeckeWeightedTraceScratch.lean` contains the finite-fiber real-part summation
lemma and exact API checks. It has not been compiled; theta-characteristics verification
remains the current dependent proof task.
