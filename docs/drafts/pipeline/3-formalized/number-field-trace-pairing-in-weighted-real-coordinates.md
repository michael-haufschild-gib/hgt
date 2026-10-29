# Number-field trace pairing in weighted real coordinates

- **ID:** hecke-weighted-trace-coordinates
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Hecke L-functions HL7; arithmetic normalization of lattice Poisson summation
- **Statement:** Let `S` split each complex mixed coordinate into real and imaginary parts
  and multiply both by `√2`. Let `C` be coordinatewise complex conjugation on mixed space.
  Then `⟨S(ι(a)), S(C(ι(b)))⟩ = Tr_(K/ℚ)(ab)` for every `a,b ∈ K`.

## Proof

The real part of an embedding value is constant on each fiber of `InfinitePlace.mk`:
the chosen embedding is either the original embedding or its complex conjugate.
Summing over these finite fibers weights each place by its multiplicity. The
trace-as-sum-of-embeddings theorem, transported from algebra homomorphisms to ring
homomorphisms, therefore gives field trace as the sum of real embeddings plus twice
the real parts of complex embeddings.

Compose the existing split real-coordinate equivalence with positive diagonal scaling:
weight `1` at real coordinates and `√2` at each complex real/imaginary coordinate.
Convert it to a Euclidean continuous linear equivalence `S`. Complex conjugation is
an actual real linear equivalence `C` on mixed space. Computing the inner product gives
`Σ_real z_r y_r + 2 Σ_complex Re(z_w y_w)` after conjugating the second vector. This is
the mixed trace of `zy`. Specializing to field embeddings and applying the trace formula
proves the statement.

## Lean declarations

In [NumberFieldTraceCoordinates.lean](../../../../formal/GaloisForLFunctions/HTGeometry/NumberFieldTraceCoordinates.lean),
namespace `GaloisForLFunctions.HTGeometry`:

- `numberFieldEmbeddingReSum_eq_placeSum`, `numberField_trace_eq_embeddingReSum`
- `numberField_trace_eq_placeSum`, `sum_infinitePlaces_eq_real_add_complex`
- `numberFieldMixedTrace`, `numberFieldMixedTrace_embedding`
- `numberFieldMixedConjugation`, `numberFieldMixedTraceWeight`
- `numberFieldTraceCoordinates`, `numberFieldTraceCoordinates_apply`
- `inner_numberFieldTraceCoordinates_conjugate`
- `numberField_trace_eq_weighted_inner`

## Dependencies and validation

The construction reuses `numberFieldMixedRealCoordinates`, `positiveDiagonalLinearEquiv`,
Mathlib `trace_eq_sum_embeddings`, `RingHom.equivRatAlgHom`, and the finite-fiber method
already used by `NumberFieldUnitPlaceLog.lean`. `WithLp.linearEquiv` identifies coordinate
functions with Euclidean vectors.

The complete scratch and final direct `lake --old env lean` source audit pass without
warnings. Four transitive axiom checks, including the final field-trace identity, report
only `propext`, `Classical.choice`, and `Quot.sound`. The module is wired into
`HTGeometry.lean`; no umbrella was compiled. Its olean is built for the written
ideal-duality consumer. No limit overrides or unproved arithmetic inputs were added.

## Next target

[Weighted ideal-lattice trace duality](weighted-ideal-lattices-have-the-arithmetic-trace-dual.md)
now identifies the exact dual lattice. The subsequent
[weighted covolume theorem](weighted-ideal-lattice-covolume-is-norm-times-root-discriminant.md)
also proves that the diagonal factor `2^r₂` cancels the existing mixed-lattice factor.
