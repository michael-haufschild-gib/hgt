# Weighted ideal-lattice covolume is norm times root discriminant

- **ID:** hecke-weighted-ideal-covolume
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Hecke L-functions HL7; arithmetic normalization of lattice Poisson summation
- **Statement:** The lattice obtained by multiplying both real coordinates at each complex
  place by `√2` has covolume `absNorm(I) * sqrt(abs(discr K))`, for every nonzero
  fractional ideal `I` of the number field `K`.

## Dependency audit

Corpus search found no existing weighted ideal-covolume theorem. Reuse
`NumberFieldTraceCoordinates`, the weighted ideal lattice formalized in
[ideal-lattice trace duality](weighted-ideal-lattices-have-the-arithmetic-trace-dual.md), and
`DualZLattice.covolume_span_eq_abs_det`.

Mathlib `mixedEmbedding.covolume_idealLattice` already gives the unweighted covolume
`absNorm(I) * (2⁻¹)^r₂ * sqrt(abs(discr K))`. Its `mixedEmbedding.stdBasis` uses exactly
the same index as `numberFieldMixedRealCoordinateIndex`; its coordinate representation
is `numberFieldMixedRealCoordinates`, by the three real/complex-coordinate lemmas.
`mixedEmbedding.volume_fundamentalDomain_stdBasis` is exactly `1`.

## Proof

Map the actual fractional-ideal real basis through weighted coordinates. Its integer
span is the weighted ideal lattice. Reindex the ideal basis to the mixed-coordinate
index, and compare its coordinate determinant with the determinant relative to
`mixedEmbedding.stdBasis`. Multiplying the two real coordinates at each complex
place by `√2` multiplies absolute determinant by `2^r₂`. The existing unweighted
covolume formula then gives the stated normalization.

The proof uses the existing unit volume of the standard-basis fundamental domain.
No unproved measure or discriminant normalization is assumed.

## Gates and status

- [x] Existing corpus and Mathlib normalization audited.
- [x] Dependency-closed paper proof implemented in Lean.
- [x] Direct source and transitive axiom audits.

In [NumberFieldIdealCovolume.lean](../../../../formal/GaloisForLFunctions/HTGeometry/NumberFieldIdealCovolume.lean),
namespace `GaloisForLFunctions.HTGeometry`:

- `numberFieldMixedRealCoordinates_eq_stdBasis_repr`
- `numberFieldTraceRealCoordinates_apply`
- `prod_numberFieldMixedTraceWeight`
- `volume_real_fundamentalDomain_traceCoordinates`
- `covolume_numberFieldTraceLattice`

The complete scratch and final direct `lake --old env lean` source audit pass without
warnings. The final covolume theorem and the imported ideal-span and dual-membership
theorems audit to only `propext`, `Classical.choice`, and `Quot.sound`.
The module is wired into `HTGeometry.lean`; no umbrella was compiled. Its olean is
built for the written actual-ideal theta consumer.
No limits or arithmetic premises were added.

The reindexing proof keeps its index equivalence explicit in a private lemma; the
public theorem supplies the actual `Basis.indexEquiv`. This avoids expansion of the
chosen equivalence while preserving the unconditional public statement.

[Intrinsic dual-lattice Gaussian summation](gaussian-poisson-sums-over-intrinsic-dual-lattices.md)
is also formalized. Next is theta inversion over actual fractional-ideal elements.
