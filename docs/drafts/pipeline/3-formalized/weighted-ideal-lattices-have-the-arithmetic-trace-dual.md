# Weighted ideal lattices have the arithmetic trace dual

- **ID:** hecke-ideal-lattice-trace-dual
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Hecke L-functions HL7; weighted number-field trace coordinates
- **Statement:** For every nonzero fractional ideal `I`, the integer dual of its weighted
  real-coordinate lattice consists exactly of the conjugated weighted embeddings of
  `FractionalIdeal.dual ℤ ℚ I`.

## Goal

Identify the arithmetic lattice on the dual side of Gaussian Poisson summation. The
trace dual is already known algebraically to equal `dual(1) * I⁻¹`. Covolume normalization,
finite residue characters, real parity factors, and unit integration remain separate targets.

## Gates

- [x] 0 → 1: precise target and dependency audit.
- [x] 1 → 2: dependency-closed proof.
- [x] 2 → 3: exact Lean theorem, direct source audit, transitive axiom audit.

## Source audit

- `HTGeometry/NumberFieldTraceCoordinates.lean` proves the exact field-trace/weighted-inner
  identity; its final source and axiom audits pass.
- `HTGeometry/DualZLatticeCovolume.lean` defines the intrinsic integer dual by the standard
  coordinate pairing. Reuse this definition instead of introducing a second dual lattice.
- Mathlib `mixedEmbedding.fractionalIdealLatticeBasis` is a real basis whose vectors are
  the mixed embeddings of `basisOfFractionalIdeal K I`, a rational basis of the field.
- `mixedEmbedding.mem_idealLattice` identifies lattice points with actual ideal elements.
- `Module.Basis.traceDual`, `traceDual_repr_apply`, and `trace_mul_traceDual` provide the
  rational trace-dual basis.
- `InnerProductSpace.ext_inner_left_basis` identifies vectors from their inner products
  against a real basis.
- `FractionalIdeal.mem_dual` gives the exact integral-trace characterization.

## Proof

Let `b` be the rational basis supplied by the ideal and `β` its weighted real embedding,
which is a real basis. If `y` belongs to the integer dual lattice, choose integers `m_i`
with `⟨β_i,y⟩=m_i`. Define the field element `c` whose coordinates in `b.traceDual` are
the rational casts of `m_i`. Trace-duality gives `Tr(b_i c)=m_i`. The weighted trace
identity and inner-product extensionality on `β` then show that `y` is the conjugated
weighted embedding of `c`.

Testing the original dual condition against every ideal element now proves
`Tr(ca)∈ℤ`, hence `c∈FractionalIdeal.dual ℤ ℚ I`. Conversely, the trace-dual membership
condition and the same weighted pairing identity immediately give integral pairings
against every ideal-lattice point. No rational-span or arithmetic-duality hypothesis is added.

## Lean declarations and validation

In [NumberFieldIdealTraceDuality.lean](../../../../formal/GaloisForLFunctions/HTGeometry/NumberFieldIdealTraceDuality.lean),
namespace `GaloisForLFunctions.HTGeometry`:

- `numberFieldTraceRealCoordinates`, `numberFieldTraceLattice`
- `mem_numberFieldTraceLattice`
- `numberFieldTraceLatticeBasis`, `span_numberFieldTraceLatticeBasis`
- `DiscreteTopology` and `IsZLattice` instances for the actual weighted lattice
- `numberFieldCoordinatePair_eq_inner`, `numberFieldTraceRealCoordinates_pair`
- `mem_dual_numberFieldTraceLattice`

The complete scratch and final direct `lake --old env lean` source audit pass without
warnings. The pairing and full dual-membership equivalence audit to only `propext`,
`Classical.choice`, and `Quot.sound`. The module is wired into `HTGeometry.lean`;
no umbrella was compiled. No limit overrides or extra arithmetic inputs were added.
Its olean is built for the written covolume consumer. The completed duality scratch is removed.

The [weighted covolume normalization](weighted-ideal-lattice-covolume-is-norm-times-root-discriminant.md)
is also formalized and audited.
