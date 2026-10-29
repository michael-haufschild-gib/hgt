# Positive diagonal images of dual lattices

- **ID:** hecke-diagonal-lattice-duality
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Archimedean place scaling for Hecke theta series
- **Statement:** For every integer submodule `L` of `ℝⁿ` and positive coordinate
  weights `s`, the intrinsic dual of `D_s L` is `D_(s⁻¹) L*`. For the integer span
  of an actual real basis, covolume is multiplied by `∏ s_i`.

## Dependencies and proof

Reuse `DualZLatticeCovolume` for the intrinsic dual and determinant covolume formula,
and `DeterminantOneLatticeShortVector` for the actual positive diagonal linear
equivalence and its determinant. Exact-name corpus searches located these ingredients;
the broader semantic scaling query was partial.

Coordinatewise cancellation gives `pair(D_s x, D_(s⁻¹) y) = pair(x,y)`. For a vector
in the scaled lattice's dual, apply the inverse of `D_(s⁻¹)` and test against each
original lattice vector. The same identity proves the converse. This argument works
for arbitrary integer submodules, without a fullness assumption.

For a full lattice, map its actual real basis through `D_s`. The determinant composition
formula and the existing covolume formula multiply covolume by `|det D_s| = ∏ s_i`.
The helper statement for arbitrary paired linear equivalences is discharged by the
explicit coordinatewise diagonal-pairing proof in the public specialization.

## Lean declarations and validation

In [DiagonalLatticeScaling.lean](../../../../formal/GaloisForLFunctions/HTGeometry/DiagonalLatticeScaling.lean),
namespace `GaloisForLFunctions.HTGeometry.DualZLattice`:

- `linearImage`, `mem_linearImage`, `linearImage_span`
- `dual_linearImage_of_pairing`, `covolume_linearImage_span`
- `pair_positiveDiagonal_inverse`
- `dual_positiveDiagonal`, `covolume_positiveDiagonal_span`

The complete scratch and final direct `lake --old env lean` source audit pass without
warnings. Both positive diagonal conclusions audit to only `propext`, `Classical.choice`,
and `Quot.sound`. The pairing premise of the general transport lemma is explicitly
proved for the reciprocal diagonal maps. No unproved input or limit override was added.
The module is wired into `HTGeometry.lean`; no umbrella was compiled.
Its olean is built for the written archimedean-theta consumer.

- [x] Source audit and exact proof.
- [x] Lean proof, final source audit, and transitive axiom audit.

The consumer is [archimedean ideal theta](ideal-theta-under-archimedean-place-scaling.md).
