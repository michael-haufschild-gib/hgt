# Gaussian Poisson sums over intrinsic dual lattices

- **ID:** hecke-intrinsic-lattice-theta
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Hecke L-functions HL7; arithmetic interpretation of full-lattice theta inversion
- **Statement:** For the actual coordinate lattice `L = B(ℤⁿ)`, the intrinsic integer dual
  is exactly `B⁻ᵀ(ℤⁿ)`. Reindex Gaussian theta inversion over the lattice subtypes and
  replace the determinant factor by `covolume(L)⁻¹`.

## Dependency audit

Corpus search finds the separate ingredients in `AffineLatticePoisson`,
`GaussianLatticeTheta`, and `DualZLatticeCovolume`, but no existing bridge between
`inverseAdjointEquiv` and the intrinsic dual-lattice subtype. Reuse all three rather
than proving Poisson summation or dual-basis covolumes again.

Mathlib `Module.Basis.restrictScalars` supplies the integer basis of the integer span
of a real basis. `restrictScalars_apply` and `restrictScalars_repr_apply` are in
`LinearAlgebra/Basis/Submodule.lean`. These can identify integer coordinate
parametrizations without an assumed lattice enumeration.

## Proof

Define the actual integer-linear parametrization `n ↦ B(n)` in real coordinates.
If `y` pairs integrally with its image, testing against each coordinate vector shows
that every coordinate of `Bᵀy` is integral. Inverting the adjoint proves
`y = B⁻ᵀm` for an integer vector `m`. Conversely, adjoint cancellation reduces the
pairing of `Bn` and `B⁻ᵀm` to the integer scalar product of `n` and `m`.

Injectivity of the two parametrizations gives equivalences with the lattice subtypes.
Transport the already proved absolutely convergent Gaussian sums through those
equivalences. Compute covolume using the mapped standard basis and the existing
determinant formula. This yields the intrinsic theta identity.

## Lean declarations and validation

In [IntrinsicLatticeTheta.lean](../../../../formal/GaloisForLFunctions/HTGeometry/IntrinsicLatticeTheta.lean),
namespace `GaloisForLFunctions.HTGeometry.IntegerLatticePoisson`:

- `integerPointLinearMap`, `latticeCoordinateEquiv`, `coordinateLatticeMap`, `coordinateLattice`
- `coordinateLatticeMap_injective`, `latticePointEquiv`
- `integerPoint_pair_inverseAdjoint`, `mem_dual_coordinateLattice`, `dual_coordinateLattice`
- `coordinateLattice_eq_span`, `det_latticeCoordinateEquiv`, `covolume_coordinateLattice`
- `latticeScale_eq_inv_covolume`, `basisLatticeEquiv`, `coordinateLattice_basisLatticeEquiv`
- `intrinsicLatticeTheta`, `coordinateLatticeTheta_eq`
- `summable_intrinsicLatticeTheta`, `summable_intrinsicLatticeTheta_basis`
- `intrinsicLatticeTheta_inversion`, `intrinsicLatticeTheta_basis_inversion`

The complete scratch and final direct `lake --old env lean` source audit pass without
warnings. The intrinsic dual, covolume, and theta inversion audit to only `propext`,
`Classical.choice`, and `Quot.sound`. The module is wired into `HTGeometry.lean`;
no umbrella was compiled. No limits or extra analytic inputs were added.
Its olean is built for the written arithmetic consumer. The completed scratch is removed.

The determinant comparison reuses Mathlib `LinearMap.det_conj` and `Basis.det_comp`,
with `Basis.det_self` simplified before broader basis reduction. Summability is
transported across equal lattice subtypes by explicit rewriting.

- [x] Corpus search and dependency audit.
- [x] Exact Lean proof and final source audit.
- [x] Transitive axiom audit.

The arithmetic consumer is now formalized:
[fractional-ideal theta inversion](fractional-ideal-theta-inversion-with-arithmetic-normalization.md).
