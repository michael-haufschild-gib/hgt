# Ideal theta under archimedean place scaling

- **ID:** hecke-archimedean-ideal-theta
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Hecke L-functions HL7; the theta family needed for integration over units
- **Statement:** Set `θ_I(y,t) = Σ_(a∈I) exp(-πt ‖S(scale_y ι(a))‖²)`, where
  `scale_y` multiplies the place coordinate by `exp(-y_w)`. Prove summability and
  `θ_I(y,t) = exp(Σ_w mult(w)y_w) (absNorm(I) sqrt(abs(discr K)))⁻¹
  t^(-[K:ℚ]/2) θ_(dual I)(-y,1/t)`.
  Also prove invariance under translating `y` by the place-log profile of a global unit.

## Corpus audit

- `NumberFieldMixedRealCoordinates` already defines `numberFieldMixedPlaceScale`,
  `numberFieldMixedCoordinateScale`, and their exact coordinate compatibility.
- `sum_numberFieldMixedCoordinateLogScale` identifies the sum of coordinate logarithms
  with the negative multiplicity-weighted place sum. Its exponential gives the general
  determinant; the existing `prod_numberFieldMixedCoordinateScale` is its determinant-one
  specialization on the weighted-zero hyperplane.
- `positiveDiagonalLinearEquiv_apply` and `det_positiveDiagonalLinearEquiv` are in
  `DeterminantOneLatticeShortVector`. Reuse their proved matrix behavior; do not unfold
  the inverse matrix construction.
- `NumberFieldUnitPlaceLog` proves multiplicativity and the weighted product formula.
  `NumberFieldUnitPlaceLogCovering` and `NumberFieldUnitPlaceLogFullRank` prove genuine
  covering and full rank of the weighted-zero unit-log lattice without assumed units.
- `DiagonalLatticeScaling` now supplies the required general scaling-duality bridge.
- After the corpus audit, Mathlib `LinearEquiv.submoduleMap` supplies the actual
  lattice-image equivalences and `MulAction.toPerm` supplies the unit action on
  each actual fractional ideal. `mixedEmbedding.normAtPlace` expresses the
  weighted Euclidean norm as the sum of squared place values.

## Proof plan

Transport the actual ideal lattice through the positive diagonal place scaling. Its
intrinsic dual is the inverse diagonal image of the original intrinsic dual, because
the two diagonal factors cancel in the coordinate pairing. Its covolume is multiplied
by the product of the scaling coordinates, namely `exp(-Σ_w mult(w)y_w)`.
Apply intrinsic lattice theta inversion and the already proved arithmetic dual and
covolume identifications. Conjugation commutes with real place scaling and preserves
the weighted Euclidean norm.

For a unit `u`, placewise multiplicativity gives
`exp(-y_w) |σ_w(u a)| = exp(-(y_w - log|σ_w(u)|)) |σ_w(a)|`.
Multiplication by `u` bijects each actual fractional ideal with itself. Reindexing
therefore proves the place-log periodicity. The product formula leaves the weighted
place sum unchanged under these translations.

## Lean declarations and validation

In [NumberFieldScaledIdealTheta.lean](../../../../formal/GaloisForLFunctions/HTGeometry/NumberFieldScaledIdealTheta.lean),
namespace `GaloisForLFunctions.HTGeometry`:

- `numberFieldScaledTraceLattice`, `numberFieldScaledIdealLatticeEquiv`,
  `numberFieldScaledDualIdealLatticeEquiv`
- `dual_numberFieldScaledTraceLattice`, `covolume_numberFieldScaledTraceLattice`
- `numberFieldScaledIdealTheta`, `summable_numberFieldScaledIdealTheta`,
  `numberFieldScaledIdealTheta_inversion`
- `norm_sq_numberFieldTraceCoordinates`, `normAtPlace_numberFieldMixedPlaceScale`
- `numberFieldIdealUnitEquiv`, `norm_sq_numberFieldPlaceScale_unit`,
  `numberFieldScaledIdealTheta_unit`, `sum_mult_placeProfile_add_unitLog`

The complete scratch and final direct `lake --old env lean` source audit pass
without warnings. Summability, inversion, and unit periodicity audit to only
`propext`, `Classical.choice`, and `Quot.sound`. The updated diagonal helper's two
main theorems were also re-audited with those same standard axioms. No mathematical
input is assumed, and no proof limits were raised. The module is wired into
`HTGeometry.lean`; no umbrella was compiled. Its olean is built for the
written uniform-tail consumer.

Finite-character transforms, parity-weighted Gaussians, unit-domain integration,
and the full Hecke Mellin identity remain subsequent obligations. The next
analytic result is [uniform exponential tails](ideal-theta-tails-decay-uniformly-on-bounded-place-profiles.md).

- [x] Exact statement and corpus audit.
- [x] Lean proof and final direct source audit.
- [x] Transitive axiom audit.
