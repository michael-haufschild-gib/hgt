# Coordinate products factor under the Euclidean Fourier transform

- **ID:** hecke-coordinate-fourier-product
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Parity-weighted Gaussian transform for Hecke HL7
- **Statement:** For every finite real Euclidean coordinate set and arbitrary
  scalar functions `f_i : ℝ → ℂ`, the Fourier transform of `∏_i f_i(x_i)` is
  `∏_i Fourier(f_i)(ξ_i)`. If all scalar functions are integrable, their coordinate
  product is integrable.

## Source audit and proof

The completed corpus search returned scalar intertwining and circle-product
identities, but no matching Euclidean product theorem in its results. Mathlib
`MeasureTheory.integral_fintype_prod_eq_prod` and `Integrable.fintype_prod` in
`MeasureTheory/Integral/Pi.lean` are inspected. The integral factorization itself
is unconditional under the Bochner integral's zero convention.

Reuse `PiLp.volume_preserving_toLp`, already used in `SchwartzPoissonSummation`,
to transfer Euclidean volume to coordinate product volume. Euclidean inner
product is the sum of scalar inner products, so its Fourier phase factors.
Apply finite-product Fubini to these phased scalar functions.

## Lean declarations and validation

In [CoordinateProductFourier.lean](../../../../formal/GaloisForLFunctions/HTGeometry/CoordinateProductFourier.lean),
namespace `GaloisForLFunctions.HTGeometry.IntegerLatticePoisson`:

- `coordinateProduct`
- `euclidean_fourier_phase_eq_prod`
- `integrable_coordinateProduct`
- `fourier_coordinateProduct`

The complete scratch and final direct `lake --old env lean` source audit pass
without warnings. Both integrability and Fourier factorization audit to only
`propext`, `Classical.choice`, and `Quot.sound`. No unproved tensor-product or
smoothness interface is assumed. The module is wired into `HTGeometry.lean`;
no umbrella was compiled. Its olean is built for the written parity
Gaussian consumer. The completed scratch is removed after the final audit.

- [x] Exact target and corpus/Mathlib source audit.
- [x] Lean proof and direct source audit.
- [x] Transitive axiom audit.
