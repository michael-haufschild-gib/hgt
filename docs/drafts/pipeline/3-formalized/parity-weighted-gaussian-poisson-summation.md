# Parity-weighted Gaussian Poisson summation

- **ID:** hecke-parity-gaussian-poisson
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Hecke HL7; real-place parity factors in the completed L-function
- **Statement:** For a finite coordinate set `ι` and `S : Finset ι`, let
  `P_S(x) = ∏_(i∈S) x_i` and `F_(S,t)(x) = P_S(x) exp(−πt‖x‖²)`.
  For `t > 0`, prove its Fourier transform is
  `((−i)/t)^|S| t^(−dim/2) F_(S,1/t)` and prove Poisson summation with
  arbitrary full lattices, shifts, and additive phases, including absolute convergence.

## Corpus audit

- `GaussianThetaCharacteristics` gives the corresponding unweighted affine
  shifted/phased Gaussian formula and all normal-convergence machinery.
- `RHTower/GaussianMomentFourier.lean` is source-inspected. `gaussMoment_eq`
  computes every scalar Gaussian moment in the phase convention `exp(−i ξ x)`;
  `integrable_gaussMomentIntegrand` supplies its actual integrability.
  The degree-one specialization at frequency `2πξ` gives the needed odd factor.
- `HTGeometry/GaussianSchwartz.lean` is source-inspected. It constructs scalar
  `gaussianSchwartz` and `polyGaussSchwartz`, with proved polynomial bounds and
  derivatives. It does not itself construct a multivariate Schwartz function.
- A completed semantic search for finite tensor products returned pointwise
  Schwartz products and coordinate multiplication, but no matching tensor-product
  constructor in the returned results. The completed Mathlib `SchwartzMap tensor`
  search likewise returned no matching constructor; this is only a query result.
- `HTGeometry/HermiteFourierEigen.lean` is source-inspected.
  `fourier_hermiteSchwartz_apply` gives eigenvalue `(-i)^n` directly in the `2π`
  convention. Since `hermitePoly 1 = 2X`, the degree-one specialization can avoid
  converting the scalar moment Fourier convention. Positive rescaling then gives
  arbitrary `t`.
- `HTGeometry/NyquistLatticeSum.lean` is source-inspected. Its unconditional
  `fourier_comp_mul_pos` gives the scalar dilation law; `schwartzScale` supplies
  an actual scaled Schwartz representative if needed for scalar integrability.
  Both it and the scalar moment formula are available routes; use one rather than
  reproving scalar Fourier integration.
- `RHTower/ThetaCusp/ThetaCuspSchwartz.lean` is source-inspected.
  `pow_mul_exp_neg_half_pi_sq_le` bounds `r^p exp(-(π/2)r²)` on `r ≥ 0` by
  `exp(p²/(2π))`. Substituting `r = sqrt(t) ‖x‖` supplies the required polynomial
  Gaussian majorant without a multivariate Schwartz object.
- The completed corpus search for Fourier products returned circle products and
  scalar intertwining identities, but no matching Euclidean product theorem.
  Mathlib `integral_fintype_prod_eq_prod` and `Integrable.fintype_prod` in
  `MeasureTheory/Integral/Pi.lean` are source-inspected; together with
  `PiLp.volume_preserving_toLp`, they give the drafted
  [Euclidean coordinate-product transform](../3-formalized/coordinate-products-factor-under-euclidean-fourier-transform.md).

## Approach

Factor the coordinate integral into scalar even/odd Gaussian Fourier integrals.
Every selected coordinate occurs once, so no higher Hermite correction appears.
Prove actual multidimensional integrability and normal convergence, then apply
the existing raw affine Poisson theorem. Polynomial factors can be bounded by a
constant times a Gaussian with half the decay rate, reducing convergence to
already proved Gaussian bounds. A multivariate Schwartz constructor is optional,
not an assumed analytic input.

Shifts and phases are part of the target: an unshifted odd Gaussian sum alone
vanishes by sign symmetry and would not suffice for the Hecke character transform.

## Lean declarations and validation

In [ParityGaussianPoisson.lean](../../../../formal/GaloisForLFunctions/HTGeometry/ParityGaussianPoisson.lean),
namespace `GaloisForLFunctions.HTGeometry.IntegerLatticePoisson`:

- `scalarParityGaussian`, `integrable_scalarParityGaussian`, `fourier_scalarParityGaussian`
- `parityDegree`, `parityMonomial`, `parityGaussian`
- `integrable_parityGaussian`, `fourier_parityGaussian`, `parityFourierFactor_eq`
- `norm_parityMonomial_le`, `exists_parityGaussian_norm_bound`
- `parityGaussian_summable_affine_translates`, `summable_norm_parityGaussian_affine`
- `parityModulation`, `fourier_affine_parityModulation`
- `summable_norm_parityModulation_affine`, `summable_norm_dual_parity_phase`
- `parity_gaussian_poisson_with_characteristics`, `parity_gaussian_theta_characteristics`

The finite subset is represented equivalently by a Boolean coordinate profile.
The scalar proof uses existing `gaussMoment_eq` at degrees zero and one. The
square-root product is identified with `t^(-dim/2)`, giving the exact normalized
multiplier. All affine physical and dual series are absolutely summable; no
summability, Schwartz representative, or Fourier identity is assumed.

The complete scratch and final direct `lake --old env lean` source audit pass
without warnings. Five axiom audits cover the scalar and multivariate transforms,
Gaussian majorant, normalized Poisson identity, and absolute modulated lattice
summability. All contain only `propext`, `Classical.choice`, and `Quot.sound`.
The module is wired into `HTGeometry.lean`; no umbrella was compiled. Its olean is
built for the written arithmetic Hecke-theta consumer. No proof limits were raised.
The completed scratch is removed.

Arithmetic finite-character weights, unit compatibility of the weighted theta
series, primitive Gauss transforms, and unit-domain Mellin integration remain open.

- [x] Exact target and corpus audit.
- [x] Dependency-closed proof and Lean formalization.
- [x] Final source and transitive axiom audits.
