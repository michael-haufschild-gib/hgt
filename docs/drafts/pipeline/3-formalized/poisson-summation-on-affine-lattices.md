# Poisson summation on affine lattices

- **ID:** hecke-affine-poisson
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Hecke L-functions HL7; arbitrary-dimensional Schwartz Poisson summation
- **Statement:** If `B` is an invertible real linear map on a finite-dimensional Euclidean space and `f` is Schwartz, then
  `Σ_n f(Bn+a) = |det B|⁻¹ Σ_k exp(2πi⟨a,B⁻ᵀk⟩) f̂(B⁻ᵀk)`, with absolute convergence.

## Purpose

Apply Poisson summation to ideal lattices and their residue cosets after choosing real coordinates. The dual-ideal identification, arithmetic theta coefficients, and unit integration remain separate obligations.

## Proof

Pull back the translate `f(·+a)` along `B`; it is Schwartz by the existing Schwartz composition operators. Linear change of variables in the Fourier integral gives the factor `|det B|⁻¹` and transforms frequency by the adjoint of `B⁻¹`. Translation gives the displayed exponential factor. Apply the proved integer-lattice Schwartz Poisson theorem to this pullback. Its summability theorem also proves absolute convergence on the affine lattice.

## Dependency audit

- Corpus: `HTGeometry/SchwartzPoissonSummation.lean` has checked proofs, clean axiom audits, and a passing final direct source audit.
- Mathlib `SchwartzMap.compCLMOfContinuousLinearEquiv` and `compSubConstCLM` construct the actual pullback.
- `MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar` proves the determinant factor. `integral_map_equiv` changes variables.
- `ContinuousLinearMap.adjoint_inner_right` identifies the dual frequency.
- Several broad Mathlib searches returned `partial: true` with interrupted text retrieval. Their empty results do not establish absence. Source inspection located these declarations.

## Lean declarations

In [AffineLatticePoisson.lean](../../../../formal/GaloisForLFunctions/HTGeometry/AffineLatticePoisson.lean),
namespace `GaloisForLFunctions.HTGeometry.IntegerLatticePoisson`:

- `latticeScale`, `latticeScale_pos`, `inverseAdjoint`
- `integral_comp_linearEquiv`
- `fourier_comp_linearEquiv`, `fourier_comp_add`
- `fourier_schwartz_comp_linearEquiv`, `fourier_schwartz_comp_add`
- `summable_norm_affine_lattice`, `summable_norm_dual_lattice`, `summable_norm_affine_dual`
- `schwartz_poisson_affine`

## Validation

The Fourier covariance, dual absolute-summability theorem, and affine Poisson identity pass
transitive axiom audits using only `propext`, `Classical.choice`, and `Quot.sound`.
The final direct source audit with `lake --old env lean` passes without warnings.
The module is wired into `HTGeometry.lean`. Its olean has been built for the written
Gaussian-theta consumer; no umbrella is compiled.

The Fourier change-of-variables and translation lemmas hold for arbitrary functions:
Mathlib's equivariant integral and its zero convention make these identities unconditional.
Schwartz membership supplies lattice summability and Poisson reconstruction. The raw
Fourier identities can therefore also be applied to explicit Gaussian kernels.

## Next use

[Gaussian theta inversion for full lattices](gaussian-theta-inversion-for-full-lattices.md)
provides the explicit kernel transformation, with final source and axiom audits passing. Arithmetic duality and unit integration
remain open before the Hecke functional equation.

## Dual equivalence and integrability

`inverseAdjointEquiv` now packages the dual map as an actual continuous linear equivalence;
`inverseAdjointEquiv_involutive` proves dualizing twice returns the original map.
`integrable_comp_linearEquiv` provides integrability covariance for actual functions.
These checked proofs were extracted from the Gaussian-theta construction into this module.
The extended source passes a direct audit without warnings. Its olean has been updated
for the already-written Gaussian consumer.
