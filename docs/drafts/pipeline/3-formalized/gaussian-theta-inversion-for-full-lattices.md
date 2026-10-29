# Gaussian theta inversion for full lattices

- **ID:** hecke-gaussian-lattice-theta
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Hecke L-functions HL7; affine Poisson summation
- **Statement:** For every invertible real linear map `B` on a finite-dimensional Euclidean
  space and `t>0`, the absolutely convergent sum
  `Θ_B(t) = Σ_n exp(−πt‖Bn‖²)` satisfies
  `Θ_B(t) = |det B|⁻¹ t^(−d/2) Θ_(B⁻ᵀ)(1/t)`.

## Scope

This is the Gaussian inversion theorem for arbitrary full lattices, including dimension zero.
The arithmetic dual ideal, finite residue characters, real parities, and unit-domain Mellin
integration remain separate obligations before a Hecke functional equation.

## Proof

Set `M = max(1,‖B⁻¹‖)`. For a coordinate shift `‖x‖∞≤R` and
`y=B(x+n)`, each coordinate satisfies `|n_i|≤M‖y‖+R`, hence
`n_i²≤2M²(‖y‖²+R²)`. If `a>0` and `c=a/[2(d+1)M²]`, summing these inequalities gives
`exp(−a‖y‖²)≤exp(aR²) ∏_i exp(−c n_i²)`. The product is summable by the corpus scalar
Gaussian theorem and finite-product summability. Thus every bounded family of lattice
translates has one summable majorant. Taking zero shift proves absolute lattice convergence.
The factor `d+1` makes this proof valid in dimension zero as well.

The Gaussian is continuous and integrable. Haar change of variables proves integrability of
its pullback by `B`. The Gaussian Fourier transform is
`(π/a)^(d/2) exp(−(π²/a)‖ξ‖²)`; linear covariance replaces `ξ` by `B⁻ᵀξ` and multiplies
by `|det B|⁻¹`. The inverse-adjoint map is an actual continuous linear equivalence, and
applying it twice returns `B`. The same convergence theorem therefore proves summability
of the dual Fourier samples. Apply actual-function Euclidean Poisson summation and extract
the scalar factors. Casting the real sums into `ℂ` gives the real identity. Finally set
`a=πt`, simplify the dual rate to `π/t`, and use `(1/t)^(d/2)=t^(−d/2)`.

## Lean declarations

In [GaussianLatticeTheta.lean](../../../../formal/GaloisForLFunctions/HTGeometry/GaussianLatticeTheta.lean),
namespace `GaloisForLFunctions.HTGeometry.IntegerLatticePoisson`:

- `gaussianKernel`, `gaussian_summable_translates`, `summable_norm_gaussian_lattice`
- `continuous_gaussianKernel`, `integrable_gaussianKernel`, `fourier_gaussianKernel`
- `gaussian_lattice_poisson`, `gaussianLatticeSum_poisson`
- `latticeTheta`, `latticeTheta_inversion`

Reusable interfaces were added to existing modules:

- `SchwartzPoissonSummation.lean`: `integer_character_eq_fourier_phase`,
  `integer_fourier_coefficient`, `euclidean_poisson_of_summable_translates`.
- `AffineLatticePoisson.lean`: `inverseAdjointEquiv`, `inverseAdjointEquiv_involutive`,
  `integrable_comp_linearEquiv`.

## Dependency audit

The scalar majorant reuses `summable_one_add_natAbs_pow_mul_exp_neg_int_sq` from
`HTGeometry/FinitePiProductSummability.lean`. Finite products use
`HTGeometry.CombinationModeDiophantineDivisor.summable_prod_pi`, reindexed through
`Fin (Fintype.card ι)`. The general product proof with raised limits is not a dependency
of these theta declarations. No limit overrides were added.

Mathlib supplies `fourier_gaussian_innerProductSpace`,
`GaussianFourier.integrable_cexp_neg_mul_sq_norm_add`, Haar linear change of variables,
and real/complex power compatibility. No multidimensional Gaussian Schwartz object is
assumed or required.

## Validation

All three extended/new source files pass final direct `lake --old env lean` audits without
warnings. Their required oleans are built for the written consumers. Four final transitive
axiom checks—dual involution, normal convergence, complex Poisson identity, and normalized
real theta inversion—report only `propext`, `Classical.choice`, and `Quot.sound`.
The Gaussian module is wired into `HTGeometry.lean`; no umbrella was compiled.

## Next targets

- [Lattice shifts and additive phases](../1-in-progress/gaussian-theta-with-lattice-shifts-and-phases.md).
- [Weighted number-field trace pairing](../1-in-progress/number-field-trace-pairing-in-weighted-real-coordinates.md).

The corpus also supplies scalar polynomial-Gaussian Fourier transforms in
`RHTower/GaussianMomentFourier.lean` and scalar polynomial-Gaussian Schwartz functions in
`HTGeometry/GaussianSchwartz.lean`. Finite-coordinate parity factors remain to be constructed.
