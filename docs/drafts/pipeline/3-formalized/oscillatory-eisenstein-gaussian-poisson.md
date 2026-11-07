# Poisson transform of the oscillatory Eisenstein Gaussian

- **ID:** oscillatory-eisenstein-gaussian-poisson
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The damped quadratic trace form has an exact, absolutely convergent binary Gaussian Poisson transform.

For real `a,b,η`, put `q=a²−ab+b²>0`, `η>0`, and

`A=η+2ib/q`, `B=−η/2−2ia/q`, `D=η+2i(a−b)/q`.

The matrix `M=[[A,B],[B,D]]` has positive definite real part and positive
real determinant `R=4/q+3η²/4`. Then

`Σ_{z∈ℤ²} exp(−π zᵀMz) = R^(−1/2) Σ_{z∈ℤ²} exp(−π zᵀM⁻¹z)`.

Writing `r=1+3qη²/16`, the inverse form is

`ηq(k²+kℓ+ℓ²)/(4r) + i((a−b)k²+2akℓ+bℓ²)/(2r)`.

## Proof

Apply one-dimensional complex Gaussian Poisson summation first in one
coordinate, then the other. Positive definite real parts dominate products
of real Gaussian series. For the intermediate form, the real determinant
is `(Re(A)Re(D)−Re(B)²)/|A|²`, which is positive. This proves every required
summability statement. Since `Re(A)>0` and `R>0`, the principal logarithm
identity gives `sqrt(A)sqrt(R/A)=sqrt(R)`. Direct algebra gives the displayed
determinant and inverse form.

## Lean and scope

Module: `MetaplecticMobiusDescent/BinaryGaussianPoisson.lean`.

- `OscSpecial.binary_gaussian_poisson_real_det`
- `OscSpecial.oscillatory_gaussian_poisson`
- `OscSpecial.dualGaussian_explicit`

Direct `lake --old env lean` passed. Three endpoint axiom audits contain only
`propext`, `Classical.choice`, `Quot.sound`. Adapted from the external OpenAI
development; attribution and Apache-2.0 license accompany the module.

The Abel limits below turn this transform into the checked
[quadratic Gauss evaluation](quadratic-trace-gauss-phase.md). No global
cancellation estimate is asserted here.

## Shifted Gaussian Abel mass

For every real `x,y` and `q>0`,

`η Σ_{m,n∈ℤ} exp(−πηq((m+x)²−(m+x)(n+y)+(n+y)²)) → 2/(√3 q)`

as `η→0+`. The affine Poisson formula leaves a dual Gaussian series whose
zero-frequency term is one. Every other term tends to zero and a fixed
Gaussian dominates the series. The square-root prefactor is exactly
`2/(√3 ηq)`.

`MetaplecticMobiusDescent/ShiftedEisensteinGaussianMass.lean` proves
`RankTwoEisShift.shifted_eisenstein_gaussian_poisson`,
`RankTwoLimit.dual_sum_tendsto_one`, and
`EisensteinAbelFiber.{shifted_gaussian_mass,scaled_shifted_gaussian_mass}`.
The direct check and four endpoint axiom audits passed with only standard axioms.
The varying quadratic phase is controlled by the estimate below.

## Residue-class Gaussian mass

For every nonzero Eisenstein integer `c` and every residue class `r mod c`,
`η Σ_{z≡r mod c} exp(−πη‖z‖²) → 2/(√3‖c‖²)`.
Write the fibre as `r₀+cO`; multiplication by `c` rescales the norm form by
`‖c‖²`, leaving a real shift. Apply the shifted mass theorem.

Consequently the damped quadratic trace sum has Abel limit
`2G(c)/(√3‖c‖²)`, where `G(c)=Σ_{r mod c} ψ_c(r²)`. Absolute summability
allows the finite fibre partition; the additive character has modulus one.

`EisensteinResidueGaussianMass.lean` proves `actual_fiber_gaussian_mass`,
`actual_oscillatory_kernel_summable`, and `original_abel_gauss_limit`.
The direct check and three endpoint axiom audits passed with standard axioms.

## Freezing the dual phase

With `Q=k²+kℓ+ℓ²`, `T=(a−b)k²+2akℓ+bℓ²`, and `r=1+3qη²/16`, put

`Vη=Σ exp(−πηqQ/(4r)) exp(−πiT/(2r))`,
`Wη=Σ exp(−πηqQ/(4r)) exp(−πiT/2)`.

For `q>0`, `η‖Vη−Wη‖→0`. The exponential difference is bounded by
`Cη²Q`; for small positive `η`, the amplitude is bounded by
`exp(−πηqQ/8)`. The Gaussian moment inequality and shifted mass give
`η³ΣQ exp(−KηQ)→0` for every `K>0`.

`TheDualGaussianPhaseFreezes.lean` proves this estimate without a moment or
summability premise. It also proves the dual scale mass multiplier `4/q`
and the prefactor limit `√q/2`. Four endpoint axiom audits and the direct
check passed with only standard axioms.
