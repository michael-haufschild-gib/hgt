# The logarithmic causal kernel has its Fourier multiplier

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The actual positive causal density has `v̂(ξ)=κ(2πiξ)⁻¹` for every real frequency. The continued factor satisfies `|κ(iy)|²=1+(1/2)log(1+y²)` also at `y=0`.

## Proof

The literal complex Laplace integral is holomorphic on `Re z>0`.
The integrable causal density itself dominates the integrand throughout each
local disk in that half-plane. Cauchy's integral formula proves differentiation
under the integral without a moment assumption.

On positive real parameters, the integral is the already proved reciprocal
factor. Analytic uniqueness extends this identity to the right half-plane.
Dominated convergence reaches every imaginary boundary point. The continued
factor is analytic and nonzero there, including at zero, so its reciprocal
has the same limit. Rewriting the exponential gives the exact Fourier formula.
The established imaginary modulus identity, together with `κ(0)=1`, gives the
logarithmic symbol at all frequencies.

## Lean

Module `CanonicalSystemOfTheWindowTower/TheLogarithmicCausalKernelHasItsFourierMultiplier.lean`.
Namespace `GaloisForLFunctions.CanonicalSystemOfTheWindowTower`.

- `measurable_logarithmicCausalKernel`
- `differentiableOn_logarithmicCausalLaplace`
- `logarithmicCausalLaplace_eq_factor_inv`
- `logarithmicCausalLaplace_imaginary`
- `fourier_logarithmicCausalKernel`
- `continuedLogReferenceFactor_imaginary_norm_sq`

Production plain audit passed. Transitive axioms are exactly
`[propext, Classical.choice, Quot.sound]`; the umbrella imports the module.
The [half-line form and Green identity](../1-in-progress/the-half-line-logarithmic-green-kernel.md)
remain to be identified.
