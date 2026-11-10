# Gaussian moments suppress small products

- **Obstacle:** B13.
- **Stage:** 3-formalized
- **Type:** THEOREM

## Observable and divisor signal

For each damping sample `ε_j`, multiply the literal Gaussian prime
summand by `ε_j n²/t`. The resulting filtered observable is exactly
`(ε_0/t) A_{σ−2}`, where `A_{σ−2}` uses the original polynomial filter
at shifted observation abscissa. The geometric sample weights supply
the factor `ε_j/ε_0`; no differentiation of an infinite sum is needed.

Gamma recurrence gives `ε Kε(w+2)=(w/2)Kε(w)` for `w≠0`.
Thus the modified complete prime filter, divided by the original
`h^d Kε(ρ−σ−it)`, tends to `(-i/2)` times the original divisor amplitude
at all sufficiently large polynomial damping exponents, for every
positive contracting grid. The threshold may increase.

The contour estimate only requires the observation abscissa below a cut
between the remainder and selected zero. It therefore proves recovery
at `σ−2` as well. A cut can be chosen above `max(1/2,σ−2,θ_remainder)`
and below `Re ρ`. The Gamma multiplier tends to `−i/2`, preserving a
nonzero reading. An unconditional AAL-or-moment-readings statement uses
the corpus's actual exceptional-layer profile.

## Independent arithmetic estimate

Let `S₁` be the actual first-moment Vaughan rectangle, with product
cutoff retained. Put `θ=ξD²M²`, `Wσ=DM D^(−σ)M^(−σ)`, and
`H_N=Σ_{1≤n≤N}1/n`. For `σ≥0`, `0≤α≤ξ`, `ξ,t>0`, positive endpoints,
and `16ξDM²≤π`, the bound is

`|S₁|²≤C Wσ² log(2D)(1+H_{2M}³) exp(−2αD²M²)`
`  × (θ/t)² [1/M+2π(1+log(2M))/θ]`.

The constant is uniform in all parameters and Vaughan cutoffs. On each
factor, `d^(2−σ)≤4D²D^(−σ)`; multiplying the two squared-energy costs
gives `256D⁴M⁴`. Also `|α−iξ|≤2ξ`. Chebyshev, the divisor second
moment and the nonstationary Schur bound give the displayed estimate.

If additionally `θ≤t≤M`, then

`|S₁|²≤C Wσ² (1+log(2D))(1+log(2M))⁴ exp(−2αD²M²) θ/t²`.

Indeed `(θ/t)²(1/M+K/θ)=θ/t²(θ/M+K)≤θ/t²(1+K)`.
The inverse-θ singularity disappears: small products gain an additional
`θ/t` in squared norm compared with the stationary-scale bound.

At the boundary angle, `α=y sin(1/t)` and `ξ=y cos(1/t)`. Uniformly in
every positive radius, eventually `0<α≤ξ`; hence the sector restriction
includes every geometric sample of the recovered moment filter.

Choose Vaughan cutoffs with `32t≤πU` and `2t≤V`. If `2D≤U` or
`2M≤V`, the rectangle vanishes by coefficient support. Otherwise
`U<2D` and `V<2M`, giving `16t≤πD` and `t≤M`. For every `θ≤t`,
`16ξDM²=16θ/D≤π`. Consequently the last bound covers **every**
small-product rectangle, without separate first-band or factor-length
assumptions.

## Scope

This changes the observable while preserving its normalized divisor
signal. Height-sized cutoffs cover all small-product rectangles; rectangles
above the stationary scale need further control. Global dyadic
summation, type-I moment terms, infinite tails and an arithmetic estimate
retaining all pole/filter cancellations are still required. No bound
below the selected divisor signal or B13 conclusion is claimed.

## Lean declarations and audit

All declarations are in `GaloisForLFunctions.ExceptionalLayerTheory`.

`GaussianMomentsReadTheDivisor.lean`:

- `complexDamping_mul_rotatedGaussianKernel_add_two`
- `rotatedGaussianMomentPrimeSum_eq`
- `rotatedPrimeMomentFilter_eq`
- `tendsto_gaussian_moment_multiplier`
- `exists_polynomial_divisor_reading_below_cutline`
- `exists_polynomial_gaussian_moment_divisor_threshold`
- `asymptoticAbscissaLaw_or_polynomial_moment_divisor_readings`
- `eventually_boundaryDamping_moment_sector`

`GaussianMomentDyadicSaving.lean`:

- `gaussianVaughanMomentDyadicSum_eq`
- `exists_gaussianVaughan_moment_dyadic_envelope_bound`
- `exists_gaussianVaughan_moment_small_scale_saving`
- `exists_gaussianVaughan_moment_all_small_rectangles_bound`

Both modules pass final direct `lake --old env lean` source audits without
warnings and are imported by `ExceptionalLayerTheory.lean`. All twelve
transitive axiom lists contain only `propext`, `Classical.choice`, and
`Quot.sound`.
