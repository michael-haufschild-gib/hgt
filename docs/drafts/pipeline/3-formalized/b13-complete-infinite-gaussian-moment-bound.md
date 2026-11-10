# Complete infinite Gaussian prime-moment bound

- **Obstacle:** B13.
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

## Statement

Put `ε=α−iξ` and

`M₁=Σ_{n≥1} Λ(n)(εn²/t)n^(−σ−it) exp(−εn²)`.

There is an absolute `C>0` such that, whenever

- `0≤σ<1`, `ξ>0`, `t≥2`, `ξ/(2t)≤α≤ξ`;
- `αX²=2`, `πU≥128t log t`, `V≥2t`, `tUV≤X`,

this actual prime series converges absolutely and satisfies

`|M₁| ≤ C [1/(2^(1−σ)−1)+12] X^(1−σ)`
`        × [2+log X/log 2]^6 / sqrt(t)`.

No zero-location premise enters. The estimate includes both actual type-I
convolutions, the finite Vaughan head and the complete type-II term.
`rotatedGaussianMomentPrimeSum` is exactly this arithmetic series with
`α=Re ε`, `ξ=−Im ε`, `ε=complexGaussianDamping y φ`; its bound is
formalized directly in the existing observable's notation.

## Type-I proof

On `[P,2P)`, the curvature `κ(x)=ξ/π+t/(2πx²)` has
`κ(P)/κ(2P)≤4`. Its second-derivative bound is at most

`100[P sqrt(ξ)+sqrt(t)+P/sqrt(t)]`.

Abel summation first retains `P^(−σ)exp(−αP²)`, then inserts `n²`
at cost `8P²`. Since `|ε/t|≤4α`, the moment prefix is bounded by
`3200P^(−σ)αP²exp(−αP²)` times the bracket above. The inequalities

`u exp(−u/2)≤2`, `z exp(−z²/2)≤1`, `sqrt(ξ)≤2sqrt(αt)`

absorb the moment into half the Gaussian, giving

`16000[sqrt(αt)+1/sqrt(t)]P^(1−σ)exp(−αP²/2)`.

A logarithmic coefficient costs `2log(2P)`. The dyadic Gaussian
fourth-power sum bounds every initial segment independently of its
endpoint. Subtracting two initial segments handles arbitrary positive
intervals.

Dilation is exact:

`G₁(ab)=b^(−σ)exp(−it log b)G₁(a; αb²,ξb²)`.

For `1≤b≤X`, the inner scale is `X/b`. Both plain and logarithmic
fibres therefore have the bound

`C₀ Qσ X^(1−σ)L^4 [sqrt(αt)+1/(b sqrt(t))]`,

where `Qσ=1/(2^(1−σ)−1)+12`, `L=2+log X/log 2`, and
`C₀=64000` or `128000`, respectively.

## Arithmetic assembly

The exact coefficients satisfy

`|Λ_U*μ_V(b)|≤log b`, supported on `b≤UV`;
`|μ_V(b)|≤1`, supported on `b≤V`.

Writing `H_K=Σ_{b≤K}1/b`, the two type-I terms are at most

`64000 Qσ X^(1−σ)L^4 log(UV)[UV sqrt(αt)+H_{UV}/sqrt(t)]`,
`128000 Qσ X^(1−σ)L^4 [V sqrt(αt)+H_V/sqrt(t)]`.

For either cutoff `K`, `tK≤X` and `αX²=2` give
`K sqrt(αt)≤2/sqrt(t)`. Also `H_K≤1+log K≤L`, so each bracket
is at most `2L/sqrt(t)`. The two contributions are bounded by
`128000 Qσ X^(1−σ)L^6/sqrt(t)` and
`256000 Qσ X^(1−σ)L^6/sqrt(t)`.

The head is at most `4αU²U^(1−σ)log U`. Since `tU≤X`, it is at
most `8X^(1−σ)L/sqrt(t)`. The existing type-II theorem contributes
at most `16sqrt(CII/t)Qσ X^(1−σ)L^4`. Vaughan's exact identity
therefore gives the claimed bound, with `C=400000+16sqrt(CII)`.

For `n≥1`, the absolute prime summand is bounded by
`|ε/t| n³ exp(−αn²)`. Polynomial-Gaussian summability and the bound
uniform in the upper endpoint justify the infinite limit.

## Scope

This closes the complete raw first-moment arithmetic estimate at the
pole-scale exponent, improving the earlier type-II-only result.
It does not preserve pole/filter cancellation or bound the filtered
current below its selected exceptional-divisor signal. B13 remains open.

## Lean declarations

Namespace `GaloisForLFunctions.ExceptionalLayerTheory`.

`GaussianMomentTypeI.lean`:

- `gaussianTypeIBound_dyadic_le`
- `gaussian_moment_curvature_absorption`
- `norm_gaussianPrimeMomentWeight_le`
- `gaussianPrimeMomentWeight_eq_shift`
- `norm_sum_gaussianPrimeMomentWeight_prefix_le`
- `norm_sum_log_gaussianPrimeMomentWeight_prefix_le`
- `norm_sum_gaussianPrimeMomentWeight_initial_le`
- `norm_sum_log_gaussianPrimeMomentWeight_initial_le`
- `gaussianPrimeMomentWeight_dilate`
- `norm_sum_gaussianPrimeMomentWeight_dilate_le`
- `norm_sum_log_gaussianPrimeMomentWeight_dilate_le`

`GaussianMomentPrimeBound.lean`:

- `norm_sum_gaussianMoment_zeta_trunc_conv_le`
- `norm_sum_gaussianMoment_log_trunc_moebius_le`
- `norm_sum_gaussianPrimeMoment_vonMangoldt_head_le`
- `summable_gaussianPrimeMoment_vonMangoldt`
- `exists_gaussianPrimeMoment_vonMangoldt_bound`
- `rotatedGaussianMomentPrimeSum_eq_arithmetic`
- `exists_rotatedGaussianMomentPrimeSum_arithmetic_bound`

Both new modules pass direct source checks with `lake --old env lean`,
without warnings. All eighteen printed transitive axiom lists contain
only `propext`, `Classical.choice`, and `Quot.sound`. Both modules are
imported by `ExceptionalLayerTheory.lean`; no umbrella build was run.
