# All-scale Gaussian moment bound

- **Obstacle:** B13.
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

## Statement

Let `S₁` be the actual first-moment Vaughan sum on
`[D,2D)×[M,2M)`, retaining the product cutoff `[A,B)`. Put
`Wσ=DM D^(−σ)M^(−σ)`. For positive integer endpoints,
`σ≥0`, `ξ>0`, `t≥1`, `ξ/(2t)≤α≤ξ`, and Vaughan cutoffs

`πU≥128t log t`, `V≥2t`,

there is an absolute constant, uniform in all parameters, such that

`|S₁|²≤C Wσ² (1+log(2D))(1+log(2M))⁴ exp(−αD²M²)/t`.

Every product scale is covered. No separate resonance-band or
factor-length assumption remains. Boundary-angle damping satisfies
`ξ/(2t)≤α` eventually, uniformly in every positive radius; together
with the existing upper-sector theorem, this covers every geometric
sample of the recovered moment filter.

## Proof

Write `X=DM`, `r=ξX²/t`, `y=αX²`, `L=1+log(2M)`. Then `y≥r/2`.
The exponential's linear and quadratic lower bounds give

`r exp(−y)≤2`, `r² exp(−y)≤8`,
`r² exp(−y)≤32 exp(−r/4)`.

Coefficient support annihilates rectangles with `2D≤U` or `2M≤V`.
Otherwise `U<2D`, `V<2M`, and hence `M≥t`.

If `r≤4 log t`, then `16ξD²M²≤64t log t≤πU/2<πD`.
The first-band condition follows. The existing nonstationary energy
estimate has squared scalar cost

`exp(−2y)[r²/M+2πLr/t]`.

The first two absorption bounds make this at most
`(8+4πL)exp(−y)/t`.

If `r>4 log t`, use two applications of Cauchy–Schwarz and
`|Gaussian(dm)|≤exp(−αD²M²)`. The actual shifted coefficient energies,
bounded by Chebyshev and the divisor second moment, give the absolute
squared cost `r² exp(−2y)`. The third absorption bound makes this at most
`32 exp(−y)/t`, because `exp(−r/4)≤1/t`.

Both cases retain `log(2D)(1+H_{2M}³)`, where
`H_N=Σ_{1≤n≤N}1/n`. Using `H_{2M}≤1+log(2M)` proves the stated bound.
No zero-location estimate enters.

For the boundary angle, `α=z sin(1/t)` and `ξ=z cos(1/t)`.
Since `sinc(1/t)→1`, eventually `sin(1/t)≥1/(2t)`;
`cos(1/t)≤1` proves the lower-sector bound for every `z>0`.

## Actual finite convolution

For `B≤2^K`, the literal shifted convolution moment

`T₁=((α−iξ)/t) Σ_{A≤n<B}(typeIILong U * typeIIShort V)(n)`
`                       × GaussianWeight(σ−2,α,ξ,t,n)`

is exactly `Σ_{j,k<K} S₁(2^j,2^k)`. Dirichlet-convolution
rearrangement keeps the product cutoff, and two exact dyadic partitions
cover both factors. By the rectangle moment identity this is the original
convolution weighted by `(α−iξ)n²/t`.

Writing `Eσ,α(D,M)` for the displayed rectangle envelope without `C/t`,
the triangle inequality gives

`|T₁|≤sqrt(C/t) Σ_{j,k<K} sqrt(Eσ,α(2^j,2^k))`.

This is an independent finite type-II arithmetic bound with Gaussian
decay retained at every product scale.

## Scope

The first moment already preserves the full normalized divisor reading.
This result covers all rectangles and finite type-II assembly. The
subsequent [uniform type-II bound](b13-uniform-gaussian-moment-typeII-bound.md)
closes type-II truncation and infinite tails. Type-I moment terms and
arithmetic control retaining pole/filter cancellation remain. No bound
below the selected divisor signal or B13 conclusion is claimed.

## Lean declarations

In `GaloisForLFunctions.ExceptionalLayerTheory`:

- `exists_gaussianVaughan_shifted_dyadic_coefficient_energy`
  (`GaussianMomentDyadicSaving.lean`)
- `norm_maskedGaussian_dyadic_trivial_sq_le`
- `exists_gaussianVaughan_moment_trivial_envelope_bound`
- `exists_gaussianVaughan_moment_all_scale_harmonic_bound`
- `exists_gaussianVaughan_moment_all_scale_bound`
- `eventually_boundaryDamping_lower_sector`
- `gaussianVaughanMomentBlock_eq_sum_dyadic`
- `exists_gaussianVaughan_moment_typeII_block_bound`

The last seven declarations are in `GaussianMomentAllScales.lean`.

## Audit

Both modules pass final direct source checks with
`lake --old env lean`, without warnings. All twelve printed transitive
axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`.
The new module is imported by `ExceptionalLayerTheory.lean`; no umbrella
build was run.
