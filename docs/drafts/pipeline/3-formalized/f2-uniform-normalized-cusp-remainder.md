# F2 — uniform exact cusp remainder

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The charge-normalized actual PM cores have a linear lower-cusp remainder, uniformly polynomial-exponential in spectral height.

## Theorem

For every upper Mayer resonance `s`, let `b_s=2ζ(2s−1)/(2s−1)` and `κ_s=−core_s/b_s`. One constant `C≥0` satisfies, for every `a>0`,

`|κ_s(a)−a^(1−2s)|≤C(1+Im s)^4 exp(π Im s) a`.

The actual completed Eisenstein cusp tail also satisfies

`|tail_u(x,Y)|≤tailConst(0) exp(−2πY)`

for `|Re u|≤1/2`, real `x`, and `Y≥1/2`. Neither estimate assumes a uniform resonance gap.

## Proof

The Schläfli integral and `|cosh z|≤cosh(Re z)` compare the complex Bessel order with its real part. The existing term majorant at order zero then bounds the entire vertical order strip, independently of imaginary height.

Write `w=2s`, `σ=Re w`, `A=averagingFactor(w)`, `B=scatteringCoefficient(w)`, and `Λ=ΓRζ`. Gamma recurrence and the completed functional equation give

`1/(ΓR(w)A b_s)=w/Λ(2−w)`, `B/(A b_s)=w`.

For `r=(fieldCore_w+B/a)/(A b_s)`, the small-axis bound is `K/a`; the uniform tail gives `D a^(−Re s−2)` above one. Hence `M=∫_0^∞a^σ|r(a)|da≤K/σ+2D`. Commuting the literal multiplicative convolution and using `|cauchyWeight_w(t)|≤t^(−σ−2)` gives normalized outgoing error at most `M a^(−1−σ)`. Modular inversion gives the exact lower error `M a`.

The inverse Gamma estimate on `1≤Re(2−w)≤2`, the Euler-region inverse-zeta bound, and the reciprocal strip-gap bounds give `M≤C(1+Im s)^4 exp(π Im s)`. This supplies the summable error needed for Gaussian physical cusp packets; it supplies no sign after energy counterterms are subtracted.

## Lean

Module: `GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.UniformNormalizedCuspRemainder`.

- `mayerCuspTail_uniform_bound`
- `mayerCuspNormalizedCore_uniform_remainder_bound`

Individual `lake --old env lean` audit passed. Both declarations have exactly `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. Imported by the RIT umbrella.
