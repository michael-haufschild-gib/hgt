# Shifted harmonic limits for the linear detector

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** A111, `levinson-gate-from-below-square-root-twists.md`.

## Target

For `L=log N` and a smooth profile `P` with `P(0)=0`, prove

`L Σ_{h,k≤N} μ(h)μ(k)(hk)^(v/L) gcd(h,k)^(1+c/L)/(hk)`
`·P(log(N/h)/L)P(log(N/k)/L)`
`→ ∫₀¹ exp((c+2v)t)[P′(1−t)−vP(1−t)]² dt`.

The detector requires the first two displacement derivatives with its
coefficient weights held fixed, for polynomial profiles of degree at most two.

## Proved arithmetic reduction

`3-formalized/shifted-selberg-euler-factorization.md` proves the exact
parameterized Euler convolution, arbitrary-weight harmonic collapse,
common summable correction majorant, and limiting unit mass.
The extra coefficient twist costs at most `exp(2|v|)` on the finite cutoff.

## Uniform Möbius replacement

For a fixed `C²` test `f` with `f(0)=0`, twice integration gives the error
`f′(0)(F(Lu)−1)+∫₀ᵘ f″(u−x)(F(Lx)−1) dx`, where `F` is the bounded
first logarithmic Möbius kernel. Dominated convergence implies
`∫₀¹|F(Lx)−1| dx→0`; convergence is therefore uniform for `δ≤u≤1`.
`TheMobiusKernelConvergesInMean` formalizes this proof; direct Lean check passed.

## Remaining detector values and derivatives

At the actual detector evaluation point `c+2v=0`. Its first two
frozen-coefficient displacement derivatives contribute only polynomial
powers of the harmonic logarithm. Existing harmonic logarithmic moments
therefore suffice; an exponential harmonic limit is unnecessary.

For fixed `v`, derivatives of the shifted Möbius transform reduce to finite
linear combinations of the same smooth tests `x^j exp(−vx)`. The limiting
transform is `P′(u)−vP(u)`; its first `v` derivative is `−P(u)` and its second
is zero. Uniform convergence away from `u=0` follows from the mean-kernel
estimate. The endpoint strip must be bounded in harmonic mass.

Prove the first two normalized correction derivatives have the same
summable fibre envelope and tend to zero on each fixed fibre. Combine
these facts with the existing harmonic moments, retaining frozen detector
coefficients throughout the displacement differentiation.

A complex continuation gives a common majorant for the correction jets.
For `n>0`, extend the amplitude by
`n⁻¹∏_{p|n}(1−p exp(z log p))`.
The bound `|exp(w)−1|≤exp(|w|)−1` gives
`|1−p exp(z log p)|≤(p−1)exp(2|z|log p)`.
Thus the normalized correction on `|z−C|≤1` is bounded by
`exp(4(|C|+1))|W_0|`. Cauchy's estimate bounds its `j`-th derivative by
`j! exp(4(|C|+1))|W_0|`. On each fixed fibre the normalized continuation
converges locally uniformly to a constant, so every positive-order jet
converges to zero. This avoids separate primewise Leibniz estimates.

`TheShiftedAmplitudeIsHolomorphic` formalizes the entire continuation,
real-axis identity, and complex majorant. Direct Lean check passed.
`TheCorrectionJetsKeepTheSummableEnvelope` contains the Cauchy estimates
and vanishing positive-order fibre sums; direct Lean check passed.
`TheShiftedMobiusProfilesConvergeUniformly` contains the full-cutoff bound
and uniform `P′−vP` profile limit on compact shift intervals; direct check pending.

The actual shift `R log N/log T` varies with height. Profile limits must be
uniform on compact shift intervals; the current profile draft has this
scope. For correction jets, the Cauchy continuity argument also works
uniformly for bounded centres, since the source argument is bounded by
`(R+1)/log N`. This moving-centre version remains to be extracted.

At the detector base point, write `A=P′−vP`. After division by the
appropriate power of `log N`, the direct arithmetic jets have integrands
`A²`, `2tA²−4PA`, and `4t²A²−16tPA+8P²`.
The reflected jets have integrands `A²`, `2tA²`, and `4t²A²` with the
reflected value of `v`. Here the profiles are evaluated at `1−t`.
Correction jets and derivatives of fixed outer dilation factors vanish
in the fixed-fibre limit. Existing polynomial harmonic moments evaluate
all six remaining integrals.

The harmonic endpoint strip can be removed using the already proved
moments, without a new floor-sum asymptotic. For `t≥1−δ`, choose `δ` so
`(1−δ)^k≥1/2`; then its indicator is bounded by `2t^k`.
The normalized harmonic mass of this strip has limsup at most `2/(k+1)`.
Taking `k` large transfers every bounded profile array that converges
uniformly away from `t=1` to its limiting harmonic polynomial.
