# Arithmetic upper bounds for the filtered prime current

- **Obstacle:** B13.
- **Stage:** 1-in-progress
- **Type:** CONJECTURE

## Required estimate

For the actual pole-and-divisor filter, find a prime-side bound smaller than
`h(t)^d Kφ(exp(−at),ρ₀−σ−it)` at some positive speed, with
`φ(t)=−π/2+1/t`. Its exponential rate is `a(β−σ)/2−dκ` when
`h(t)=exp(−κt)`. The former real-Gaussian rate also lost `π/4`.
The bound must not assume the zero exclusion it is intended to prove.

## Arithmetic candidates

The absolutely convergent Euler region gives the bound
`|A(t)| ≤ C h^d (1+t)^d exp(a(c−σ)t/2)` for each fixed `c>1`.
A Mellin–Barnes integral on `Re z=c` retains every filter factor:
`P_h(exp(h(z−β)))=O(h^d(1+|z|)^d)`.
Gamma decay makes the vertical integral finite; the literal Euler series
bounds `|ζ′/ζ(c+iv)|` independently of the exceptional divisor.
This estimate still exceeds the selected mode by exponential rate
`a(c−β)/2+π/4`. Contraction subtracts `dκ` from both rates.
Its paper proof and successful Lean audit are recorded in
`../3-formalized/b13-euler-bound-and-fast-contraction.md`.

Existing prime–pole estimates include
`ArithmeticIndexDescent.exists_screwPrimeSum_explicit_classical_rate` and
`exists_allPrimesMixedSource_all_detail_growing_coarse_rate`.
They have square-root-logarithmic savings, insufficient to bridge a fixed
power gap. Their transfer to this Gaussian filter is not assumed.

Ordinary mean-square estimates must be checked at the actual scale:
prime length `X=exp(at/2)`, height `t=2 log X/a`. Bounds requiring height
comparable to `X` do not control these readings.

## Status

The zero-free improvement gives, for every fixed `b>0`,
`|A(t)|≤C_b h^d(1+t)^(d+3) exp(a(1−σ)t/2−bt/log(2t))`, uniformly in spacing.
Its complete proof and Lean audit are recorded in
`../3-formalized/b13-zero-free-improvement-of-prime-filter-bound.md`.
It forces decay when `dκ≥a(1−σ)/2`, including equality. The exceptional-layer
growth theorem applies when `dκ<a(β−σ)/2−π/4`; the two regimes are disjoint.
No independent bound contradicting the exceptional-layer signal is proved.

The sharper independent estimate is now
`|A_h(t)|≤C h^d(1+t)^(d+5) exp(a(1−σ)t/2−a t w(2t+1)/4)`,
where `w(T)=(log T)^(−2/3)(log log T)^(−5/3)/10^8`.
It permits contraction relaxed by a positive multiple of the actual width;
see `../3-formalized/b13-vinogradov-korobov-prime-filter-bound.md`.
This remains a subexponential saving and does not close the fixed gap.

Complex damping supplies a different observable: at angle `−π/2+1/t`,
the complete literal prime filter has bound `C h^d t^N exp(at(c−σ)/2)`
for every `c>max(1,σ)`, while its selected kernel mode has rate
`a(Re ρ−σ)/2` without a fixed Gamma penalty. These are formalized in
`ComplexGaussianDamping.lean`. The complete rotated finite-layer recovery
is now proved in `BoundaryDampingReadsTheDivisor.lean`, with its full
contour error in `RotatedContoursForFiniteDivisorFilters.lean`.
Every positive speed and every eventually positive spacing tending to zero
recover the nonzero normalized divisor. Raw growth holds below
`dκ<a(β−σ)/2`; the independent zero-free bound below proves rotated decay
at `dκ≥a(1−σ)/2`. The remaining arithmetic gap is `a(1−β)/2>0`.
See `../3-formalized/b13-boundary-damping-recovers-exceptional-divisor.md`.

The normalized divisor limit now holds for every positive `h(t)→0`.
Thus raw decay at the arithmetic threshold coexists with nonzero normalized
recovery; contraction-induced smallness is not a contradictory upper estimate.
See `../3-formalized/b13-unrestricted-contracting-damping-limit.md`.

An upper estimate on one unbounded sequence of heights would suffice,
because the filtered lower law holds at every sufficiently large height.
A fixed-damping mean-square limit does not establish such a sequence for
`y=exp(−at)`; the required interchange of cutoff and height limits remains open.

## Proved boundary-angle zero-free bound

The complete rotated observable satisfies

`|A_h^rot(t)|≤C h^d t^N exp(a(1−σ)t/2−a t w(t³+1)/4)`

eventually, with constants and threshold uniform for `0<a≤t/4` and
`0≤h≤1`. A full zero-free rectangle of height `t³` includes bounded zeta
heights; exact pole cancellation and all filter factors survive the shift.
Horizontal edges and Euler tails have sufficient quadratic exponential decay.

For fixed `a>0`, the saving dominates every polynomial. It covers critical
contraction and the enlarged schedule
`h(t)=exp((−a(1−σ)/2+a w(t³+1)/8)t/d)`.
Both Lean modules and eleven transitive axiom audits pass; see
`../3-formalized/b13-boundary-vinogradov-korobov-bound.md`.
The fixed exponential gap to the selected divisor remains open.

## Polynomial damping scales

Divisor recovery now holds at radius `t^(−A)` for every sufficiently large
`A`, uniformly over positive contracting spacing, with normalized error
`O(1/t)`. For every `κ>0`, sufficiently large `A` forces raw prime-filter
growth at `h=t^(−κ)`. Each fixed grid sample has Gaussian damping scale
`t^((A+1)/2)`, with a proved uniform kernel envelope. See
`../3-formalized/b13-polynomial-damping-recovers-exceptional-divisor.md`.

The independent bound for the same observable is
`C h^d t^N t^(A(1−σ)/2) exp(−A log(t)w(t³+1)/4)`, with `C,N` independent
of `A`. It retains the power gap `A(1−Re ρ)/2`; no contradiction follows.

`Sieve.sum_vonMangoldt_block_decomp` decomposes a block against any complex
weight into two type-I sums and one type-II sum. The Gaussian type-II
contribution now has an independent bound with the actual coefficients and
product cutoff. For damping `ε=α−iξ`, the pair kernel is
`exp(−α(m₁²+m₂²)P²) min(ℓ,8ℓ sqrt(λ)+12/sqrt(λ))`, where
`λ=|ξ(m₁²−m₂²)|/π`, `[P,Q)` is the intersection of both divisor fibres,
and `ℓ=max(Q−P,0)`. At zero curvature the minimum is replaced by `ℓ`.
The height phase cancels exactly. The bound retains the real damping and
has a proved strict saving when `λ≤1/1024` and `48≤ℓ sqrt(λ)`.
See `../3-formalized/b13-gaussian-vaughan-bilinear-cancellation.md`.

The Gaussian type-I estimates and the complete finite-block bound are now
proved. On `[P,Q)`, the phase curvature lies between
`λ=ξ/π+t/(2πQ²)` and `Hλ=ξ/π+t/(2πP²)`; every prefix has bound
`min(Q−P,8(Q−P)H√λ+12/√λ)`. Abel summation retains the initial Gaussian
and abscissa weights, and the logarithmic term costs `2 log(Q−1)`.
The two exact truncated-coefficient fibre sums plus the square root of
the type-II energy bound the literal von Mangoldt block, including lower-half
interior rotations. The type-I bound halves the trivial one when
`H√λ≤1/32` and `(Q−P)√λ≥48`.
See `../3-formalized/b13-complete-gaussian-vaughan-block-bound.md`.

First-derivative cancellation now improves the dyadic type-II bound.
Put `θ=ξD²M²`, `Wσ=DM D^(−σ) M^(−σ)`, and `H_N=Σ_{n=1}^N 1/n`.
For `σ,α≥0`, `ξ>0`, positive endpoints, and `16ξDM²≤π`, the actual
rectangle, with both arithmetic coefficients and the product cutoff, obeys

`|S|²≤C Wσ² log(2D)(1+H_{2M}³) exp(−2αD²M²)`
`  × [1/M+2π(1+log(2M))/θ]`.

The constant is uniform in all parameters and Vaughan cutoffs. For `t>0`,
`t≤32θ` and `M≥t`, the bound simplifies to
`C Wσ² (1+log(2D))(1+log(2M))⁴ exp(−2αD²M²)/t`.
Every rectangle containing a quadratic stationary point satisfies the
scale condition, since `t=2ξ(dm)²≤32θ`. First-band and short-factor
conditions are still required. See
`../3-formalized/b13-nonstationary-gaussian-typeII-energy.md`.

The height cancels from correlations, leaving a small-product loss.
The first-moment and all-scale results below resolve it and complete the
raw prime bound. Pole cancellation and contracting filter factors still
require arithmetic control before comparison with the selected mode.
The near-diagonal estimate treats a different phase and is not used.

## First moments remove the small-product singularity

Multiplying each Gaussian sample by `ε_j n²/t` gives exactly
`(ε_0/t)` times the original pole/divisor filter at abscissa `σ−2`.
The full normalized divisor reading survives, multiplied by `−i/2`,
at sufficiently large polynomial damping exponents on every contracting
grid. No extra contraction power appears. The boundary samples eventually
satisfy `0<α≤ξ`, uniformly in the positive damping radius.

The independent squared bound for the actual first-moment rectangle is
the previous envelope times `C(θ/t)²`. If `θ≤t`, choose Vaughan cutoffs
`32t≤πU` and `2t≤V`. A rectangle with `2D≤U` or `2M≤V` vanishes;
every other rectangle has `16t≤πD` and `t≤M`. Thus every small-product
rectangle satisfies

`|S₁|²≤C Wσ² (1+log(2D))(1+log(2M))⁴ exp(−2αD²M²) θ/t²`.

The inverse-θ loss is removed while retaining a nonzero divisor signal.
See `../3-formalized/b13-gaussian-moments-suppress-small-products.md`.
The observable has changed; its full normalized divisor reading survives.

The all-scale extension now covers every rectangle with
`πU≥128t log t`, `V≥2t`, and `ξ/(2t)≤α≤ξ`:

`|S₁|²≤C Wσ² (1+log(2D))(1+log(2M))⁴ exp(−αD²M²)/t`.

Below `ξD²M²=4t log t`, coefficient support forces the nonstationary
band. Above it, Gaussian decay supplies the inverse-height factor from
the absolute coefficient-energy bound. Boundary damping supplies the
lower sector uniformly in every positive radius. Exact dyadic assembly
also bounds the actual finite type-II convolution, retaining Gaussian
decay. See `../3-formalized/b13-all-scale-gaussian-moment-bound.md`.
The type-II bound now passes to the actual infinite convolution. For
`0≤σ<1`, choose `X=max(1,sqrt(2/α))`; then

`|T₁|≪σ X^(1−σ)(1+log X)^4/sqrt(t)`.

Dyadic summation is uniform in both prime endpoints. The coefficient
bound `|(typeIILong U * typeIIShort V)(n)|≤2n²` proves absolute
convergence before passing to the infinite sum. Thus type-II truncation
and infinite tails are closed. See
`../3-formalized/b13-uniform-gaussian-moment-typeII-bound.md`.
The complete raw moment now satisfies, under the same sector/cutoffs and
`t≥2`, `αX²=2`, `tUV≤X`,

`|M₁|≪σ X^(1−σ)(1+log X)^6/sqrt(t)`.

Type-I dilation retains `sqrt(αt)+1/(b sqrt(t))`. The exact coefficient
bounds `|Λ_U*μ_V(b)|≤log b`, `|μ_V(b)|≤1`, their finite supports and
`tUV≤X` pay the total masses; reciprocal masses cost logarithms. The
finite head and absolute convergence are included. See
`../3-formalized/b13-complete-infinite-gaussian-moment-bound.md`.
Arithmetic control preserving pole/filter cancellation remains. The
complete bound retains the pole-scale exponent and does not beat the
selected divisor signal.

## Pole extraction from the first type-I term

For `c=Λ_U*μ_V`, retain `A_UV=Σ_{b≤UV}c(b)/b` signed. With
`P₁(s,ε,t)=ε/(2t)Γ((3−s)/2)ε^(−(3−s)/2)`, the actual complete
first type-I convolution satisfies

`|Σ_n(ζ*c)(n)M₁(n)−A_UV P₁|`
` ≤ [4Γ(1−σ/2)+16Γ(2−σ/2)] UV log(UV)t α^(σ/2)`.

This uses `0≤σ<1`, `t≥2`, `0<α≤ξ≤2αt`, and `UV≥1`; no
Vaughan cutoff or scale separation is needed. At `αX²=2`, the
remainder is `≪σ UV log(UV)t X^(−σ)`. Integration by parts on
lattice cells bounds the discrepancy by total variation, independently
of divisor spacing. The complex Gamma integral gives the exact main
term before absolute values enter. See
`../3-formalized/b13-typeI-pole-extraction.md`.

## Second-order first type-I cancellation

Under the same sector conditions and `αX²=2`, the first type-I
remainder improves to

`|Σ_n(ζ*c)(n)M₁(n)−A_UV P₁|`
` ≤ 2Dσ (UV)² log(UV)t² X^(−1−σ)`,

where `Dσ=Γ((1−σ)/2)+10Γ((3−σ)/2)+16Γ((5−σ)/2)`.
The complete fibre remainder is at most `2Dσ bt²X^(−1−σ)`.
The second derivative is integrable for `σ<1`, and the trapezoidal
endpoint correction vanishes. This gains a factor `UVt/X` in the
arithmetic error scale. Exact proof and Lean declarations:
`../3-formalized/b13-second-order-gaussian-lattice-cancellation.md`.

## Signed logarithmic type-I main terms

Let `B_V=Σ_{b≤V}μ(b)/b`, `D_V=Σ_{b≤V}μ(b)log b/b`, and
`L₁=∫₀∞log x·M₁(x)dx`. Under the same sector conditions, `αX²=2`
and `V≤X`, the actual logarithmic convolution satisfies

`|Σ_n(log*μ_V)(n)M₁(n)−(B_V L₁−D_V P₁)|`
` ≪σ Vt X^(−σ)(1+log X)`.

The lattice comparison uses `|log(x/b)|≤x/X+X/x+|log(X/b)|`.
All resulting Gaussian moments converge for `σ<1`; exact signed
reciprocal Möbius masses remain outside the error estimate. See
`../3-formalized/b13-logarithmic-typeI-pole-extraction.md`.

Both type-I remainders have a full Gaussian-length saving. Their signed
main terms combine with type II as below. Centred type-II cancellation
and the bound for the complete filtered current remain open.

## Second-order logarithmic type-I cancellation

Under the same conditions, the logarithmic remainder improves to

`|Σ_n(log*μ_V)(n)M₁(n)−(B_V L₁−D_V P₁)|`
` ≪σ V²t²X^(−1−σ)(1+log X)`.

Fractional powers with margin `δ=(1−σ)/2` preserve integrability of
`x^(−σ)log x` at zero. Two integrations by parts and the vanishing
endpoint correction give fibre error
`≪σ bt²X^(−1−σ)(1+|log(X/b)|)`. This gains `Vt/X` in the actual
logarithmic type-I convolution, keeping both signed continuum terms.
Both type-I errors now have second-order bounds; centred type II remains
open. Proof and explicit constant:
`../3-formalized/b13-second-order-logarithmic-lattice-cancellation.md`.

## Exact signal size and the short-scale boundary

The selected-mode exponent is now exact:
`E=((A+1)(Re ρ−σ)−1)/2−dκ`, with positive normalized modulus
`C(x)=sqrt(2π)/2·(1/2)^((x−1)/2)·exp(−1/2)` for `x=Re ρ−σ`.
Above the divisor-recovery threshold, the literal prime filter has the same
exponent and coefficient equal to the full divisor amplitude times `C(x)`.
Critical contraction `κ=((A+1)x−1)/(2d)` gives a positive limiting modulus
independent of `A`. See
`../3-formalized/b13-sharp-polynomial-observation-boundary.md`.

For every radius `y(t)≥1/t` and bounded spacing `0≤h(t)≤1`, the selected
mode tends to zero when `0<x<1/2`. Thus no raw-growth contradiction is
available at polynomial Gaussian scales `t^((A+1)/2)≤t`. This does not
prove prime-filter decay or rule out an upper bound relative to the decaying
mode. The independent upper estimate above remains unchanged; cancellation
below the exact signal size is still missing.


## Uniform reduction to centred type II

For `1/2≤σ<1`, `t≥2`, `0<α≤ξ≤2αt`, `αX²=2`,
`1≤U,V≤t²`, and `X≥t⁸`,

`M₁−P₁=T_II+B_V L₁−(1+A_UV+D_V)P₁+Oσ(1/t)`.

The explicit error is `(8Dσ+3Cσ+8)/t`; two allowed cutoff pairs differ
by at most twice this. Both lattice errors and the finite head are now
uniformly negligible. The remaining object is the centred actual type-II
sum, including its logarithmic continuum term. No bound for that object
or contracting-grid factor is supplied. Proof and Lean audit:
`../3-formalized/b13-centred-vaughan-current.md`.
