# Arithmetic saving for every logarithmic-clock derivative

- **ID:** W11-NQD
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [Quantitative boundary saving](../3-formalized/ads3-narain-quantitative-boundary-saving.md)

## Conjecture

For fixed positive target heights, put
`R(y)=yA_YZ(y)+(3/π)log y−B_YZ` and `H(L)=exp(L/2)R(exp(−L))`.
There is `c>0` such that, for every integer `k≥0`, there is `C_k>0` with

`|H^(k)(L)|≤C_k exp(−c L w(L))`

for all sufficiently large `L` (threshold allowed to depend on `k`), with
`w(L)=(log L)^(−2/3)(log log L)^(−5/3)/10^8`.
Thus every logarithmic-clock derivative has every fixed inverse-power
saving. A bound on `H` alone does not justify differentiating its error.

## Corpus mechanism

The proved boundary identity gives
`H(L)=(2π)^(−1)∫ exp(iLt)M(it)dt`, where
`M=narainMellinMean Y Z`. Its exponential envelope gives every absolute
spectral moment. `RHTower.integrable_expDecay_mul_pow` and
`hasDerivAt_expFourier` in `ExpDecayFourierAnalytic.lean` provide moment
integrability and differentiation under the integral.
`deningerFourier_contDiff` in `Deninger/DeningerFourierBoundedDerivs.lean`
provides smoothness from these moments. These imported endpoints have transitive axiom audits containing only
`propext`, `Classical.choice` and `Quot.sound`.

The derivative integral has integrand `u^k M(u)` on the Mellin boundary.
On the arithmetic rectangle, `|Re u|≤1/8` gives
`|u|^k≤(1+|Im u|)^k`. This preserves analyticity and increases only the
polynomial exponent in the existing rectangle envelope. The same
finite contour, exponential tail estimate and polynomial absorption
should therefore give the displayed rate for each `k`. The width parameter
comes from `M` alone; absorbing polynomial growth preserves a single
positive saving constant `c` for every derivative order.

The required derivative identity, weighted rectangle assembly and
actual-source conclusion remain unformalized. No bound on derivatives
of the reciprocal zeta factor is needed for this mechanism.

The proved [Schwartz construction](../3-formalized/ads3-narain-boundary-schwartz.md)
uses the corpus's Landau interpolation: the spectral exponential envelope
gives bounded clock derivatives, while the source estimates give rapid
function decay on both rays. That qualitative conclusion needs no new
weighted contour. Preserving one quantitative `c` for every derivative
order remains the stronger target here.

## Uniform analytic-clock refinement

A stronger candidate has constants `C,c,r>0` and one threshold `L₀`
independent of derivative order:

`|H^(k)(L)|≤C k! r^(−k) exp(−cLw(L))` for every `k≥0` and `L≥L₀`.

The exponential spectral envelope gives a holomorphic clock extension.
A moving-contour estimate uniform on a fixed complex disk around each
large real `L` would retain the same saving: bounded imaginary clock
shifts consume only part of the vertical exponential decay, and bounded
real shifts cost at most a constant on the displaced edge. Cauchy's
estimate then supplies the factorial bound and common threshold.
The corpus uses `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`
in `HTGeometry/HolomorphicRealTaylor.lean` for exactly this final step.
`GaloisForLFunctions.RHTower.iteratedDeriv_ofReal_comp` in
`RealJetsOfHolomorphic.lean` transports complex jets to the real clock
on a local ball; its premises require only that ball, not an entire extension.
The strip-analyticity and local jet-transport endpoints have the same
standard transitive axiom set.

For `z=L+iv`, apply the existing real-clock rectangle lemma to
`M_v(u)=exp(ivu)M(u)`. If `|v|≤r`, then
`|exp(ivu)|≤exp(r|Im u|)`, so the same rectangle envelope holds with
vertical decay exponent `π/2−r`. This absorbs the imaginary shift before
estimating the left edge; replacing it by `exp(rT)` after discarding
vertical decay would lose the saving. Taking `r≤π/8` also leaves a
uniform exponential boundary tail. Thus the proposed complex estimate
needs a uniform twist bound and tail assembly, not a new rectangle identity.

For a fixed disk radius `r≤π/16` around real `L`, choose contour height
`T=L`. On the disk, `Re z≥L−r` and `d(L)≤1/8`, so
`exp(−d(L)Re z)≤exp(r/8)exp(−d(L)L)`.
The remaining tail `exp(−πL/8)` is at most `exp(−d(L)L)`.
The already proved polynomial absorption therefore supplies the same
`exp(−cLw(L))` disk bound, up to a constant independent of derivative
order. Cauchy on this fixed disk gives the displayed factorial estimate.

Uniform complex-clock contours, their actual-source identification and
the resulting quantifier order remain unformalized. The real-frequency
bound alone does not establish the required disk supremum.

The [universal-constant refinement](../3-formalized/ads3-narain-universal-saving-constant.md)
proves the scalar exponent `c=1/128` independently of target heights.
The same absorption applies to the proposed complex-disk bound.

## Two-sided refinement

For `L→−∞`, shift to the fixed line `Re u=1/4`. The actual mean is
analytic between this line and the boundary, and its existing positive-line
bounds give absolute integrability. The known good-height sequence controls
the horizontal edges. Applying this to `u^k M(u)` predicts
`|H^(k)(L)|≤D_k exp(L/4)` for every `k` at sufficiently negative `L`.
Together with the positive-clock estimate, this would make `H` Schwartz.
Fourier inversion would then give Schwartz regularity of `t↦M(it)` as well.
This is a separate route to the stronger boundary-function claim in the
[logarithmic-saving card](../3-formalized/ads3-narain-average-logarithmic-savings.md), avoiding
spectral differentiation of the reciprocal zeta factor. The two-sided derivative contours remain unformalized; Schwartz
regularity itself is already proved by Landau interpolation and Fourier
inversion.

A sharper two-sided candidate allows every `0<γ<1/2`, with one fixed
Cauchy radius and threshold for all orders:
`|H^(n)(L)|≤C n! (π/16)^(−n) exp(γL)` as `L→−∞`.
Use a fixed Mellin line `Re u=η` with `γ<η<1/2`; polynomial contour
losses are absorbed by the gap `η−γ`. The actual large-height source
also predicts `exp(−L/2)H(L)/(−L)→3/π`, so the endpoint bound
`H(L)=O(exp(L/2))` should fail. These quantitative derivative bounds
and the sharp endpoint obstruction remain unformalized.

## Gates

- [x] 0 → 1: actual Fourier identity, spectral moments, strip-analyticity and jet-transport inputs audited.
- [ ] 1 → 2: all weighted contour estimates and derivative identities proved.
- [ ] 2 → 3: direct Lean checks, transitive axiom audits and umbrella imports.
