# Unattained power-comb boundaries from zero density

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** A82; ordinary convergence at an unattained subcritical endpoint.
- **Statement:** For `0<a<1/2`, `PowerCombTailConverges a` iff every zeta zero satisfies `Re ρ<1-a`.
- **Status:** Necessary direction available. Sufficient direction unproved; no new Lean theorem claimed.

## Corpus connection

`ZeroConfigurationGeometry/ThePrimeErrorKeepsItsBoundaryTrace` proves that,
at every bounding abscissa `β>1/2`, the normalized unsmoothed prime error
equals its absolutely convergent boundary-zero trace plus a term tending
to zero. No gap below the boundary is required.

`TheRightSubstripsHaveSummableReciprocalZeros` obtains reciprocal summability
from an explicit density deficit in each fixed right substrip. Its dyadic
proof retains more decay than reciprocal summability alone records.

The actual contact symbol is
`ζ(s+2a)(-ζ′/ζ(s+a)-ζ(s+a))`. At `β=1-a`, a boundary zero contributes
`-ζ(ρ+a)/(ρ-a)` to the normalized contact trace, per multiplicity copy.
The real pole contributes
`(-ζ′/ζ(β)-ζ(β))/(1-2a)`.

## Missing proof

1. Extract weighted reciprocal summability from the density deficit. Choose
   the retained substrip sufficiently close to `β` that its deficit absorbs
   growth of `ζ(ρ+a)`.
2. Prove the actual arithmetic contact prefix has that boundary trace,
   with a vanishing normalized error. The prime-error `o(x^β)` statement
   alone is insufficient: harmonic convolution can accumulate its error.
3. With no zeros on `Re ρ=β`, the trace vanishes and the existing finite
   comb decomposition gives convergence. Its limit is then fixed by
   `EveryConvergentPowerCombHasItsZeroSideLimit`.

The critical case `a=1/2` is excluded: the right-substrip density deficit
vanishes there, and ordinary critical convergence has already been disproved.

## Quantitative route

Write `β=1-a`. A right-substrip moment `Σ |γ|^-p<∞`, with `p<1`, would
give both `# {|γ|≤Y}≤S Y^p` and `Σ_(|γ|>Y)|γ|^-1≤S Y^(p-1)`.
In `abs_psi_sub_add_re_finiteSum_le`, take `Y=H=x^(1/8)` and
`θ=(β-σ)/2`. The count term has exponent `(p+1)/8<1/4`, the reciprocal
tail has exponent `β-(1-p)/8`, and the lower-strip term has exponent
`σ+7(β-σ)/16`. All are strictly below β. Thus this moment would upgrade
the existing prime trace to a power-saving remainder.

`RHTower.DeletionMixedRefinement.norm_powerSumRemainder_le` supplies the
uniform complex-prefix error
`|s(s+1)|/(Re s+1) N^(-Re s-1)`, plus the half endpoint.
Applied at `s=ρ+a`, it controls the finite zero convolution. For the omitted
zeros, the normalized convolution is bounded by
`(1+log N) Σ_(|γ|>Y)|γ|^-1`, using `Reρ≤β`; the same moment kills this tail.
Choosing σ close enough to β should also absorb the zeta multiplier.

The remaining arithmetic remainder has exponent strictly below `1-2a`.
Its convolution becomes a Riemann sum with an integrable power envelope.
The existing `tendsto_tailRiemannSum_of_powerBound` assumes continuity;
the contact remainder has jumps at reciprocal integers. That extension,
and the exact assembly remain unproved.

## Substrip moment input

Put `θ=min((σ−1/2)/2,1/4)`. The density bound gives dyadic bucket counts
`O((1+n)^B 2^((1−θ/3)n))`. Weighting each bucket by `2^(-pn)` is summable
for `p>1−θ/3`; taking `p=1−θ/6` gives `0<p<1`.
The moment bounds the low count by `S Y^p` and the reciprocal tail by
`S Y^(p−1)`, since each low atom costs at least `Y^-p` and each high
reciprocal costs at most `Y^(p−1)|γ|^-p`.

Lean input written, verification pending:
`ZeroConfigurationGeometry/TheRightSubstripsHaveSubunitMoments`,
`exists_rightSubstrip_power_tail_and_count`.

`RightSubstripCutoffsHavePowerTails` constructs the exact finite height
cutoffs and bounds their full omitted reciprocal mass.
`ThePrimeErrorHasAPowerSavingRightTrace` writes the resulting estimate
`|ψ(x)−x+x^β Re rightTrace(σ,β,x)|≤C x^κ`, `κ<β`, using
`κ=max((p+1)/8, β+(p−1)/8, (β+σ)/2)`.
Both are unverified. No gap below β is assumed.

## Uniform multiplier input

`PowerTailZetaMultiplierBound` is written, unverified. For `0<σ₀<1`,
`σ₀≤Re s≤1`, and `|Im s|≥1`, it proves
`|ζ(s)|≤(22+1/(1−σ₀)) |Im s|^(1−σ₀)`.
Take the Euler cutoff `N=floor |Im s|`; the prefix and Bernoulli
remainder are both `O(N^(1−σ₀))`, uniformly up to `Re s=1`.
With `σ₀=σ+a`, division by `ρ−a` leaves the moment weight
`|γ|^(-(σ+a))`. Choosing σ sufficiently close to `β=1−a` puts
this exponent above the density threshold.
