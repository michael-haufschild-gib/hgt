# Explicit camera heights

- **ID:** explicit-camera-height
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** review-0511, A42.

## Target

Expose a finite height expression for the camera readout and its moment,
pair-gap and isolation consequences, with numerical counting inputs for ζ.
No threshold selected from an eventual statement counts as effectivization.

## Corpus reduction

`discMoment_readout_rvm` already constructs its parameter-dependent height as
`2π exp(U₀)`. Its proof defines `U₀` by maxima, logarithms and the constants
`growthRate`, `floorRate`, `slowConst`; the latter retains
`latticeSumConst=Σ_{k∈ℤ}(1+k²)⁻¹`. The local-count specialization still obtains
its Backlund constant and starting height existentially.

`SquareRootThreshold/EffectiveHorizons/XiContourBounds.lean` now proves
`|∫ Im(ζ'/ζ)|≤29π log T≤100 log T` for admissible `T≥4`.
With the existing good-height contour count, this should give the sharp
local-density formula with `T₀=10` and additive constant `A=200`.
Its slope remains the exact Riemann–von Mangoldt density.

For a density factor `θ>1`, take
`H(θ)=max(20,2π exp(max(1,2/(θ−1))))` and
`A(θ)=3θ/(2π)+200(1+log(4π))+1`.
The centred count at `T≥H(θ)` then has slope `θ log(T/2π)/(2π)`
and additive term `A(θ) log(T/2π)` throughout `[T/2,3T/2]`.

The existing `RHTower.WeilDeletion.tsum_inv_normSq_spectralPoint_lt`
and `carrier_tsum_le` bound the actual ζ Lorentzian mass by `33/100`.
Pairing the nonzero integer lattice terms and comparing them to the
inverse-square series bounds `latticeSumConst` by `5`. Thus the relative
rate constant is at most

`πλ+2+320·slackBound(ℓ)·λ²·(1+slackBound(ℓ)(2π)^M+slackBound(ℓ)λ)`.

For the actual ζ camera at any `λ>1/2`, use `θ=λ+1/2` and the maximum
of `H(θ)` and the resulting explicit general camera height. No zero-count
or tail estimate remains as an analytic premise in that specialization.

## Finite height expression

For moment order `J`, density factor `θ≥0`, aperture factor `λ>θ/2`,
count constant `A≥0`, tail mass `S≥0`, isolation exponent `M≥0` and tail
rate `K′≥0`, put

`β=λ−θ/2`, `ℓ=2πA/λ`, `e=6·slackBound(ℓ)(1+slackBound(ℓ))`,

`K=growthRate(ℓ)λ²+floorRate(ℓ)λ²(λ+8M)+2`,

`B=eλ+K+K′+2+J`, `ρ=8B/β`, `α=(8B(1+ρ))⁻¹`, `q=max(0,log α⁻¹)`,

`U=max(1,2π/λ,2Bq+(λ+4)+(log(max(S,1))+605)+1)`.

The point height is `2π exp U` with `J=K′=0`. If `C` is the finite
relative-rate bound above, the moment height is

`2π exp(max(U,log(max(6C,4λ)+1)))`.

The existing `growthRate`, `floorRate` and `slackBound` are finite
logarithmic expressions. These formulas contain no infinite sum or threshold
selected from an eventual statement.

## Proof

1. A good ordinate has no ξ zero: every ξ zero gives a nontrivial ζ zero in
   the open strip. Commuting the imaginary-part map with the horizontal
   integral transfers the bound `29π log T≤100 log T`. The good-height
   contour count and admissible ordinates in `[x−2,x−1]`, `[y,y+1]` give
   the stated sharp count for `x≥10`. At `T≥H(θ)`, write `u=log(T/2π)`.
   Then `u≥1`, `(θ−1)u≥2`, the centred density is at most `(u+2)/(2π)`,
   and `log(3T/2+2)≤(1+log(4π))u`. This proves the camera count.
2. Each Lorentzian zero term is bounded by its reciprocal-square term.
   The multiplicity-preserving carrier comparison and the existing
   reciprocal-square bound give mass `<33/100`. For the lattice,
   `(1+k²)⁻¹≤k⁻²` away from zero; each positive half has sum at most two.
   Hence the full lattice sum is at most five, giving `slowConst≤C`.
3. The definition of `U` gives every inequality in `rvm_order_facts` and
   `camera_tail_budget`: choose decay order `⌈(K+K′)u²⌉` and spline order
   `⌈windowExponent⌉+⌈(K+K′)u²⌉+J`. Their ratio to bump width is at most
   `ρu`. The additional moment-height term gives `exp u≥6·slowConst`
   and `exp u≥4λ`. Thus `rvm_readout_core` applies with its unchanged
   count, mass and isolation conditions. The point construction is the
   same floor/tail estimate at `J=K′=0`.
4. For mimics, polarization cancels the window images. First and second
   moments give centre error `4r²T^(M+κ)+E` and squared-gap error
   `24r³T^(M+κ)+4E`; an isolated dipole satisfies `d≤2E`, where
   `E=exp(−K′u³)`. Point isolation reads integer multiplicity to error
   `1/4`, so mimics agree there. For scale `δ/log T`, enlarge the point
   height at `M=1` by `2δ⁻¹max(0,log(2/δ))`; then `T⁻¹≤δ/log T`.
   The Hankel gap, discriminant and bordered cluster-location polynomial
   use these same moment bounds at orders `2`, `2k−2` and `2k−1`, with
   no additional height threshold.
5. For actual ζ, take `θ=λ+1/2`, `A=A(θ)` and `S=33/100`, then maximize
   with `H(θ)`. Both analytic inputs are now unconditional. The resulting
   point and moment theorems retain only their geometric isolation conditions.

## Lean status

Sources are in `ZeroConfigurationGeometry/EffectiveHeights/`: `LocalZetaCount`,
`SpectralMass`, `LatticeRate`, `Heights`, `PointReadout`, `MomentReadout`,
`ClusterConsequences`, `ImageConsequences` and `ZetaReadout`. Formalization and final audits remain
in progress; this card does not yet count as a valid proof.
