# Camera windows give negative Weil tests

- **ID:** camera-windows-give-negative-weil-tests
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** review-0511, A39; F6 requires every zero, without a separation alternative.

## Target

For every `λ>1` and `c>0`, give a finite `T₀` such that positivity at aperture
`λL_T`, `T≥T₀`, implies `|Re ρ−1/2|<exp(−c log³(T/2π))` for each zero at height `T`.
No mimic, zero-separation assumption or restriction on multiplicity is permitted.

## Cluster construction

Put `μ=λ/2`, `θ=μ+1/2`, `u=log(T/2π)`, `A=zetaCameraCountConstant(θ)` and
`C=θ/π+A`. The proved ζ count bounds the number of distinct zeros in a unit
ball about a zero by `Cu`. Its Lorentzian mass is `<33/100`.

Suppose the zero has depth `δ≥exp(−cu³)`. Set `B=slowExponent(μ)+2`.
The existing `SquareRootThreshold.exists_empty_annulus` gives an index
`j≤Cu` and an empty annulus with outer radius `η=(δ/4)/T^(Bj)` and inner
radius `r=η/T^B`. Thus `η≤δ/4` and

`max(0,log(1/η))≤(c+2+8BC)u³`.

The normalized variation estimate is
`η·slowRate(H,L,η,ε,1)≤slowRate(H,L,1,ε,1)` for `0<η≤1`.
The existing polynomial rate at isolation radius one therefore gives
`6r·slowRate≤T^(−2)≤1/4`. The camera is uniformly close to one on the inner
cluster, regardless of internal spacings, and blind to all other nearby zeros.
The reflected cluster is disjoint and has the same isolation annulus.

At cubic-logarithmic isolation, choose decay order `k=⌈Ku⁴⌉` and spline
order `m=⌈windowExponent⌉+k`. The floor costs at most a fixed multiple of
`u⁵`; the spline logarithm is bounded by `u⁵+6M_Kq u⁴`.
A finite parameter choice in the tail inequality gives absolute Fourier tail
at most `1/4` for each normalized convolution camera.

Convolution converts each camera image into one Fourier transform and doubles
aperture, giving `λL_T`. Subtract the transforms for the two reflected clusters.
On either cluster the values at a reflected pair are within `1/4` of opposite
unit values, so each point-image has real part at most `−7/16`.
All other nearby terms vanish. The quadratic far tail is bounded by the square
of the absolute Fourier tail, hence by `(1/4+1/4)²=1/4`.
One zero of multiplicity at least one already gives total real part at most
`−7/16+1/4<0`.

## Lean obligations

Expose the absolute Fourier tail from `exists_local_slow_pair` and
`tsum_far_multDiff_le`; prove its quadratic comparison, the normalized
variation inequality, quartic-order tail estimate, and the ζ annulus reduction.
Then assemble the negative test and positivity receiver with explicit heights.
All new proofs are still being checked. The earlier isolated-pair construction
is insufficient for the full target and does not close A39.
