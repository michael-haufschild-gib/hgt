# Camera windows give negative Weil tests

- **ID:** camera-windows-give-negative-weil-tests
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** review-0511, A39.

## Target

Compose local camera windows with a negative diagonal Weil test at aperture
`λL_T`, `λ>1`, retaining cubic-logarithmic tail resolution. No mimic is an
input to this construction.

## Candidate mechanism

The camera at half that aperture supplies `F,G` whose point image is
`F̂(γ)·conj(Ĝ(conj γ))`. A convolution realizes this product as one Fourier
transform, doubling aperture. Thus the condition for this construction is
exactly `λ>1` when the actual ζ density factor tends to one.

For a separately isolated off-line point, normalize this transform to one
there and zero at its reflected partner. Subtract a normalized camera for that partner;
the resulting values are `1` and `−1`, giving pair contribution `−2m`.
If the normalized absolute tail is at most `E`, the new test's quadratic
tail is at most `4E²`.

For an isolated FE pair at spectral coordinates `T±iδ`, use the order-one camera centred at `T`.
Its normalized convolution transform has values within `δ²P` of `±δ`,
where `P=T^(M_c+κ)` for camera isolation exponent `M_c`. If `δP≤1/4`, each point-image differs from `−δ²`
by at most `9δ²/16`; the pair contributes at most `−7mδ²/8`.
The quadratic tail is at most `E²`, so `δ≥2E` gives a negative test.
Multiplicity is arbitrary and equal on the two reflected points.

These two cases cover a pair whose other zeros lie at distance at least
`T^(−M)` from each endpoint. Use the order-one camera with isolation exponent
`M+1` when `δ≤T^(−(M+κ+2))`: the centre's external separation is at least
`T^(−M)/2≥T^(−(M+1))`. Otherwise use point isolation with exponent
`M+κ+3`; this scale is smaller than both the partner gap and the external
separation. The resulting positivity receiver should say that every
off-line zero has depth `<2E` or another non-reflected zero within the
polynomial isolation scale. It has no count, mass or mimic premise for ζ.

## Required closure

`tsum_far_multDiff_le` already bounds the absolute weighted camera tail;
`camera_tail_budget` bounds it after division by the target floor.
Expose these estimates together with the local variation and exact blindness
from `exists_local_slow_pair`, including the order-one displacement multiplier.
For the convolution transform `q`, reflection preserves tail membership and
multiplicity. Each reflected value is bounded by `Σ_far m|q|`, hence
`Σ_far m|q(γ)q(conj γ)|≤(Σ_far m|q|)²`. Formalize this comparison and
the two-case geometric reduction before claiming the stated receiver.
