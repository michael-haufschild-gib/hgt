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
there and zero at its reflected partner. Subtract its reflected conjugate;
the resulting values are `1` and `−1`, giving a strictly negative pair
contribution. For a tiny isolated FE pair, instead multiply the nearly
constant camera transform by the displacement from its real spectral centre.
Its two values have opposite signs, and the negative contribution has size
proportional to the squared depth.

## Required closure

The camera's complex readout error alone does not bound the diagonal tail.
Prove the corresponding absolute weighted tail bound from its floor and
decay estimates, including the displacement multiplier. Then bound the
convolution test's quadratic tail and compare it with the negative pair
contribution. The quantitative isolation and depth ranges must remain
explicit in the final statement.
