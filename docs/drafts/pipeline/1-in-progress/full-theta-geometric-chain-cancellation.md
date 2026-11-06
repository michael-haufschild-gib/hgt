# Literal all-rank jets of a geometric theta source

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ6
- **Statement:** For every integer `q≥2`, every finite rank and `0<a<1/2`, the literal aperture-weighted signed mixed-jet Hankel matrix of the ordinary source supported on `1,q,q²,…` is positive definite.

The corpus identity `thetaPairApertureSpectrum_eq_shifted` turns the pair
`(q^i,q^j)` into a common positive radial density times
`p^(i+j) cos((i−j)θ) w_a((s−(i+j)h)₊)`, where
`h=log q`, `p=exp(−h/2)` and `θ=bh`.
Grouping by `i+j=k` gives the Chebyshev coefficient
`U_k(cos θ)=Σ_(i=0)^k cos((2i−k)θ)`.

The [complete-chain spectrum](../3-formalized/geometric-theta-aperture-spectrum.md)
is strictly positive, with absolute convergence before cancellation inside
each total-exponent block. The proof uses nonnegative twice-cumulative
phase coefficients and strictly convex damped aperture weights.

**Remaining bridge:** construct the infinite masked source, identify its
literal Fourier transform and mixed derivatives with the proved pair
series, and apply the positive-density moment theorem. Spectrum positivity
alone does not discharge these regularity and reassembly obligations.

**Full-source issue:** distinct prime chains interact. Positivity of each
chain alone does not prove positivity after multiplicative convolution.
The next test is whether the resulting positive representation survives
adding an independent prime, or whether the radial Bessel integration is
essential for that interaction.

Corpus anchors: `TwoAtomApertureSpectrum`, `TwoAtomApertureWeight`,
`ThetaPairCenterTailSeries`, `BesselRadialSlice`.
