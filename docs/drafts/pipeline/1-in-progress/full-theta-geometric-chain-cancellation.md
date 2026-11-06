# Geometric-chain cancellation for theta aperture pairs

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ6
- **Statement:** For every integer `q≥2`, `0<a<1/2` and real frequency `b`, the aperture spectrum of the complete ordinary source supported on `1,q,q²,…` is strictly positive.

The corpus identity `thetaPairApertureSpectrum_eq_shifted` turns the pair
`(q^i,q^j)` into a common positive radial density times
`p^(i+j) cos((i−j)θ) w_a((s−(i+j)h)₊)`, where
`h=log q`, `p=exp(−h/2)` and `θ=bh`.
Grouping by `i+j=k` gives the Chebyshev coefficient
`U_k(cos θ)=Σ_(i=0)^k cos((2i−k)θ)`.

**Proposed cancellation:** the twice-cumulative coefficients
`C_k=Σ_(j=0)^k(k+1−j)U_j(cos θ)` are nonnegative. The finite sequence
`f_k=p^k w_a((s−kh)₊)` has nonnegative second differences. Two discrete
summations by parts would express the entire common-center sum as
`Σ C_k(f_k−2f_(k+1)+f_(k+2))`, paying each diagonal once.

**Full-source issue:** distinct prime chains interact. Positivity of each
chain alone does not prove positivity after multiplicative convolution.
The next test is whether the resulting positive representation survives
adding an independent prime, or whether the radial Bessel integration is
essential for that interaction.

Corpus anchors: `TwoAtomApertureSpectrum`, `TwoAtomApertureWeight`,
`ThetaPairCenterTailSeries`, `BesselRadialSlice`.
The cumulative-coefficient identity, strictness, infinite-source reassembly
and literal all-rank bridge remain to be proved and formalized.
