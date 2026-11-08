# Alias-notch saturation for differentiated splines

- **ID:** alias-notch-saturation-for-differentiated-splines
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** Differentiated cardinal splines can have arbitrarily high-order Fourier zeros while their complete aliasing density has an exact seventh-order notch.

## Candidate exact law

Let `B_m` be the convolution of `m` unit interval indicators and `g_m=D^(m-4)B_m`, with integer `m≥5`. Write `a_g(s)=Σ_{k≥1}|ĝ(2πks)|²` and `M_g=∫|g|²`. For `0<ε<1/m`, the proposed identity is

`a_g(1+ε) = M_g ε^7 / (2(1+ε)^8)`.

The Fourier numerator is periodic on integer frequencies, so
`a_g(1+ε)=(ε/(1+ε))^8 a_g(ε)`.
At overlap `ε`, the autocorrelation translates are disjoint. Poisson summation and `∫g=0` therefore give `a_g(ε)=M_g/(2ε)`.

## Relevance

The sum over all harmonics loses the arbitrarily high order of each individual Fourier zero. Harmonics of size `1/ε` retain seventh-order mass. Adding `B_m` restores a nonzero integral; proving the mixed alias terms have higher order is a separate step. This calculation does not establish arithmetic matrix positivity or AAL.

For odd `m≥5`, center the splines and put `φ_m=B_m+D^(m-4)B_m`. The proposed Fourier identity makes the two summands respectively real and purely imaginary on the real frequency axis. Their squared spectra therefore add. With `s=j+ε`, the candidate unit-integral formula is

`a_φ(s) = M_g ε^7/(2s^8) + M_B ε^(2m-1)/(2s^(2m)) - ε^(2m)/(2s^(2m))`.

This would retain a strictly positive seventh-order coefficient despite unbounded harmonic zero multiplicity. The mixed-profile identity remains part of the formalization target.

## Status

Formalization pending. Exact normalization, Fourier convention, support, and strict positivity of `M_g` must be verified in the corpus.
