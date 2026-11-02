# Continuous spectrum of actual logarithmic Cauchy averaging

- **Stage:** 1-in-progress
- **Type:** Paper theorem; Lean formalization in progress
- **Route:** PM

For `Re w>0`, let `T_w` be the actual logarithmic Cauchy operator and
`φ_w(ξ)=m(w,w/2+2πiξ)` its certified Gamma multiplier.

## Targets

1. `spectrum(T_w) = {0} ∪ range φ_w = closure(range φ_w)`.
2. For every complex `λ`, `T_w f=λ f` implies `f=0` in `L²`.
3. In particular, zero belongs to the spectrum without an eigenvector;
   the actual Cauchy transform has no bounded inverse on all of `L²`.

## Source and proof mechanism

The literal logarithmic kernel is integrable. Its Fourier transform is
continuous, tends to zero at infinity, and is nowhere zero. The local corpus
provides `HTGeometry.circleOfC0`, extending such a symbol continuously to the
Cayley circle with value zero at infinity, and a faithful unital circle
multiplier representation. Its range is a closed star subalgebra because
the representation is an isometry from a complete space. Spectral permanence
for that closed subalgebra, and the algebra equivalence onto its range,
identify the actual operator spectrum with the compactified symbol range.
The circle point at infinity contributes zero; every other circle point
comes from a finite real frequency. Fourier decay places zero in the closure
of the finite-frequency range.

For nonzero `λ`, the Gamma symbol minus `λ` is holomorphic in
`−1<Re u<Re w+1`. Fourier decay ensures it is not identically zero.
The connected-strip identity theorem makes its zero set countable; the
injective central-frequency parametrization gives a null real level set.
An `L²` eigenvector would have Fourier support in that null set. For `λ=0`,
the already certified injectivity applies.

## Scope and positive conclusion

This is a proposed classification of the actual Cauchy operator, not the
Mayer transfer operator. Its positive content is the explicit continuous
Gamma spectral curve, together with the sharp operator norm and actual
amplification proved separately. No equivalence between Cauchy fixed fields
and Mayer transfer eigenfunctions is assumed. Local searches found the
source identities and generic analytic/Cayley tools, but not this exact
operator classification.
