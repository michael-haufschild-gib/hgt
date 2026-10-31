# Actual elliptic local spectral characters have exact integrals

- **Stage:** 3-formalized
- **Parent:** [Actual local Iwasawa kernels](../1-in-progress/local-spherical-kernels-read-normalized-iwasawa-magnitudes.md).
- **Statement:** At every actual finite completion and at infinity, the
  radial character `exp(-(s+1) log(max(1,|x|)))`, using the named adelic
  magnitude, is absolutely integrable for `Re(s)>0`. Its integral is
  `(1-Q^(-1)exp(-s log Q))/(1-exp(-s log Q))`, where `Q` is the actual
  prime residue cardinality and is three at infinity.

## Proof

The dense finite-field embedding sends the actual place uniformizer to an
integer with valuation `exp(-1)`. At infinity, the embedded parameter `x/y`
has the same value. Thus the normalized-uniformizer input of the general
[spectral-kernel theorem](../3-formalized/local-spherical-integrals-read-normalized-valuations.md)
is proved at every actual completion.

The completed residue field is canonically equivalent to the actual finite
prime residue ring, and to `F₃` at infinity. Its cardinality therefore equals
the normalization base in `finiteCompletionMagnitude` or
`infinityCompletionMagnitude`. Equality of bases identifies their valuation
magnitudes and hence the entire radial character. The general integrability
and integral identities transfer, including the exact residue factors.

Identification of these radial characters with the actual Iwasawa section,
and the global product integral, remain in the parent task.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticLocalSpectralIntegrals.lean`:
`finiteCompletionSpectralKernel_integrable`,
`infinityCompletionSpectralKernel_integrable`,
`integral_finiteCompletionSpectralKernel`,
`integral_infinityCompletionSpectralKernel`. Direct Lean and transitive axiom audits passed; only `propext`,
`Classical.choice`, and `Quot.sound` occur.
