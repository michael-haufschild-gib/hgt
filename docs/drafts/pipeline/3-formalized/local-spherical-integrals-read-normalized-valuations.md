# Local spherical integrals read normalized valuations

- **Stage:** 3-formalized
- **Parent:** [Actual local Iwasawa kernels](../3-formalized/local-spherical-kernels-read-normalized-iwasawa-magnitudes.md).
- **Statement:** For a locally compact discretely valued field whose valuation
  attains `exp(-1)`, let `Q` be its residue cardinality and `|x|` the normalized
  valuation magnitude. For `Re(s)>0`, `exp(-(s+1) log(max(1,|x|)))` is absolutely
  integrable for normalized additive Haar, with integral
  `(1-Q^(-1) exp(-s log Q))/(1-exp(-s log Q))`.

## Proof

Choose an irreducible integer with valuation `exp(-1)`, using the proved
normalized-uniformizer theorem. Its inverse-power integer ball of radius `n`
is exactly `v(x)≤exp(n)`: multiply by the uniformizer power, write each nonzero
valuation as `exp(m)`, and compare integers. The successive shell therefore
satisfies `max(1,v(x))=exp(n)`; shell zero is the whole integer ring.
The order-preserving exponential normalization gives `max(1,|x|)=Q^n`.

Put `z=exp(-s log Q)`. On shell `n`, the character is `(z/Q)^n`, exactly the
previously audited spherical kernel. Since `Q>1` and `Re(s)>0`, `|z|<1`.
Its audited absolute-integrability theorem and geometric-series integral give
the asserted local factor. No choice of uniformizer remains in that factor.

Actual elliptic finite and infinity valuations attain `exp(-1)` by their
proved uniformizers. Identification with their named magnitudes and their
actual Iwasawa sections remains in the parent task.

## Lean

`HTGeometry/LoopEisenstein/ValuationSpectralKernel.lean`:
`valuationShell_normalizedMagnitude`, `sphericalKernel_eq_valuationSpectralKernel`,
`valuationSpectralKernel_integrable`, `integral_valuationSpectralKernel`.
Direct Lean audit passed. All three transitive axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.
