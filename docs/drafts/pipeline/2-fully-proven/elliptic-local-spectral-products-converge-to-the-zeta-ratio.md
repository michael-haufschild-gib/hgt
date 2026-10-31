# Elliptic local spectral products converge to the zeta ratio

- **Stage:** 2-fully-proven
- **Parent:** [Global radial integral](../1-in-progress/elliptic-radial-kernels-integrate-to-the-global-zeta-ratio.md).
- **Statement:** For `Re(s)>1`, unordered finite products of the actual
  normalized local spectral integrals, including infinity, converge to
  `ζ_K(u)/ζ_K(u/3)`, where `u=exp(-s log 3)`.

## Proof

The actual finite residue cardinality is `3^d`, where `d` is the corresponding
closed-point degree. Hence `exp(-s log(3^d))=u^d`, and the local Haar factor is
`(1-(u/3)^d)/(1-u^d)`.

The condition `Re(s)>1` gives `|u|<1/3`. The audited affine Euler products at
`u` and `u/3` converge respectively to `(1-u)ζ_K(u)` and
`(1-u/3)ζ_K(u/3)`. The second limit is nonzero, so their quotient is the
unordered product of the local spectral factors. Reindex through the audited
bijection between actual finite adelic places and affine closed places.
Multiplication by the degree-one infinity factor `(1-u/3)/(1-u)` cancels
the missing factors and gives the complete zeta ratio.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticSpectralProduct.lean`:
`hasProd_elliptic_affine_intertwining_factors`,
`ellipticFiniteSpectralFactor_eq_affine`,
`tendsto_ellipticSpectralCylinderProduct`. Direct audit pending.
