# Actual elliptic simple-root integrals are zeta ratios

- **Stage:** 3-formalized
- **Parent:** [Local Iwasawa kernels](../3-formalized/local-spherical-kernels-read-normalized-iwasawa-magnitudes.md).
- **Statement:** The actual finite and affine negative-root sections equal
  `exp(t H(a))` and `exp((s-t) H(a))`. After spectral normalization, both
  are absolutely integrable for `Re(z)>1` and integrate to
  `ζ_K(3^(-z))/ζ_K(3^(-z-1))`.

## Proof

An idele has unit valuation outside finitely many finite places. Taking
logarithms of its magnitude therefore gives the sum of the local logarithms,
including infinity. Substitute the actual simple-root Iwasawa pairs
`(1,M_v)` and `(M_v,M_v⁻¹)` into the two Borel characters. Their logarithms
are respectively `(0,H(a))` and `(H(a),-H(a))`.

For the finite root set `t=-(z+1)`; for the affine root set `s=t-(z+1)`.
Both sections become the independently defined adelic radial kernel.
Its audited global integrability and integral give the claims.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticSimpleRootIntegrals.lean`:
`integral_adelicIwasawaSection_finiteNegativeRoot` and
`integral_adelicIwasawaSection_affineNegativeRoot`. Direct Lean and transitive axiom audits passed.
Only `propext`, `Classical.choice`, and `Quot.sound` occur.
