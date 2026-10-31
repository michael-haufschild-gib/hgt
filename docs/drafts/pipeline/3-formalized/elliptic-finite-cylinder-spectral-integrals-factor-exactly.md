# Elliptic finite-cylinder spectral integrals factor exactly

- **Stage:** 3-formalized
- **Parent:** [Global radial integral](../2-fully-proven/elliptic-radial-kernels-integrate-to-the-global-zeta-ratio.md).
- **Statement:** Assembly maps the local cylinder product measure to actual
  adelic Haar restricted to that cylinder. For `Re(s)>0`, its radial spectral
  kernel is integrable and its integral is the finite product of the exact
  local intertwining factors, including infinity.

## Proof

Assembly is an open measurable embedding with image precisely the adeles
integral outside the chosen finite set. The audited pullback measure identity
and the embedding's map–comap identity identify its pushforward with
restricted ambient Haar. This transports every complex Bochner integral.

Each local spectral kernel is integrable on `Re(s)>0`. Dependent finite-product
Fubini gives integrability of their coordinate product. The unused integral
tail has probability one. Product Fubini with the infinity factor proves
integrability of the entire cylinder kernel and gives the product of local
integrals. Substitute their audited residue-cardinality formulas.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticCylinderIntegrals.lean`:
`ellipticCylinderAssembly_measurePreserving`,
`integral_ellipticCylinderAssembly`,
`ellipticCylinderSpectralKernel_integrable`,
`integral_ellipticCylinderSpectralKernel`. Direct Lean audit passed. All four transitive axiom checks contain only
`propext`, `Classical.choice`, and `Quot.sound`.
