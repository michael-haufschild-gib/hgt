# Finite elliptic unipotent prefixes are uniformly integral

- **Stage:** 2-fully-proven
- **Parent:** [Arithmetic cell coordinates](../1-in-progress/affine-a1-bruhat-cells-have-one-polynomial-root-coordinate.md).
- **Statement:** Every finite adelic free-coefficient prefix completed by
  zeros is uniformly integral. Every rational prefix belongs to the actual
  uniformly integral rational unipotent subgroup.

## Proof

Each adele is integral outside finitely many places. Intersecting the
cofinite sets for a finite prefix gives a common set of integral places.
All later free coefficients vanish, hence are integral there. The audited
stream criterion gives uniform integrality. Prefix completion commutes
with the diagonal function-field embedding, proving the rational claim.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticUnipotentFinitePrefixes.lean`:
`unipotentPrefixCompletion_mem_uniformlyIntegral` and
`unipotentPrefixCompletion_mem_uniformlyIntegralRational`. Direct audit pending.
