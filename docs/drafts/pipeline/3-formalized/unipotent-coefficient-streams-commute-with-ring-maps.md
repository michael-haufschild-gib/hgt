# Unipotent coefficient streams commute with ring maps

- **Stage:** 3-formalized
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** Every homomorphism of commutative rings acts entrywise on the
  actual unipotent coefficient group and coefficientwise on its unrestricted
  stream. An injective ring map gives an injective group map.

## Proof

Entrywise power-series mapping preserves determinant one. It sends the three
constant-entry conditions `a₀=1,c₀=0,d₀=1` to the same conditions. Hence it
restricts to a group homomorphism. The stream reads only coefficients of the
three free entries, and coefficient extraction commutes with ring mapping.
Injectivity follows entrywise from injectivity on every coefficient.
Applying the stream bijection proves the corresponding law for decoding a
mapped stream into a matrix.

## Lean

`HTGeometry/LoopEisenstein/UnipotentCoefficientMap.lean`:
`unipotentCoefficientMap`, `unipotentCoefficientMap_injective`,
`unipotentStream_map`, `unipotentCoefficientMap_stream_symm`.
Direct `lake --old env lean` check passed. Both transitive axiom audits
contain only `propext`, `Classical.choice`, and `Quot.sound`.
