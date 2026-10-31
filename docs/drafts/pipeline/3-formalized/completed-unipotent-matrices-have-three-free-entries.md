# Completed unipotent matrices have three free entries

- **Stage:** 3-formalized
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** The actual completed positive unipotent subgroup of
  `SL₂(F[[X]])` is equivalent to triples `(a,b,c)` with `a(0)=1`,
  arbitrary `b`, and `c(0)=0`. Its fourth entry is `a⁻¹(1+bc)`.

## Proof

The existing unipotent subgroup consists exactly of determinant-one
matrices whose constant reduction is upper unipotent. Thus `a(0)=d(0)=1`
and `c(0)=0`. The power series `a` is a unit because its constant
coefficient is one. Its inverse also has constant coefficient one.
The determinant equation gives the unique value `d=a⁻¹(1+bc)`.

Conversely, any such triple gives determinant one by direct
multiplication. The displayed fourth entry has constant coefficient
one, so the resulting literal matrix belongs to the existing
unipotent subgroup. Reading the three entries and reconstructing the
fourth are inverse operations.

## Lean

`HTGeometry/LoopEisenstein/PositiveUnipotentCoordinates.lean`:
`positiveUnipotentCoordinateEquiv`. Direct Lean check passed; transitive axioms: `propext`, `Classical.choice`,
`Quot.sound`.

This is the coordinate parametrization. Triangular multiplication,
restricted adelic reduction and quotient probability remain separate.
