# Unipotent free coordinates work over every commutative ring

- **Stage:** 3-formalized
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** Over every commutative coefficient ring, positive determinant-one
  matrices with upper-unipotent constant reduction are parametrized by three
  arbitrary entries `a,b,c`, subject only to `a(0)=1` and `c(0)=0`.

## Proof

Reduction is a group homomorphism, so the inverse image of the upper root
subgroup is an actual subgroup. Its entry conditions are
`a(0)=d(0)=1` and `c(0)=0`. A power series with constant coefficient one
is a unit over every commutative ring. Hence the determinant condition
forces `d=a⁻¹(1+bc)`. Conversely this formula has determinant one and
constant coefficient one, and produces a matrix in the stated subgroup.
Reading the other three entries and constructing this matrix are inverse
operations. Cancellation uses the unit `a`; no division in the coefficient
ring and no field hypothesis is required.

Over the adele ring, this gives the algebraic coordinate model before
imposing uniform finite-place integrality.

## Lean

`HTGeometry/LoopEisenstein/UnipotentCoefficientGroup.lean`:
`unipotentCoefficientEquiv`. Direct Lean check passed; transitive axioms are exactly `propext`, `Classical.choice`, `Quot.sound`.
