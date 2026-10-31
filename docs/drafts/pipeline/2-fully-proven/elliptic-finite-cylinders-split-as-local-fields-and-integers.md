# Elliptic finite cylinders split as local fields and integers

- **Stage:** 2-fully-proven
- **Parent:** [Actual Haar products](../1-in-progress/elliptic-adelic-haar-has-exact-finite-cylinder-products.md).
- **Statement:** For every finite set `S` of actual elliptic finite places,
  the finite adeles integral outside `S` form an open additive subgroup,
  additively homeomorphic to the product of the completed fields in `S`
  and the compact product of integer rings outside `S`.

## Proof

Assemble coordinates by choosing the unrestricted field coordinate on `S`
and the integer-ring coordinate off `S`. Only `S` can violate integrality,
so assembly lies in the actual restricted product. Coordinate evaluation
provides its additive inverse map.

Assembly factors through the restricted product for the principal filter
of the complement of `S`. In that topology continuity is exactly continuity
of all coordinate maps. The inclusion into the cofinite restricted product
is continuous. Coordinate evaluation also proves continuity of the inverse.
The cylinder is open because all outside-place integer conditions define
an open subset of the restricted product. The outside integer product is
compact by the audited local compactness and Tychonoff's theorem.

This identifies topology and groups. Haar-product normalization is a
separate assertion.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticFiniteCylinders.lean`:
`finiteAdeleCylinderHomeomorph`, `finiteAdeleCylinder_isOpen`,
`finiteCylinderTail_compact`. Direct audit pending.
