# The integral positive vertex has unit Borel coordinates

- **Stage:** 3-formalized
- **Parent:** [Integral loop vertices](../1-in-progress/valued-loop-iwasawa-and-integral-vertices.md).
- **Statement:** Central valuation units times coefficient-integral positive
  determinant-one matrices form an actual subgroup of the central loop group.
  Both intrinsic Borel torus coordinates have valuation one on its intersection
  with the positive Borel.

## Proof

The positive splitting is an injective homomorphism, and central elements
commute with it. Their product therefore defines a homomorphism from
`Fˣ×SL₂(F[[X]])`. Equality of products first gives equality of positive
matrices under projection, then equality of central factors by cancellation.
The image of the product of the two integral subgroups is the required vertex.

Its product `central(c) positive(p)` lies in Borel exactly when `p` is Iwahori:
projection gives this condition, and faithful positive splitting recovers it.
Uniqueness of the central–Iwahori factors identifies the central Borel
coordinate with `c` and the finite coordinate with the upper-left constant
coefficient of `p`. The former is a valuation unit by definition. The two
constant diagonal entries of the integral Iwahori multiply to one and each
has valuation at most one, so both have valuation one.

## Lean

`HTGeometry/LoopEisenstein/IntegralPositiveVertex.lean`:
`LoopSL2.integralPositiveVertex_borel_torus_values`. Direct Lean check passed; transitive axioms are exactly `propext`, `Classical.choice`, `Quot.sound`.
