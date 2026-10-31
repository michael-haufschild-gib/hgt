# Elliptic additive reduction preserves integral places

- **Stage:** 3-formalized
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** The actual elliptic adele additive group splits as the diagonal
  function field times its compact simple-pole domain. Projection to the domain
  is continuous and additive. Rational reduction introduces no new finite
  nonintegral places.

## Proof

The audited additive quotient homeomorphism identifies the compact domain
`D` with `A/K`. Composing its inverse with the quotient map gives a continuous
additive retraction `ρ:A→D`, equal to the identity on `D` and zero on diagonal
field elements. Unique additive-domain reduction gives the rational coordinate
`q(a)` with `a−q(a)∈D`. Uniqueness and additivity of `D` give
`q(a+b)=q(a)+q(b)`. Applying `ρ` to the remainder yields
`a=q(a)+ρ(a)`, and these coordinates invert `(z,d)↦z+d`.

At every finite place, every element of `D` is integral. If the component
of `a` is integral, the component of `q(a)=a−ρ(a)` is a difference of
integral elements and is integral. This holds at each place separately,
so a uniform finite exceptional set is preserved through coefficient reduction.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticAdditiveSplitting.lean`:
`continuous_adeleGapProjection`, `adeleAdditiveSplitting`,
`adeleRationalProjection_integral_at`. Direct Lean check passed; transitive axioms are exactly `propext`, `Classical.choice`, `Quot.sound`.
