# Elliptic domain and rational sampling gives adelic Haar

- **Stage:** 3-formalized
- **Parent:** [Triangular root coefficients](../1-in-progress/triangular-root-coefficients-unfold-arithmetic-cells.md).
- **Statement:** The actual adele ring is second countable, with jointly
  measurable addition. The map `(d,z)↦d+z` from the additive domain times
  the actual function field preserves domain Haar probability times
  counting measure onto ambient adelic Haar.

## Proof

There are countably many finite places and therefore countably many finite
place sets. Each corresponding open cylinder is a countable product of
second-countable local fields and integral rings. These cylinders cover the
finite adeles. The countable-open-cover theorem, then the infinity factor,
give second countability and joint Borel measurability of addition.

The sampler is measurable because each fixed rational translate of the
domain inclusion is continuous and the function field is countable. For
any nonnegative measurable function, Tonelli converts its sampler integral
into the integral over the domain of the sum of all rational translates.
The audited scalar periodization formula identifies this with the ambient
Haar integral. Equality of these integrals determines the pushforward measure.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticAdditiveSampling.lean`:
`ellipticFiniteAdeles_secondCountable`, `ellipticAdeles_measurableAdd₂`, and
`ellipticAdditiveSampler_measurePreserving`. Direct Lean audit passed;
all three declarations depend only on `propext`, `Classical.choice`,
and `Quot.sound`.
