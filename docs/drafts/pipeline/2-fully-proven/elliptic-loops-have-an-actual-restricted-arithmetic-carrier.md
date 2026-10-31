# Elliptic loops have an actual restricted arithmetic carrier

- **Stage:** 2-fully-proven
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** The actual elliptic local central loop groups have a restricted
  adelic group and a faithfully embedded arithmetic subgroup. Every adelic loop
  admits integral–Borel factors in this carrier. Both Borel torus coordinates
  have valuation one outside a finite set of places.

## Proof

At each finite completion use the coefficient-integral completed subgroup
`K_v`; form its restricted product and include the infinity component.
The rational arithmetic domain consists exactly of completed rational loops
whose diagonal local images belong to `K_v` at all but finitely many places.
This is a subgroup because every local coefficient-field map is a homomorphism.
The resulting adelic map is injective already at infinity, by the audited
injectivity of the central coefficient-field map. Its image is the arithmetic
subgroup; no unrestricted rational completed loop is assumed admissible.

Define adelic integral and positive-Borel subgroups componentwise. For a Borel
element, the audited local intersection theorem makes both torus valuations
one at every place where the element is integral, hence almost everywhere.

For Iwasawa existence, choose local `K_v B_v` factors. At each integral finite
component `g_v`, choose specifically `k_v=g_v,b_v=1`. The integral family is
restricted everywhere, and the Borel family is identity outside the finite
exceptional set of the original loop. Together with the infinity factors,
these are actual adelic factors whose product is the original element.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticLoopCarrier.lean`:
`arithmeticLoopEmbedding_injective`, `adelicBorel_torus_eventually_integral`,
`exists_adelic_integral_borel`. Direct check pending.
