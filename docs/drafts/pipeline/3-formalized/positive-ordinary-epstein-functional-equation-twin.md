# A positive ordinary Dirichlet twin from a rectangular lattice

- **ID:** positive-ordinary-epstein-functional-equation-twin
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Γ15; positivity-constrained functional-equation twins.
- **Statement:** The normalized representation series
  `D(s)=½Σ_(m,n)≠0 (m²+64n²)⁻ˢ` has nonnegative ordinary Dirichlet coefficients,
  coefficient `a(1)=1`, absolute convergence on `Re s>1`, a self-dual completion
  `F(s)=(8/π)ˢ Γ(s)D(s)` with simple poles at `0,1`, and a real zero in `(½,1)`.
  It belongs to the extended Selberg class, has degree two and conductor `256`,
  and satisfies every Ramanujan power bound. Its coefficients are not multiplicative.

## Proof

`LatticeSectionTheory.epsteinLambda_eight_has_offLine_zero` supplies the zero.
`hasSum_epsteinLambda` supplies the lattice-indexed Dirichlet representation and
`epsteinLambda_one_sub` the paired functional equation.

Group lattice points by `m²+64n²`; each fiber is finite. Half its cardinality is
nonnegative and its first value is one. The fibers at `5` and `13` are empty,
whereas `(1,1)` represents `65`, obstructing multiplicativity at a coprime pair.
Swapping lattice coordinates gives
`Λ_(1/8)(s)=8^(2s)Λ_8(s)`, hence `F(s)=8ˢΛ_8(s)/2` is reflection-even.

## Coefficient and growth bounds

The Gaussian norm fiber contains the rectangular fiber. Jacobi's two-square
formula therefore gives `0 ≤ a(n) ≤ 2d(n)`. The divisor bound gives
`a(n) ≤ 2C_ε n^ε` for every `ε>0`. Grouping the absolutely convergent lattice
series by its norm produces the ordinary Dirichlet series on `Re s>1`.

Write `P=rectFEPair 8` and
`R(s)=8ˢ/2 · [s(s−1)P.Λ₀(s)−(s−1)+s/8]`.
Then `R(s)=s(s−1)F(s)` away from `0,1`, and `R(0)=R(1)=1/2`.
Both theta kernels have exponential tails. Monotonicity bounds the remaining
interval starting at one, so `mellin_orderOneEnvelope_of_decay` gives an
order-one envelope for `P.Λ₀`. Polynomial and exponential multiplication give
the same envelope for `R`.

The ordinary regularization is
`H(s)=(π/8)ˢ Γ(s+1)⁻¹ R(s)=(s−1)D(s)` on `Re s>1`.
Reciprocal Gamma is entire with an order-one envelope. Thus `H` is entire of
finite order; `H(1)=π/16`, so `D` has a simple pole at one.

Coordinate interchange gives `Λ_(1/8)(s)=64ˢΛ_8(s)` on `Re s>1`.
The paired functional equation then gives `R(1−s)=R(s)` there; the identity
theorem extends this equality to the plane. Real coefficients give Schwarz
reflection, first on the Dirichlet half-plane and then by analytic continuation.
Hence the scalar Selberg functional equation has `Q=8/π`, one Gamma factor
`Γ(s)`, and root number one: degree two, conductor `256`.

The existing real zero `σ∈(1/2,1)` of `Λ_8` is also a zero of `D`, since the
Gamma and exponential factors are nonzero there. The obstruction at `5·13`
excludes coefficient multiplicativity.

## Lean certificate

Namespace: `GaloisForLFunctions.SelbergClass.PositiveEpstein`.

- `exists_positive_ramanujan_counterexample`: unconditional normalized,
  nonnegative Ramanujan member of `RHTower.ExtendedSelbergClass`, with
  nonmultiplicative coefficients and a real zero in `(1/2,1)`.
- `extendedClass_conductor`: conductor `256`.
- `numerator_one_sub`, `numerator_zero`, `numerator_one`: reflection and the
  exact pole-cleared endpoint values.
- `orderOneEnvelope_regularized`, `regularized_one`: entire order-one envelope
  and residue numerator `H(1)=π/16`.

Leaf: `formal/GaloisForLFunctions/SelbergClass/PositiveEpsteinCompletion.lean`;
coefficient and growth proofs are in its two sibling imports. Wired into
`SelbergClass.lean`.

The leaf passed `lake --old env lean`. The counterexample and conductor
axiom audits contain only `[propext, Classical.choice, Quot.sound]`.

## Selection boundary

Nonnegative counting coefficients and Ramanujan bounds do not repair selection
by the functional equation. The positive arithmetic content is the exact
ordinary norm-fiber decomposition, its divisor bound, and its finite-order
continuation. The Euler-product-constrained case of Γ15 remains open.
