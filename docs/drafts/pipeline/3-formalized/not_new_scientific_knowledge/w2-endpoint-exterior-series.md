# Every arithmetic alternating projection is nonnegative

- **ID:** w2-endpoint-exterior-series
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [W2 representation construction](../../1-in-progress/w2-representation-construction.md)
- **Statement:** For every `n`, the prescribed arithmetic class function satisfies
  `Σ_(σ∈S_n) sign(σ) χ_arith(σ) = E^(n)(0) ≥ 0`, where
  `E(z)=G(1/4+z/M)²/G(1/4)²`, `G=xiCentreLift`, and `M=xiEndpointColorMass`.

## Proof

The theta identity gives `G^(n)(0)=n!·thetaCuspRawEvenMoment(n)/(2n)! ≥ 0`.
Taylor expansion of each derivative propagates nonnegativity along the positive real axis.
Translation by `1/4`, dilation by `1/M`, squaring, and division by the positive squared value
preserve every nonnegative Taylor coefficient. Also `E(0)=E'(0)=1`.

Pair the centered Hadamard products at `s` and `−s`, with `s²=−y`. Their exponentials cancel,
giving `G(y)²/G(0)²=Π_q(1+y/t_q²)`. Divide at `y=1/4+z/M` and `y=1/4` to obtain
`E(z)=Π_q(1+z α_q/M)`. The square retains both functional-equation copies.
Absolute summability of endpoint weights expands this product over finite subsets.
Grouping by cardinality and uniqueness of scalar power-series coefficients give

`E^(n)(0)=n! Σ_(|S|=n) Π_(q∈S)(α_q/M)`.

The complex alphabet `α_q/M` has mass one. Absolute convergence factors its fixed-word
trace over permutation cycles, identifying it with the prescribed arithmetic character.
A repeated letter has a sign-reversing stabilizer transposition; an injective word has trivial
stabilizer. Each `n`-element subset has `n!` orderings. Thus the signed trace is exactly the
same derivative, proving its nonnegativity without any zero-location premise.

## Lean

- `RHTower/Representation/EndpointExteriorSeries.lean`: nonnegative Taylor coefficients and normalization.
- `RHTower/Representation/EndpointExteriorProduct.lean`: exact product, subset expansion, and
  `xiEndpointExteriorCoefficient_eq_deriv`, `xiEndpointExteriorCoefficient_nonneg`.
- `HTGeometry/SymmetricCharacters/ComplexColoring.lean`: `complexWordCharacter_eq_complexCycleCharacter`.
- `HTGeometry/SymmetricCharacters/AlternatingComplexColoring.lean`:
  `sum_sign_complexWordCharacter_eq_subset`; `complexAlternatingMass` is the signed sum.
- `RHTower/Representation/EndpointAlternatingPositivity.lean`:
  `complexWordCharacter_xiEndpoint`, `xiEndpointArithmeticCharacter_alternating_eq`, and
  `xiEndpointArithmeticCharacter_alternating_nonneg`.

All five modules pass direct leaf checks and are umbrella-wired.

## Scope

This identifies a positive arithmetic subfamily using classical product and alternating-trace
identities. Column projections alone do not establish mixed Young projection positivity,
full Gram positivity, or RH.
