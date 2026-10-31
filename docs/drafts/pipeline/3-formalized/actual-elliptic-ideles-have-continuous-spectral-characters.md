# Actual elliptic ideles have continuous spectral characters

- **Stage:** 3-formalized
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** The unit group of the actual elliptic adele ring has
  a positive continuous magnitude homomorphism. Every complex power
  of this magnitude is a continuous character trivial on diagonal
  function-field units.

## Proof

An adelic unit and its inverse are integral outside finitely many
finite places. Their local valuations multiply to one, so both are
one there. The normalized local magnitudes consequently have finite
multiplicative support. Their product, including infinity, defines
a multiplicative magnitude. A homomorphism sends units to units,
so this nonnegative real magnitude is strictly positive. The audited
actual completed-place product formula gives magnitude one on every
diagonal field unit.

The ideles for which both the element and its inverse lie in the
integral adelic subring form an open neighborhood of one. Every local
valuation, including infinity, is one on this neighborhood; hence the
magnitude is locally constant there. Multiplicativity gives continuity
everywhere.

For `s∈ℂ`, define `χ_s(a)=exp(s log|a|)`. Positivity makes the real
logarithm continuous and additive under multiplication. Thus `χ_s`
is a continuous, nonvanishing character, and the product formula makes
it trivial on diagonal field units. Products of two such characters
give the corresponding two-coordinate torus character.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticIdeleCharacters.lean`:
`ideleMagnitude`, `ideleMagnitude_diagonal`, `continuous_ideleCharacter`,
`ideleTorusCharacter_diagonal`. Direct Lean check passed; transitive axioms:
`propext`, `Classical.choice`, `Quot.sound`.

This constructs actual idele characters. Independence of the loop
Iwasawa factorization still requires both integral Borel coordinates
to have valuation one.
