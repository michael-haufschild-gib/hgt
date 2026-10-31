# Actual elliptic ideles rotate restricted loops

- **Stage:** 3-formalized
- **Parent:** [Restricted elliptic rotation](degree-rotation-preserves-the-restricted-elliptic-loop-group.md).
- **Statement:** Every idele defines an automorphism of the actual restricted
  central loop group. It preserves positive Borel and fixes its two idele
  coordinates, hence every Borel spectral character.

## Proof

Evaluate the idele in each completed coefficient field and rotate the local
Laurent variable. Outside finitely many finite places, its valuation is one.
The integral-loop rotation theorem therefore preserves the loop's finite
exceptional-place condition. Local multiplicativity assembles into an adelic
homomorphism. The inverse idele gives its inverse at every component.

Local rotation preserves positive Borel, so the componentwise automorphism
restricts to the adelic Borel. Its two local Borel coordinates are unchanged;
componentwise equality of the assembled ideles gives equality of both global
coordinates. Their spectral character is therefore unchanged as well.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticLoopRotation.lean`.
`adelicDegreeRotation` and `adelicBorelCharacter_rotation` passed direct
Lean and transitive axiom audits; only `propext`, `Classical.choice`, and
`Quot.sound` occur.
