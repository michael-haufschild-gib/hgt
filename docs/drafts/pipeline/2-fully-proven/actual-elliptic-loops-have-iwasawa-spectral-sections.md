# Actual elliptic loops have Iwasawa spectral sections

- **Stage:** 2-fully-proven
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** Each pair of complex spectral parameters defines a nonzero
  function on the actual restricted adelic central loop group, invariant under
  left integral loops and equivariant under right positive Borel. Its Borel
  character is trivial on the actual arithmetic Borel.

## Proof

A family of local units with valuation one outside a finite set defines an
actual idele: the family and its pointwise inverse both satisfy the restricted
condition. The two intrinsic Borel torus coordinates give two such families,
by the exact local integral-loop intersection. They define idele-valued
homomorphisms; composing their audited idele characters gives a Borel character.

On the intersection of adelic integral loops and Borel, both valuations are
one at every finite place and at infinity. Every normalized local magnitude,
and hence each global idele magnitude, is one. The spectral character is
therefore one on this intersection.

If `k₁b₁=k₂b₂`, then `b₁b₂⁻¹=k₁⁻¹k₂` lies in the intersection. Thus the
character values of `b₁,b₂` agree. Evaluate the character on any of the proved
actual adelic Iwasawa factors to define the section. The factorizations
`k₀(kb)=(k₀k)b` and `(kb)b₀=k(bb₀)` give its two transformation laws.
A character of a group takes nonzero values.

For an arithmetic adelic Borel element, the faithful infinity field map
reflects Borel membership of its rational preimage. Naturality of the
positive splitting and both torus coordinates identifies its two ideles
with diagonal rational units. The audited curve product formula makes
both spectral characters one.

Continuity and Eisenstein summation remain separate.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticLoopCharacters.lean`:
`adelicIwasawaSection`, `adelicIwasawaSection_left_integral`,
`adelicIwasawaSection_right_borel`, `adelicBorelCharacter_arithmetic`. Direct check pending.
