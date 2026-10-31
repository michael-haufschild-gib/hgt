# A volume-one simple-pole domain for the elliptic adeles

- **ID:** elliptic-adeles-have-a-volume-one-simple-pole-domain
- **Stage:** 3-formalized
- **Statement:** For `K=F₃(x,y)`, `y²=x³−x`, the simple-pole domain
  `D=(∏finite O_v)×(F₃(x/y)⁻¹+m∞)` is compact and open, has ambient
  additive Haar measure one, and maps homeomorphically onto `A_K/K`.
  Restriction to `D` induces an additive Haar probability measure on the quotient.

## Proof

The maximal ideal `m∞={v∞<1}` is open and closed, and is a closed subset
of the compact infinity integers. The infinity factor of `D` is the union
of its three translates by `c(x/y)⁻¹`, `c∈F₃`. Thus `D` is compact and open.

Put `B=(∏finite O_v)×m∞`. Both `D` and the full integral product are
disjoint unions of three translates of `B`: use simple-pole coefficients
for `D` and constant residues for the integral product. Distinct coefficients
cannot differ by `m∞`, since their values are respectively `exp(1)` and `1`.
Translation invariance equates the two volumes. The integral product has
the defining Haar normalization one, so `D` has volume one.

The unique additive gap representative proves that `D→A_K/K` is a bijective
additive homomorphism. It is continuous, and open because both the inclusion
of the open subgroup and the quotient map are open. Hence it is a
homeomorphism. Pulling ambient Haar measure back to the open subgroup gives
Haar measure of total mass one; pushing it through this isomorphism gives
the asserted quotient Haar probability measure.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticQuotientHaar.lean`:
`adeleHaar_ellipticAdditiveDomain`, `additiveQuotientHomeomorph`,
`additiveQuotientHaar_isAddHaar`, and `additiveQuotientHaar_isProbability`
passed direct `lake --old env lean` and transitive axiom audits.
Only `propext`, `Classical.choice`, and `Quot.sound` occur.
