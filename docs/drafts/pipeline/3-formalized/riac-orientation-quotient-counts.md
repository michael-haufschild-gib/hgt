# Actual orientation quotient counts

- **ID:** RIAC-orientation-quotient-counts
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Curve orientation counts](riac-curve-orientation-square-root.md)
- **Statement:** The signed transporter mass is the difference of two independently defined arithmetic orbit counts.

For a finite group acting on a finite set `X`, a character `χ:G→{±1}`
acts on `X×{±1}` by `g·(x,u)=(g·x,χ(g)u)`. An equivariant arithmetic
map `φ` acts as `(x,u)↦(φ(x),u)`. Let `A` and `B` count its stable
orbits in the oriented and ordinary sets respectively. Then

`|G|(A−B)=Σ_x Σ_{g·x=φ(x)} χ(g)`.

Equivalently, `A−B` is the sum of the existing normalized local orientation
weights. The counts retain stabilizers. They also retain both orientation
labels when the character is trivial; no surjectivity assumption is needed.

For each `g`, the oriented twist is the product of its ordinary twist and
`{u:χ(g)u=u}`. The second set has cardinality `1+χ(g)`. Subtracting the
two twisted Burnside identities proves the formula.

[OrientationQuotientCounts.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/OrientationQuotientCounts.lean):
`orientationTwistEquiv`, `orientationTwist_card`,
`orientationFixedOrbitCount_mul`, `orientationFixedOrbitCount_sub_eq_sum`.
Direct Lean check passed; all three theorem audits use only
`propext`, `Classical.choice`, `Quot.sound`.

This is a count realization, not a cancellation estimate. The arithmetic
curve comparison and the integer conductor-height bound remain separate.
