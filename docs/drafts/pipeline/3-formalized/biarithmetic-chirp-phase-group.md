# The actual logarithmic-chirp phase group

- **ID:** biarithmetic-chirp-phase-group
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Logarithmic chirp tangents](../1-in-progress/biarithmetic-logarithmic-chirp-tangents.md)
- **Statement:** The closure of the simultaneous logarithmic phase flow is a compact topological group. Each phase has value one at the unit cofactor and is completely multiplicative on positive integer cofactors.

The phase flow is a continuous homomorphism from the additive real line
to the product of circles. Its closed subgroup closure is compact. Unit
and multiplicative identities hold on the orbit and define closed sets,
so they extend to its actual closure. No phase identity is postulated.

Lean: `BiarithmeticGeometry/ChirpPhaseGroup.lean`.
Audited declarations: `logarithmicChirpPhaseGroup_carrier`,
`logarithmicChirpPhaseGroup_compactSpace`, `logarithmicChirpPhase_one`,
and `logarithmicChirpPhase_mul`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/ChirpPhaseGroup.lean`.
- [x] All four transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Default proof limits; umbrella import wired; umbrella not compiled.

Integer-horizon realization and source covariance classification remain
separate formalization obligations.
