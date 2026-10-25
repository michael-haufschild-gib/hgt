# Three phase samples detect chirp nonstationarity

- **ID:** biarithmetic-chirp-phase-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Logarithmic chirp tangents](../1-in-progress/biarithmetic-logarithmic-chirp-tangents.md)
- **Statement:** Equal real parts at three successive rotations by a nonreal unit force the complex amplitude to vanish. The logarithmic-chirp angle `2(log 2)²` is strictly between zero and pi.

The unit norm supplies the second-order recurrence for rotated real parts.
A constant three-term progression forces the amplitude's real part to
vanish; the nonzero imaginary part of the rotation then forces its
imaginary part to vanish. The bounds `0 < log 2 ≤ 1` and `3 < pi` verify
the exact prime-two angle without any logarithmic irrationality premise.

Lean: `BiarithmeticGeometry/ChirpPhaseRigidity.lean`.
Audited declarations: `complex_three_rotation_rigidity`,
`complex_three_rotation_not_constant`, `logarithmicChirp_two_angle`, and
`logarithmicChirp_two_rotation_not_constant`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/ChirpPhaseRigidity.lean`.
- [x] All four transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Default proof limits; umbrella import wired; umbrella not compiled.

This proves the rotation obstruction. The actual source-kernel comparison
and complete source tangent classification require their own checks.
