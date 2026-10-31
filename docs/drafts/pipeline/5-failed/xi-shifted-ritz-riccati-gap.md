# Shifted Xi Ritz Riccati gap

- **Stage:** 5-failed
- **Disposition:** Retired as an existing motion constraint, not a false conjecture.

The proposed inequality `lambda' + lambda² < 0` is already the reciprocal hard-root
speed law. `xiShiftedCanonicalAdmissionHardEdgeWorldlineVelocity_pos` proves
`0 < -xdot / x² - 1` for every nonzero local admission root in a positive chamber.
`xiShiftedMomentHankelMatrix_posDef_of_riemannHypothesis` supplies that chamber under RH.
Changing root coordinates to a generalized eigenvalue does not add a distinct endpoint.

The stronger positive survivor is already formalized:
`xiShiftedCanonicalAdmissionHardEdgeWorldline_mul_normalizedTerminalMass` proves
`hardSpeed * normalizedTerminalMass = 2 n y x²`, and
`xiShiftedCanonicalAdmissionHardEdgeNormalizedTerminalMass_pos` proves strict mass positivity.
The source proof differentiates the canonical admission and uses finite confluent
Christoffel–Darboux. No new Lean wrapper is added.
