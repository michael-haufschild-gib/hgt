# Exact finite pronic covariance as a step integral

- **ID:** biarithmetic-finite-pronic-step-embedding
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Quantitative digital covariance](../1-in-progress/biarithmetic-digital-profile-bounded-covariance-error.md)
- **Statement:** Every finite signed pronic pairing of arbitrary real arithmetic rows equals the Lebesgue pairing of their truncated floor-step functions against `x⁻² dx` on `(1,∞)`.

Truncating each row at the chosen horizon makes it bounded. The existing
step-Gram theorem then applies, and its infinite sum has exactly the
prescribed finite support. No bound or summability premise is imposed on
the original arithmetic rows.

Lean: `BiarithmeticGeometry/FinitePronicStepEmbedding.lean`.
Audited declarations: `finitePronicPairing_eq_stepGram` and
`finitePronicPairing_eq_integral`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/FinitePronicStepEmbedding.lean`.
- [x] Both transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Umbrella import wired; umbrella not compiled.

Scaled annular comparisons and covariance asymptotics remain separate obligations.
