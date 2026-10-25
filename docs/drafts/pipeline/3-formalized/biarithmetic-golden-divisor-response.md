# Exact golden divisor-response profiles

- **ID:** biarithmetic-golden-divisor-response
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Golden divisor positivity](../1-in-progress/biarithmetic-golden-divisor-positivity-phase.md)
- **Statement:** The actual golden source's ordinary divisor response at every positive integer depends exactly on its five-adic valuation. Every profile value occurs at a power of five. For nonnegative damping, the profile decreases in both valuation and damping and every response is at most one.

Only powers of five contribute to the source. Enumerating those divisors
gives `1-(1/sqrt(5)) Σᵣ₌₀ᴹ ((αt)^r-(βt)^r)`. Positivity and order of the
two roots give both monotonicity laws. The response at zero is zero by the
natural divisor-set convention.

Lean: `BiarithmeticGeometry/GoldenDivisorResponse.lean`.
Audited declarations: `goldenDivisorResponse_eq_profile`,
`goldenDivisorResponse_pow`, `goldenDivisorProfile_antitone`,
`goldenDivisorProfile_parameter_antitone`, and `goldenDivisorResponse_le_one`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/GoldenDivisorResponse.lean`.
- [x] All five transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Umbrella import wired; umbrella not compiled.

The exact positivity chamber and range endpoints remain separate Lean obligations.
