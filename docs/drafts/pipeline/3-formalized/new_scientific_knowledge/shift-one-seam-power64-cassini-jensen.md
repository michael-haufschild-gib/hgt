# Shift-one seam power-64 Cassini--Jensen law — formalization certificate

- **ID:** `shift-one-seam-power64-cassini-jensen`
- **Stage:** 3-formalized
- **Paper proof:**
  `other/shift-one-seam-power64-cassini-jensen.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/XiSquaredSeamCassiniGlobalJensenLaw.lean`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Status:** `[UNCONDITIONAL LEAN] [RH-EQUIVALENT CRITERION]`

## Formalized theorem

Lean constructs the even Xi quotient and shifted squared-coordinate entire source, preserves the
zero-divisor multiplicity pairing, proves the exponent-64 atom integral and Tonelli divisor sum,
identifies the Cassini--Jensen integral with the Hermitian power-64 mass, identifies its residual
with the nonnegative transverse charge, and proves residual vanishing and the source dominance
criterion equivalent to the Riemann hypothesis.

## Capstones

```text
xiSquaredSeamCassiniSourceKernel_tsum_eq_jensenExcess
xiSquaredSeamPowerSixtyFourJensenDivisorIntegral_eq_two_mul_cassiniIntegral
xiSquaredSeamCassiniPowerSixtyFourJensenIntegral_eq_hermitianMass
xiSquaredSeamPowerThirtyTwoTransverseCharge_eq_cassiniJensenResidual
cassiniJensenResidual_nonneg
cassiniJensenResidual_eq_zero_iff_riemannHypothesis
xiSquaredSeamCassiniJensenDominated_iff_riemannHypothesis
```

## Verification and boundary

Serialized direct checks and the `RHTower` umbrella build pass.  Combined scratch
`#print axioms` audits use only `propext`, `Classical.choice`, and `Quot.sound`.  Lean proves the
identity and equivalence unconditionally; it does not prove the RH-equivalent source inequality.
That Euler--Gamma inequality and RH remain consumers, not hidden assumptions.
