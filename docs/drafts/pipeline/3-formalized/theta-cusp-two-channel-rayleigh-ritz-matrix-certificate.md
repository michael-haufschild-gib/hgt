# Theta-cusp two-channel Rayleigh--Ritz matrix certificate

- **ID:** theta-cusp-two-channel-rayleigh-ritz-matrix-certificate
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Fernández, nonorthogonal-basis Rayleigh--Ritz generalized eigenvalue principle, arXiv:2405.10340; formal theta-cusp two-channel score family
- **Statement:** Positive definiteness of the two-channel score-energy matrix converts the existential Stein certificate into one explicit adjugate-response determinant inequality.

## Goal

Eliminate the existential choice of generator coefficients from `ThetaCuspFirstRadialTwoChannelSteinEnergyCertificate`.  The replacement must expose only the two diagonal score energies, their mixed energy, and the two finite response moments, then feed the existing first-radial, linear Hankel, and degree-two-tail RH consumers.

## Gates

- [x] 0 → 1 in-progress: exact Rayleigh--Ritz adjugate witness identified
- [x] 1 → 2 fully-proven: energy matrix strict positivity and source matrix implication closed
- [x] 2 → 3 formalized: Lean modules build, standard axioms only, formal lint passes
- [ ] 3 → 4 publication-ready: standalone theorem, physics provenance, and Lean certificate

## Approach

For energy matrix `[[A,B],[B,D]]` and response vector `(c1,c2)`, use the adjugate witness

```text
a = D*c1-B*c2,
b = A*c2-B*c1.
```

Writing `Delta=A*D-B^2` and `Q=D*c1^2-2*B*c1*c2+A*c2^2`, its response is `Q` and its energy is `Delta*Q`.  Thus `Delta>0`, `Q>0`, and `kappa*Delta <= lambda*Q` imply the existential Rayleigh certificate.  For the theta source, prove strict positivity of every nonzero two-channel score by its right-endpoint limit and one explicit interior value.

## Formal result

`HTGeometry.exists_positive_twoChannelRayleighWitness_of_adjugate` proves the reusable adjugate-witness implication.  `RHTower.thetaCuspFirstRadialTwoChannelSteinEnergy_eq_quadratic` identifies the source energy with its `2×2` quadratic form.  `RHTower.thetaCuspFirstRadialTwoChannelSteinEnergy_pos` proves strict energy positivity for every nonzero coefficient pair from the right-endpoint score limit and one exact interior sign.  Consequently, `RHTower.thetaCuspFirstRadialTwoChannelSteinEnergy_det_pos` proves the score-energy determinant is positive, while `RHTower.thetaCuspFirstRadialTwoChannelSteinAdjugateResponse_pos` proves the response quadratic form is positive without additional hypotheses.

`HTGeometry.twoChannelRayleighMatrixCertificate_of_positiveWitness` proves the reverse generalized Cauchy--Schwarz bound.  Consequently, `RHTower.thetaCuspFirstRadialTwoChannelRayleighRitzCertificate_iff` shows that the explicit determinant-response inequality is exactly equivalent to the former existential certificate, not merely sufficient.  `RHTower.thetaCusp_firstRadial_upper_of_twoChannelRayleighRitzCertificate`, `RHTower.forall_primeArchSourceTraceHankel_linear_nonneg_of_twoChannelRayleighRitz`, and `RHTower.riemannHypothesis_of_twoChannelRayleighRitz_of_primeArchDegreeTwoTail` wire it through the first-radial, linear Hankel, and RH interfaces.

## Remaining research target

Prove the single explicit scalar inequality `ThetaCuspFirstRadialTwoChannelRayleighRitzCertificate`.  Strict positive-definiteness of the energy matrix, positivity of its adjugate response, and the existential generator choice are discharged.
