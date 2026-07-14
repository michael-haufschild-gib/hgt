# Theta-cusp two-channel polarized hypervirial certificate

- **ID:** theta-cusp-two-channel-polarized-hypervirial-certificate
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / PHYSICS VALUE BRIDGE
- **Physics source:** generalized quantum virial identities and anomalous half-line quantum bootstraps
- **Lean consumers:** the theta-cusp two-channel Rayleigh--Ritz certificate, first-radial moment bound, prime--archimedean Hankel positivity, and the degree-two-tail RH interface

## Goal

Replace every score-product entry of the strict two-channel Rayleigh matrix by its exact polarized curvature/field-gradient value.  The resulting certificate must be equivalent to `ThetaCuspFirstRadialTwoChannelRayleighRitzCertificate`, so no new hypothesis is introduced.

## Physics value relation

For a half-line ground-state density `rho` with `rho'=-2*W*rho` and differentiable vector fields `P,Q`, write

```text
S_P=P*W-P'/2,
S_Q=Q*W-Q'/2.
```

Then the polarized local hypervirial identity is

```text
S_P*S_Q*rho
  = (P*Q*W'/2 + P'*Q'/4)*rho
      - (P*Q*W*rho)'/2.
```

On the theta radial half-line, the endpoint current vanishes for the fields `P_1(x)=x` and `P_2(x)=x^2`.  Hence the score-energy matrix is exactly

```text
A = integral (x^2*W'/2 + 1/4)*rho,
B = integral (x^3*W'/2 + x/2)*rho,
D = integral (x^4*W'/2 + x^2)*rho.
```

This is the off-diagonal polarization of the already-formalized one-field local virial theorem.  It removes every squared rational superpotential from the determinant and adjugate response.

## Gates

- [x] live formal and failed-route corpus checked
- [x] primary physics mechanism and half-line anomaly identified
- [x] exact RH-facing consumer identified
- [x] generic polarized local hypervirial identity formalized
- [x] all three theta score-energy entries rewritten
- [x] virial matrix certificate proved equivalent to the Rayleigh--Ritz certificate
- [x] strict determinant and adjugate-response positivity transported
- [x] first-radial, linear-Hankel, and RH-facing consumers exposed
- [x] targeted Lean build and axiom audit
- [x] formal lint and index refresh
- [ ] RH

## Verification boundary

The physics literature supplies the generalized commutator/hypervirial mechanism.  The polarized algebra, theta endpoint currents, integrability, source specialization, and certificate equivalence must be proved directly in Lean.  No numerical evidence is used.

Primary sources: C. V. Sukumar, *Generalised Virial theorems in Classical and Quantum Physics*, arXiv:1410.5592; D. Berenstein and G. Hulsey, *Anomalous Bootstrap on the Half Line*, arXiv:2206.01765.

## Lean surface

- `HTGeometry.integral_Ioi_halfLineSteinScore_mul_eq_virial`
- `RHTower.thetaCuspFirstRadialTwoChannelSteinPairing_eq_virialPairing`
- `RHTower.thetaCuspFirstRadialDilationSteinEnergy_eq_virialEnergy`
- `RHTower.thetaCuspFirstRadialTwoChannelSteinCrossEnergy_eq_virialCrossEnergy`
- `RHTower.thetaCuspFirstRadialQuadraticMonomialSteinEnergy_eq_virialEnergy`
- `RHTower.thetaCuspFirstRadialTwoChannelVirialEnergyDet_pos`
- `RHTower.thetaCuspFirstRadialTwoChannelVirialAdjugateResponse_pos`
- `RHTower.thetaCuspFirstRadialTwoChannelVirialRayleighRitzCertificate_iff`
- `RHTower.riemannHypothesis_of_twoChannelVirialRayleighRitz_of_primeArchDegreeTwoTail`

## Corpus effect

The missing mixed entry is now an exact curvature/field-gradient value.  The complete two-channel matrix, its determinant, and its adjugate response contain no squared rational superpotential.  Existing Rayleigh--Ritz consumers accept the new certificate by an equivalence theorem, so this is a direct replacement rather than an additional hypothesis.

## Open core

Prove the single explicit virial Rayleigh--Ritz scalar inequality.  The remaining terms are curvature moments, polynomial field gradients, radial power moments, and source couplings; boundary-current and rational-superpotential hypotheses have been discharged.
