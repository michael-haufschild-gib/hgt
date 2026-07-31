# L-bit support temporal-scale law

- **ID:** `lbit-support-temporal-scale-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Date:** 2026-07-30
- **Formal source:**
  `formal/GaloisForLFunctions/HTGeometry/LBitSupportTemporalScaleLaw.lean`

## Exact law

Every nonempty l-bit support \(S\) defines a balanced integer Walsh
character on the complete Boolean configuration spectrum. For every
coefficient family \(J\),

\[
  \Delta_S=
  \sum_x k_S(x)E_J(x)=2^{|I|}J_S.
\]

For the exactly scaled family
\[
  J_S(g)=g^{w(S)}J_S,
\]
the actual centered finite-time Fourier response is
\[
  W_S(g,A)=
  \operatorname{sinc}
  \left(A\,2^{|I|}g^{w(S)}J_S\right).
\]
At the inverse-power birth horizon \(A=\tau g^{-w(S)}\),
\[
  \boxed{
  W_S(g,\tau g^{-w(S)})=
  \operatorname{sinc}(\tau\,2^{|I|}J_S)}
\]
for every \(g\ne0\). If \(J_S\ne0\), then along \(g\downarrow0\) the
response converges to one below the birth horizon, to the displayed sinc
profile at birth, and to zero beyond birth.

## Formal declarations

- `lbitSupportIntegerCharacter_balanced`;
- `lbitSupportIntegerCharacter_detuning`;
- `scaledLBitSupportDetuning_eq`;
- `scaledLBitSupportDetuning_abs_hasPositiveBirthProfile`;
- `lbitSupport_scaled_finitePhaseResponse`;
- `lbitSupport_scaled_finitePhaseResponse_birth_exact`;
- `lbitSupport_scaledReporter_wallCrossing`;
- `lbitSupport_scaled_finitePhaseResponse_wallCrossing`.

## Scope

The horizon is genuine elapsed time in the ideal centered phase-sampling
law, but the Hamiltonian family is exactly diagonal and monomially scaled.
The integer character acts on the complete configuration cube, so this is
not a scalable support-local measurement protocol. No claim is made about
finite-device noise, general analytic remainders, or a microscopic
Anderson/MBL transfer.

## Verification

Direct target compilation passed:

```text
lake env lean GaloisForLFunctions/HTGeometry/LBitSupportTemporalScaleLaw.lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/LBitSupportTemporalScaleLaw.olean
```

Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
Final `lake build` audit is reserved for publication audit.
