# HB isolated unit-amplitude nonlinear covariance no-go (2026-08-31)

New Lean module:
- formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMIsolatedUnitAmplitudeCovarianceInterpolationNoGo.lean
- imported by formal/GaloisForLFunctions/RHTower.lean

Result:
- For every overtone n and real clock time t, define a finite-support-preserving coordinatewise polynomial evolution
  E(x)_q = m_q x_q + x_q^2 (x_q - 1) K_q,
  where K_q interpolates the reflected clock defect at the literal source-cocycle amplitude.
- E has the centered Birmingham–Mokhtari clock as its coefficientwise real-amplitude vacuum first variation.
- E is exactly source-FE covariant on every canonical unit Xi basis packet, unconditionally, including tilted fibres.
- At nonzero time, full finite-packet covariance of this same E is equivalent to RH.

Route kill:
- d4HBIsolatedUnitAmplitudeNonlinearEvolutionRouteKilled
- Universal isolated unit-amplitude/source-specific covariance cannot be the missing HB producer: it is freely polynomially interpolable without changing the vacuum jet.
- Exact survivor: covariance on an amplitude family accumulating at vacuum/full packet space, or a physical coefficient law excluding interpolation. Other survivors change the clock/source law or are vacuum-singular.

Verification:
- lake env lean direct module check passed.
- targeted lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMIsolatedUnitAmplitudeCovarianceInterpolationNoGo passed.
- axiom audit for five main theorems: only propext, Classical.choice, Quot.sound.
- formal_tools lint sees module through umbrella; only unrelated pre-existing unreachable HTGeometry.AutonomousExponentDichotomy and HTGeometry.RittLevelThreeHomogeneous errors.
- temporary scratch files removed; no own Lean process left.

Cards:
- docs/drafts/pipeline/3-formalized/hb-isolated-unit-amplitude-covariance-interpolation-no-go.md
- docs/drafts/pipeline/5-failed/hb-isolated-unit-amplitude-nonlinear-covariance.md

Frontier map was read only and not edited.