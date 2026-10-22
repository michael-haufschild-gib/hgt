# Theta-cusp direct fixed-action C5 seam orientation

- **ID:** C5-FA-SEAM-ORIENT-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Lean-corpus chain `ThetaCuspFixedActionC5Jacobian` →
  `ThetaCuspActionVelocitySeamLogMinorNoGo` →
  `PrimeArchThetaModularDifferentialClosure`
- **Statement:** For the literal completed theta source, the velocity-only fixed-action seam minor
  is strictly negative, but the first surviving direct fixed-action C5 seam coefficient
  `A²D - 5ABC + 4B³ - 18A³C + 36A²B²` is strictly positive.

## Goal

Decide whether the negative action-velocity seam obstruction kills the direct fixed-action C5
Jacobian route. It does not: direct Jacobian has an additional cancellation, and its next seam
coefficient has strict forward orientation.

## Gates

- [x] 0 → 1 in-progress: source-pure corpus derivation and RH passport
- [x] 1 → 2 fully-proven: exact modular-ODE elimination, chamber sign, and Bell transfer
- [x] 2 → 3 formalized: targeted module builds and standard-only `#print axioms`
- [ ] 3 → 4 publication-ready: standalone proof and independent external review

## Exact result

Write `L = log(thetaCuspFullSource)` and

`A=-L₂(0), B=-L₄(0), C=-L₆(0), D=-L₈(0)`.

Lean proves

`0 < A²D - 5ABC + 4B³ - 18A³C + 36A²B²`.

The raw source invariant is exactly `thetaCuspFullSource(0)^6` times this log invariant. Universal
modular-ODE elimination identifies the normalized invariant with a degree-twelve polynomial in the
self-dual squared modular scale. That polynomial is strictly positive on the already certified
physical chamber `191/10 ≤ X < 20`.

## Route decision

- **Killed:** velocity-only fixed-action monotonicity. Lean already proves
  `thetaCuspActionVelocitySeamLogMinor < 0`.
- **Survives:** direct C5 Jacobian. Lean now proves its first surviving seam invariant has the
  opposite, required strict sign.
- **New insight:** the velocity obstruction is not functorial under passage to the full direct
  Jacobian; the lower transverse term cancels and eighth-log data decides the germ.

## Full RH proof chain

1. **This card, closed:** strict positive direct fixed-action seam invariant.
2. **Open analytic bridge:** formalize its equality with the first nonzero displacement coefficient
   of the center derivative of `thetaCuspReflectedActionC5FixedActionJacobian`.
3. **Open global transport:** prove the direct Jacobian has nonnegative orientation for every
   physical center/displacement, transporting modular-center C5 to all reflection centers.
4. **Open rank passage:** feed global source C5 into the reflection-odd rank-four/Ptolemy wall;
   `thetaCuspCenterMixedGramFourEquispaced_posSemidef_iff_oddParityWall` and
   `thetaCuspCenterMixedGramFourEquispaced_posSemidef_iff_ptolemy` are existing consumers.
5. **Open cofinal passage:** extend fixed rank-four positivity to arbitrary finite packets and close
   no-escape/cofinal limits.
6. **Existing RH endpoints:** identify resulting universal source positivity with either
   `riemannHypothesis_iff_thetaCuspTiltSource_tiltFlux_nonneg` or
   `riemannHypothesis_iff_xiWeilPolarization_nonneg`.

Steps 2–5 remain genuine proof burdens; this theorem alone does not prove RH.

## Novelty audit

Corpus search found no prior declaration of this direct fixed-action eighth-log invariant or its
sign. Closest external result found by primary-source search was Planat–Solé,
“Second-Level Concavity of the Riemann Ξ Kernel,” arXiv:2608.19160 (19 August 2026), which studies a
different first Laguerre/log-concavity expression and explicitly does not prove RH. No matching
fixed-action C5 Jacobian seam theorem was found in the audited literature.

## Lean certificate

- `GaloisForLFunctions.HTGeometry.PolynomialODEJetC5FixedActionSeamClosure`
  - `modularThetaC5FixedActionSeamJetElimination`
  - `modularThetaC5FixedActionSeamPolynomialReal_pos_of_mem_physicalChamber`
  - chart transport and source-positive closure theorems
- `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFixedActionC5JacobianSeamOrientation`
  - `thetaCuspC5FixedActionSeamLogValue_pos`
  - `thetaCuspC5FixedAction_direct_survives_velocity_seam_noGo`

Both modules are wired into their umbrellas. Targeted builds pass. `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-08-29 — Corpus-derived conjecture; velocity obstruction separated from direct Jacobian.
- 2026-08-29 — Exact ODE elimination, source-positive chart transport, chamber sign, and Bell
  transfer formalized; direct seam route retained.
