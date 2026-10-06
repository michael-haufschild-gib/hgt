# TT C86 — Speculative cubic kinetic principal

- Stage: 5-failed.
- Type: FALSIFIED candidate formula; TT and its curvature attack remain active.
- Parent: `../1-in-progress/tt-kinetic-contraction-source.md`.

The proposed normalized zero-clock source C*(1-3*z)²*(1+6*z), with
C=6844157203887991842733489140006912, was conjectured from the rank-one first
jets and the first two control leading terms. Those data did not determine
its degree or terminal multiplicity.

Exact second-clock jets and the complete cross-core give the actual source
G(z)=C*(1-9*z²). The audited identity

    G(z)-C*(1-3*z)²*(1+6*z)=18*C*z²*(1-3*z)

is strictly positive throughout0<z<1/3. Thus the candidate equality fails on
an entire interval, without a sampled test or numerical approximation.

Positive survivor: the complete drift-independent quadratic source identity,
positive interior, exact terminal zero and constant strictly negative
curvature. This provides the correct initial polynomial for the full
finite-clock concavity attempt. The anticipated curvature-sign obstruction
from the speculative cubic is withdrawn.

Paper dependencies are closed by the exact moment and defect-field identities.
All28 declarations in `ThetaCuspRatioKineticClockPrincipalJets` and
`ThetaCuspRatioKineticClockPrincipal` passed direct/imported Lean audits with
only standard axioms. Killing theorem: `kineticClockPrincipal_cubic_lt`;
positive source theorem: `compactSlope_clock_zero`. Full evidence and scope:
`../3-formalized/tt-kinetic-clock-principal.md`. No full source sign or RH
proof/falsification is claimed.
