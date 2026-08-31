# ULF-TAFM-21 lower-triangular clock representation

Paper:
docs/drafts/pipeline/2-fully-proven/universal-law-field/topologically-admitted-formation-mechanics/lower-triangular-observer-clock-transport-anomaly-cocycle-and-flat-square-law.md

Lean:
formal/GaloisForLFunctions/HTGeometry/ObserverClockTriangularRepresentation.lean
Stage-3 certificate in matching folder. Wired into HTGeometry.UniversalLawField, umbrella not built.

Mechanism:
- P = canonical row+column marginal recovery; Q = anchored interaction.
- P+Q=Id; P|H=0, Q|H=Id.
- Scale clock multiplier T_lambda preserves H, hence relative to V=M⊕H:
  T_lambda = [[A_lambda,0],[H_lambda,D_lambda]].
- Exact composition:
  A_(lambda*mu)=A_lambda A_mu
  D_(lambda*mu)=D_lambda D_mu
  H_(lambda*mu)=H_lambda A_mu + D_lambda H_mu.
- Since clock rates commute:
  H_lambda A_mu + D_lambda H_mu =
  H_mu A_lambda + D_mu H_lambda.
  This is exact flat clock-square conservation.
- Every clock output splits into observed marginal + lifted interaction.
- If observed marginal closes, full lift closes iff anomaly is zero. This is literal closed-observer/open-history mechanism.
- Constant FE sign/phase is diagonal and information-neutral via ULF-TAFM-20.

Verification: scratch and direct Lean pass; targeted build 8780/8780; 10 capstones depend only on propext, Classical.choice, Quot.sound; no forbidden declarations.

Boundary: flatness constrains composition but not magnitude. Next RH producer must be a source-specific signed admission theorem bounding literal arithmetic cocycle in a bilateral interaction chamber.