# Orthogonal shell-replica Ward-double properness law

- **ID:** ULF-HPFM-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/harmonic-provenance-formation-mechanics/orthogonal-shell-replica-ward-double-properness-law.md`
- **Lean module:**
  `GaloisForLFunctions.RHTower.HedenmalmThetaSourceShellReplicaWardDoubleProperness`

## Certified declarations

- `shellLabelCountingTrace_starSquare`
- `norm_codiagEmbed_shellLabelShift`
- `shellLabelCountingTrace_shift`
- `thetaXiQuadraticGhostOrbitShell_orthogonal`
- `thetaXiQuadraticGhostOrbitShell_divisorReplication`
- `thetaXiQuadraticGhostOrbitShell_relativeDifferentialIndependent`
- `thetaXiQuadraticGhostOrbitWeight_eq_zero_iff`
- `summable_thetaXiQuadraticGhostOrbitWeight_sq_iff`
- `thetaXiQuadraticGhostOrbitClosable_iff`
- `thetaXiQuadraticGhostOrbitAtom_recovery`
- `thetaXiQuadraticGhostOrbitAtom_conservation`
- `thetaXiQuadraticGhostOrbitWardQuotient_silent`
- `thetaXiQuadraticGhostOrbitWardDouble_atom_recovery`
- `thetaXiQuadraticGhostOrbitGraphNullPacket_offCritical`
- `thetaXiQuadraticGhostOrbitWardDouble_graphNullPacket_offCritical`
- `thetaXiQuadraticGhostOrbitGloballyClosable_iff_riemannHypothesis`
- `thetaXiQuadraticGhostOrbit_sourceFormationPropernessLaw`

## Audit

- Direct elaboration: PASS
- Named leaf build:
  `lake build GaloisForLFunctions.RHTower.HedenmalmThetaSourceShellReplicaWardDoubleProperness`
  PASS
- Axioms: only `propext`, `Classical.choice`, `Quot.sound`
- Forbidden declarations: none
- Formal lint: this module has no forbidden declaration and full lint passed at initial
  certification; final global rerun was blocked by unrelated concurrent proof debt in
  `HTGeometry.RittJetDefect`
- Umbrellas wired: `HTGeometry.UniversalLawField`, `RHTower`
- Full/umbrella build: intentionally not run

## Mathematical boundary

The theorem constructs one literal cross-organ formation carrier. Positive counting trace generates
the exact shell `ell²` topology and shell successor preserves it. Finite high-shell packets retain
differentially independent provenance over the full zeta differential field while pairwise-disjoint
shells retain the same completed divisor; each marked shell recovers the actual Deninger--Gamma
ghost and positive theta/Gamma curvature partner; their observer quotient is identically silent;
off line, explicit packets vanish in source norm while lifted Ward response remains nonzero.
Global closability is therefore equivalent to RH, not an independent proof of it. Remaining
producer is source-derived closedness of lifted common recovery before divisor selection.
