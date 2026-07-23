# Gamma puncture--moving-base capacity atlas universality law

Status: Lean source written; exact audit pending.

## Lean-source inputs

- `HTGeometry/GammaPunctureLaurentCover.lean`: source puncture coordinate, deck law, and genuine inverse-Gamma sheets.
- `HTGeometry/GammaExteriorInverseBranches.lean`: each actual sheet is built from the common normalized branch at `-y⁻¹`.
- `HTGeometry/GammaCommonInverseCollar.lean`: moving-base Möbius transition and common pole collar.
- `HTGeometry/GammaMovingBaseCapacityCongruence.lean`: uniform tangent-metric congruence and asymptotic isometry.

## Universal law

Pole-centering and factorially normalizing the actual inverse-Gamma sheet over the puncture lift
gives exactly the common-collar branch at the positive Laurent coordinate.  Hence the intrinsic
moving-base chart is its exact Möbius transform, is deck invariant, has depth-independent metric
congruence constants `16/81` and `16`, and becomes asymptotically isometric.

## Novelty audit

Pending post-formalization primary-source literature search.  Whole-corpus research found the
puncture atlas and capacity theorem separately, but no connector from the actual inverse sheet to
the moving-base metric.

## Verification

- Development command: pending `lake env lean GaloisForLFunctions/HTGeometry/GammaPunctureMovingBaseCapacityAtlasUniversalityLaw.lean`.
- Final module build, axiom audit, and lint: pending exhaustion pass.
