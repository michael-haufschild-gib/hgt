# Suzuki finite-Stieltjes ground-edge exclusion universality law

## Status

In progress — paper proof and Lean source complete; exact check and literature novelty audit pending.

## Theorem-first provenance

- `RHTower/SuzukiFiniteStieltjesHerglotzMassLaw.lean`
  - `suzukiFiniteNegativeStieltjesHerglotz_massLaw`
- `RHTower/SuzukiGroundEdgeApertureObstruction.lean`
  - `suzukiGroundEdgeAverage_gt_XiC_curvature_of_half_lowerMoment`
- `RHTower/SuzukiGroundEdgeHerglotzObstructionLaw.lean`
  - `not_suzukiAffineSewnExteriorWeylQuotient_herglotz_of_groundEdgeMoment`

## Universal law

A finite negative-Stieltjes Suzuki source and a positive ground-edge source cannot describe the
same affine-sewn central flux when the ground moment is at least half the Xi-curvature times its
positive mass. Under Herglotz positivity, finite Stieltjes chord mass forces that flux at or below
Xi curvature, while the ground-edge moment forces it strictly above Xi curvature.

This is the exact source-identification obstruction joining the spectral-mass and Robin/ground
descriptions of the same exterior Weyl quotient.

## Paper proof

Assume Herglotz positivity. The finite-Stieltjes mass law gives
`edge - spectralMass ≤ XiCurvature`. The half-curvature ground-moment theorem gives
`XiCurvature < groundAverage`. The source-identification hypothesis equates `groundAverage` with
`edge - spectralMass`, a contradiction.

## Lean status

Source complete in
`formal/GaloisForLFunctions/RHTower/SuzukiFiniteStieltjesGroundEdgeExclusionUniversalityLaw.lean`.

Exact source check is deferred because the parent
`SuzukiFiniteStieltjesHerglotzMassLaw.olean` is not yet present. Source proof is complete; parent
and this file remain in the final dependency-refresh batch.

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only; corpus search found
the finite-Stieltjes Herglotz mass budget and the ground-edge Herglotz obstruction separately but
no theorem excluding their exact source identification.
