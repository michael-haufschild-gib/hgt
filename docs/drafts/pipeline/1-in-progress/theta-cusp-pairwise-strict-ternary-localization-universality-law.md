# Theta-cusp pairwise-strict ternary-localization universality law

## Status

- Stage: 1-in-progress
- Lean target: `GaloisForLFunctions.RHTower.ThetaCuspPairwiseStrictTernaryLocalizationUniversalityLaw`

## Theorem-generated route

Source statements were read first:

- `thetaCuspCenterMixedTwoNodeMatrix_posDef`
- `thetaCuspCenterMixedThreePointMatrix_posSemidef_iff`
- `thetaCuspCenterMixedThreePoint_localizationLaw`

For ordered nodes `0, x, x+y`, these statements concern the same three gaps `x`, `y`, and `x+y`.
Combining them shows every full-matrix failure occurs while all three two-node sectors remain
strictly positive, and is therefore a genuinely ternary negative-determinant obstruction.  The
existing localization radii confine it to one bounded middle shell.

## Candidate law

At every critical aperture, every possible center-mixed theta three-node PSD failure is confined
away from coalescence and infinity, has negative cubic determinant, and has positive-definite
two-node matrices at all three pairwise gaps.

## Open audits

- Exact Lean check
- Axiom audit
- Literature novelty audit
