# Theta-cusp pairwise-strict ternary-localization universality law

## Status

- Stage: 3-formalized
- Lean target: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspPairwiseStrictTernaryLocalizationUniversalityLaw`
- Scientific status: `[PROVED HERE] [FORMALIZED] [UNCONDITIONAL] [NOT RH]`

## Theorem-generated route

Source statements were read first:

- `thetaCuspCenterMixedTwoNodeMatrix_posDef`
- `thetaCuspCenterMixedThreePointMatrix_posSemidef_iff`
- `thetaCuspCenterMixedThreePoint_localizationLaw`

For ordered nodes `0, x, x+y`, these statements concern the same three gaps `x`, `y`, and `x+y`.
Combining them shows every full-matrix failure occurs while all three two-node sectors remain
strictly positive, and is therefore a genuinely ternary negative-determinant obstruction.  The
existing localization radii confine it to one bounded middle shell.

## Original localization law

At every critical aperture, every possible center-mixed theta three-node PSD failure is confined
away from coalescence and infinity, has negative cubic determinant, and has positive-definite
two-node matrices at all three pairwise gaps.

## Stronger closure

Global source-angle concavity now proves

```text
Matrix.PosSemidef (thetaCuspCenterMixedThreePointMatrix a x y)
```

for every admissible aperture and every nonnegative pair of gaps.  Consequently the localized
failure shell is empty and no admissible positive-gap packet has negative cubic determinant.
The original localization certificate remains true, but its failure branch is vacuous.

Formalized declarations:

- `thetaCuspCenterMixedThreePointMatrix_posSemidef`
- `thetaCuspCenterMixedThreePointDeterminant_nonneg`
- `thetaCusp_pairwiseStrict_ternaryLocalization_no_failure`
- `thetaCusp_pairwiseStrict_ternaryLocalization_no_negativeDeterminant`

## Audits

- Exact direct Lean checks and targeted module build passed.
- Axiom audit contains only standard `propext`, `Classical.choice`, and `Quot.sound`.
- External priority remains unverified; no novelty claim is made.
