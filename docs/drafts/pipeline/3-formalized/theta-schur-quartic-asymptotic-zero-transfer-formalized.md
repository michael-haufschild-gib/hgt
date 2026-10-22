# Theta Schur quartic asymptotic zero transfer — Lean certificate

- **ID:** `GTA-PQ4-LSC-formalized`
- **Stage:** 3-formalized
- **Paper card:** `theta-schur-quartic-asymptotic-zero-transfer.md`
- **Module:** `GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSchurQuarticAsymptoticZeroTransfer`

## Exact certified surface

The module proves the literal persistent positive charge floor from every off-real `XiC` zero,
the cofinal-smallness criterion on actual corrected theta stages, and
`riemannHypothesis_of_thetaSourceSchurPositiveQuarticChargeCofinallySmall`. It also proves that the
stronger all-stage flag implies cofinal smallness. No zero-location, convergence, or Schur packet
hypothesis is added beyond the card's definitions.

## Verification

On 2026-08-28, direct `lake env lean` elaboration and targeted `lake build` of the named module
completed successfully. The card's earlier standard-only axiom audit was retained without repeat.

