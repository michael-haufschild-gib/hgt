# Mobius squarefree Fisher regular-germ cofinal four-unit law

- **ID:** `mobius-squarefree-fisher-regular-germ-cofinal-four-unit-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `../1-in-progress/mobius-incidence-curvature-gamma-sonin-pole-divisor-transfer-rh.md`
- **Statement:** At every strict-right Xi zero, physical source scaling gives the exact Fisher pole/analytic split, while the analytic germ at the moving zero tends to `2` and its squared magnitude tends to `4`.

## RH effect

Discharges MSC distinguished-point regular finite-part budget. Remaining: graph-uniform
nonexpansiveness, oriented-residue horizontal annihilation, and cofinal graph convergence.

## Certificate

- Lean: `RHTower.exists_mscPhysicalRegularGerm_residueSplit_tendsto_four`
- Module: `GaloisForLFunctions.RHTower.HedenmalmGammaSewnSquarefreeFisherRegularGermCofinal`
- `lake env lean` and targeted `lake build` pass.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- 2026-08 audit (`2606.17494`, `2606.09096`, `2511.22755`, `2608.24827`): no squarefree Fisher regular-germ/cofinal-four statement found.
