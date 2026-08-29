# Exact C5 master-residual decomposition

- **ID:** C5-MR-residual
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Reserve discarded by one-scalar master reduction is exactly adaptive scale-gap
  surplus plus exact third-likelihood-channel residual.

## Result

On `0 < t < u`, adaptive scale-gap term is strictly positive. On structural tail, third-channel
residual is also strictly positive, hence full master residual is strict. Exact identity is

`completed = master-reserved + adaptive scale-gap + adaptive third-channel residual`.

This is strongest positive survivor of C5 master-reserve seam no-go. It identifies exact data that
must remain in any literal direct-J proof.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.ThetaCuspFixedActionC5MasterReservedSeamNoGo`
- `c5CompletedMasterResidualReserve_eq_scaleGap_add_adaptiveResidual`
- `c5CompletedMasterAdaptiveScaleGap_pos`
- `c5CompletedMasterResidualReserve_pos`
- `c5CompletedCompensationMargin_pos_iff_master_gt_neg_residual`
- Targeted build: PASS.
- Axioms: only `propext`, `Classical.choice`, `Quot.sound`.
