# Suzuki negative-shift defect escape — Lean certificate

- **ID:** `suzuki-negative-shift-defect-escape-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-negative-shift-defect-escape.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/HTGeometry/ApertureFourierPairing.lean`
- `formal/GaloisForLFunctions/HTGeometry/HyperbolicModulus.lean`
- `formal/GaloisForLFunctions/HTGeometry/LowerBoundedSourceResolvent.lean`
- `formal/GaloisForLFunctions/HTGeometry/PositiveOperatorInner.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiNegativeShiftEscape.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiProjectiveDefectBoundary.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiXiFirstDefectJet.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiXiFirstDefectJetSource.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.HTGeometry.ApertureFourierPairing`:

```text
GaloisForLFunctions.HTGeometry.apertureChar
GaloisForLFunctions.HTGeometry.apertureFourier_apertureExp_eq
GaloisForLFunctions.HTGeometry.norm_apertureFourier_sub_le_of_im_bound
```

`GaloisForLFunctions.HTGeometry.HyperbolicModulus`:

```text
GaloisForLFunctions.HTGeometry.exp_div_four_le_sinh
GaloisForLFunctions.HTGeometry.freeDefectAngle_eq
GaloisForLFunctions.HTGeometry.tendsto_freeDefectAngle_atTop
```

`GaloisForLFunctions.HTGeometry.LowerBoundedSourceResolvent`:

```text
GaloisForLFunctions.HTGeometry.LowerBoundedSource
GaloisForLFunctions.HTGeometry.LowerBoundedSource.exists_threshold_norm_smul_sub_lt
GaloisForLFunctions.HTGeometry.LowerBoundedSource.norm_shift_ge
GaloisForLFunctions.HTGeometry.LowerBoundedSource.shift_smul_sub
GaloisForLFunctions.HTGeometry.LowerBoundedSource.tendsto_smul_solution
GaloisForLFunctions.HTGeometry.freeSource
```

`GaloisForLFunctions.HTGeometry.PositiveOperatorInner`:

```text
GaloisForLFunctions.HTGeometry.abs_imbalance_lt_one
GaloisForLFunctions.HTGeometry.defectGramState
GaloisForLFunctions.HTGeometry.defectGramState_isHermitian
GaloisForLFunctions.HTGeometry.defectGramState_mulVec_even
GaloisForLFunctions.HTGeometry.defectGramState_mulVec_odd
GaloisForLFunctions.HTGeometry.imbalance_eq_neg_one_of_evenPart_eq_zero
GaloisForLFunctions.HTGeometry.imbalance_eq_one_of_oddPart_eq_zero
GaloisForLFunctions.HTGeometry.inner_div_norm_sq_eq_imbalance
GaloisForLFunctions.HTGeometry.inner_eq_evenPart_sq_sub_oddPart_sq
GaloisForLFunctions.HTGeometry.norm_sq_eq_evenPart_sq_add_oddPart_sq
GaloisForLFunctions.HTGeometry.parity_weight_nonneg
GaloisForLFunctions.HTGeometry.parity_weights
GaloisForLFunctions.HTGeometry.tInner_add_smul_id
GaloisForLFunctions.HTGeometry.tInner_shift_floor_eq_shift
GaloisForLFunctions.HTGeometry.tInner_shift_lower_bound
```

`GaloisForLFunctions.RHTower.Suzuki.SuzukiNegativeShiftEscape`:

```text
GaloisForLFunctions.RHTower.exists_shift_threshold_carrier_close
GaloisForLFunctions.RHTower.norm_freeDenominator_ge
GaloisForLFunctions.RHTower.norm_suzukiApertureCarrier_sub_free_le
GaloisForLFunctions.RHTower.norm_suzukiFreeLivsic_le_bound
GaloisForLFunctions.RHTower.suzukiApertureCarrier_apertureExp
GaloisForLFunctions.RHTower.suzukiApertureCarrier_smul
GaloisForLFunctions.RHTower.suzuki_negativeShift_escape
GaloisForLFunctions.RHTower.suzuki_negativeShift_escape_freeSource
```

`GaloisForLFunctions.RHTower.Suzuki.SuzukiProjectiveDefectBoundary`:

```text
GaloisForLFunctions.RHTower.suzukiFreeLivsic_tendstoUniformlyOn_upperStrip
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 36 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.

## Open gates carried by the paper card

- source-side cofinal shift selected with defect angle tending to `kappa_Xi∈(77/85,1)`,
- RH

These are research frontier items, not formalization debt.
