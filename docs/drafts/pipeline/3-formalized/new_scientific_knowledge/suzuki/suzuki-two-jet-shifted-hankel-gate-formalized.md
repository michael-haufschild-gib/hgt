# Suzuki Two-Jet Shifted-Hankel Gate — Lean certificate

- **ID:** `suzuki-two-jet-shifted-hankel-gate-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-two-jet-shifted-hankel-gate.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/RHTower/SuzukiPositiveResolventParityNoGo.lean`
- `formal/GaloisForLFunctions/RHTower/SuzukiPositiveSpectralResponseNoGo.lean`
- `formal/GaloisForLFunctions/RHTower/SuzukiRelativeTiltReciprocalConcavity.lean`
- `formal/GaloisForLFunctions/RHTower/SuzukiTwoJetShiftedHankelGate.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.RHTower.SuzukiPositiveResolventParityNoGo`:

```text
RHTower.suzukiPositiveParityResolventModel_of_positive
RHTower.suzukiPositiveParityResolvent_slack_surjective_at_fixed_torque
```

`GaloisForLFunctions.RHTower.SuzukiPositiveSpectralResponseNoGo`:

```text
RHTower.suzukiThreePointResolvent_commutes_position
RHTower.suzukiThreePointResponse_sourceEquation
RHTower.suzukiThreePoint_relativeTiltGap_gt_one
RHTower.suzukiThreePoint_twoJetSlack_eq
```

`GaloisForLFunctions.RHTower.SuzukiRelativeTiltReciprocalConcavity`:

```text
RHTower.iteratedDeriv_two_squaredXiReciprocalRadialField
RHTower.primeArchSuzukiRelativeTiltGapCalibration_eq_moments
RHTower.primeArchSuzukiRelativeTiltGapCalibration_le_one_iff_shiftedHankelMinor_nonneg
RHTower.primeArchSuzukiRelativeTiltGapCalibration_pos
RHTower.squaredXiReciprocalRadialField_concaveAt_one_iff_shiftedHankelMinor_nonneg
RHTower.suzukiAllAngleCarrier_forces_relativeTiltGap_le_one
RHTower.suzukiSecondDefectParityCurvature_eq_relativeTiltGap
```

`GaloisForLFunctions.RHTower.SuzukiTwoJetShiftedHankelGate`:

```text
RHTower.moment_twoJetSlack_eq_hankelMinor
RHTower.norm_iteratedDeriv_two_le_schurSlack
RHTower.primeArchSuzuki_twoJetSlack_eq_shiftedHankelMinor
RHTower.primeArchSuzuki_twoJetSlack_nonneg_iff_shiftedHankelMinor_nonneg
RHTower.real_secondJet_add_schurBoundary_nonneg
RHTower.suzukiAllAngleCarrier_forces_parity_twoJetSlack
RHTower.suzukiAllAngleCarrier_forces_real_twoJetSlack
RHTower.suzukiParity_twoJetSlack_balanced_nonneg_iff
RHTower.suzukiParity_twoJetSlack_eq
RHTower.suzukiParity_twoJetSlack_of_balanced_energy
RHTower.suzukiParity_twoJetSlack_surjective_at_fixed_torque
RHTower.suzukiParity_twoJetSlack_torque_decomposition
RHTower.suzukiSchurCarrier_forces_parity_twoJetSlack
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 26 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.

## Open gates carried by the paper card

- 3 -> 4 publication-ready: specialist priority review and integration into a standalone

These are research frontier items, not formalization debt.
