# Suzuki Ground-Residue Polarization Selection — Lean certificate

- **ID:** `suzuki-ground-residue-polarization-selection-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-ground-residue-polarization-selection.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiGroundProjectionReflectionCone.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiGroundResiduePolarizationSelection.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.RHTower.Suzuki.SuzukiGroundProjectionReflectionCone`:

```text
RHTower.primeArchSuzukiGroundProjection_admitted_iff_reflectionCone
RHTower.primeArchSuzukiGroundProjection_admitted_of_reflection_fixed
RHTower.primeArchSuzukiGroundProjection_evenMass_gt_eightyOne_div_four_mul_oddMass
RHTower.primeArchSuzukiGroundProjection_not_admitted_of_reflection_antifixed
RHTower.primeArchSuzukiGroundProjection_oddShare_lt_four_div_eightyFive
RHTower.primeArchSuzukiGroundProjection_reflectionCone_iff_distance
RHTower.primeArchSuzukiGroundProjection_reflectionCone_iff_oddMass
RHTower.primeArchSuzukiGroundProjection_reflectionCorrelation_gt_seventySeven_div_eightyFive
RHTower.primeArchSuzukiGroundProjection_reflectionDistance_sq_lt
```

`GaloisForLFunctions.RHTower.Suzuki.SuzukiGroundResiduePolarizationSelection`:

```text
RHTower.exists_isGreatest_suzukiDefectMatchingShiftSet_of_two_limits
RHTower.primeArchSuzukiGreatestDefectShift_spec_of_groundResidues
RHTower.primeArchSuzukiGroundOddEvenThreshold_mem_Ioo
RHTower.primeArchSuzuki_target_lt_groundResidueAngle_iff_ratio
RHTower.target_lt_suzukiGroundResidueAngle_iff
RHTower.tendsto_suzukiDefectAngle_groundResidues
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 15 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.

## Open gates carried by the paper card

- 3 -> 4 publication-ready: specialist priority review and inclusion in a standalone Suzuki

These are research frontier items, not formalization debt.
