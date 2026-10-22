# Suzuki Interior-Excursion Shift Selection — Lean certificate

- **ID:** `suzuki-interior-excursion-shift-selection-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-interior-excursion-shift-selection.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiInteriorExcursionShiftSelection.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.RHTower.Suzuki.SuzukiInteriorExcursionShiftSelection`:

```text
RHTower.exists_isGreatest_suzukiDefectMatchingShiftSet_of_witness
RHTower.exists_suzukiDefectMatchingShift_of_interior_overshoot
RHTower.primeArchSuzukiGreatestDefectShift_spec_of_interior_overshoot
RHTower.suzukiDefectAngle_eq_target_iff
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 4 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.
