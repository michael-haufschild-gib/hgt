# Suzuki–Xi first-defect jet gap — Lean certificate

- **ID:** `suzuki-xi-first-defect-jet-gap-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-xi-first-defect-jet-gap.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiXiFirstDefectJet.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiXiFirstDefectJetSource.lean`
- `formal/GaloisForLFunctions/RHTower.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.RHTower.Suzuki.SuzukiXiFirstDefectJet`:

```text
RHTower.eightyFive_mul_re_xiShiftedReciprocalMoment_one_lt_four_mul_zero
RHTower.eightyFive_mul_re_xiShiftedReciprocalSquare_sq_lt_four_mul_re
RHTower.seventySeven_div_eightyFive_mul_xiRealLogDeriv_one_lt_deriv
RHTower.xiHedenmalmLivsicFirstDefectJet_mem_Ioo
RHTower.xiHedenmalmLivsic_firstDefectJet_tendsto_of_locallyUniform
```

`GaloisForLFunctions.RHTower.Suzuki.SuzukiXiFirstDefectJetSource`:

```text
RHTower.suzukiGroundLeakage_eventually_gt_xiHedenmalmLivsicFirstDefectJet_floor
RHTower.suzuki_defectAngle_tendsto_xiHedenmalmLivsicFirstDefectJet
RHTower.xiHedenmalmLivsicFirstDefectJet_groundLeakageFloor_pos
RHTower.xiHedenmalmLivsic_matching_source_parity_shares
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 9 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.

## Open gates carried by the paper card

- source-only cofinal schedule enters the strict cone and identifies full Xi target
- RH or class-complete no-go

These are research frontier items, not formalization debt.
