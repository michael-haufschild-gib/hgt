# Suzuki boundary-log non-clock and non-flat tangent theorem — Lean certificate

- **ID:** `suzuki-boundary-log-nonclock-nonflat-tangent-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-boundary-log-nonclock-nonflat-tangent.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/HTGeometry/CfcNormBound.lean`
- `formal/GaloisForLFunctions/HTGeometry/CompactOperatorDiscreteSpectrum.lean`
- `formal/GaloisForLFunctions/HTGeometry/HadamardFinitePart.lean`
- `formal/GaloisForLFunctions/HTGeometry/SignedCharFunCentralJet.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiBoundaryLogEndpointBlowUp.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiFiniteShiftNonClock.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiRestrictedWeilForm.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiStrongResolventLimit.lean`
- `formal/GaloisForLFunctions/HTGeometry/StrongConvergenceDense.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.HTGeometry.CfcNormBound`:

```text
GaloisForLFunctions.HTGeometry.abs_neumannFamilySymbol_le
GaloisForLFunctions.HTGeometry.abs_neumannSymbol_le
GaloisForLFunctions.HTGeometry.abs_resolventSymbol_le
GaloisForLFunctions.HTGeometry.eventually_forall_abs_neumannSymbol_le
GaloisForLFunctions.HTGeometry.neumannSymbol_sub_one_mul
GaloisForLFunctions.HTGeometry.tendsto_norm_cfc_zero
```

`GaloisForLFunctions.HTGeometry.CompactOperatorDiscreteSpectrum`:

```text
GaloisForLFunctions.HTGeometry.tendsto_id_of_norm_comp_tendsto_zero
```

`GaloisForLFunctions.HTGeometry.HadamardFinitePart`:

```text
GaloisForLFunctions.HTGeometry.cutoffDividedDifference
GaloisForLFunctions.HTGeometry.cutoffFinitePart
GaloisForLFunctions.HTGeometry.cutoffFinitePart_eq
GaloisForLFunctions.HTGeometry.integral_left_inv_sub
GaloisForLFunctions.HTGeometry.integral_punctured_inv_dist
GaloisForLFunctions.HTGeometry.integral_right_inv_sub
```

`GaloisForLFunctions.HTGeometry.SignedCharFunCentralJet`:

```text
GaloisForLFunctions.HTGeometry.exponentialSourceCombination_pairing
GaloisForLFunctions.HTGeometry.neg_integral_expNeg_mul_deriv
GaloisForLFunctions.HTGeometry.neg_integral_exp_mul_deriv
```

`GaloisForLFunctions.RHTower.Suzuki.SuzukiBoundaryLogEndpointBlowUp`:

```text
GaloisForLFunctions.RHTower.abs_cauchyDividedDifference_le
GaloisForLFunctions.RHTower.cauchyDividedDifference
GaloisForLFunctions.RHTower.cauchyFinitePart_eq_dividedDifference_add
GaloisForLFunctions.RHTower.not_bounded_of_tendsto_neg_half_cauchyFinitePart
GaloisForLFunctions.RHTower.tendsto_neg_half_cauchyFinitePart_atTop
```

`GaloisForLFunctions.RHTower.Suzuki.SuzukiFiniteShiftNonClock`:

```text
GaloisForLFunctions.RHTower.suzukiBoundaryLogTerm
GaloisForLFunctions.RHTower.suzukiBoundaryPole_ne_log_add_bounded
GaloisForLFunctions.RHTower.tendsto_sub_mul_suzukiBoundaryLog
GaloisForLFunctions.RHTower.tendsto_sub_mul_suzukiBoundaryPole
```

`GaloisForLFunctions.RHTower.Suzuki.SuzukiRestrictedWeilForm`:

```text
GaloisForLFunctions.RHTower.ApertureTest
GaloisForLFunctions.RHTower.IsRestrictedWeilRepresentative
GaloisForLFunctions.RHTower.blockKernels_sum_eq_representative
GaloisForLFunctions.RHTower.cauchyFinitePart
GaloisForLFunctions.RHTower.intervalIntegral_eq_integral_of_apertureTest
GaloisForLFunctions.RHTower.restrictedWeilForm
GaloisForLFunctions.RHTower.restrictedWeilForm_eq_blocks
GaloisForLFunctions.RHTower.restrictedWeilRepresentative
GaloisForLFunctions.RHTower.restrictedWeilRepresentative_eq
GaloisForLFunctions.RHTower.weilFinitePartBlock_eq
GaloisForLFunctions.RHTower.weilPrimeBlock_eq
GaloisForLFunctions.RHTower.weilPrimeBlock_eq_jumpForms
GaloisForLFunctions.RHTower.weilScalarBlock_eq
GaloisForLFunctions.RHTower.weilSmoothBlock_eq
```

`GaloisForLFunctions.RHTower.Suzuki.SuzukiStrongResolventLimit`:

```text
GaloisForLFunctions.RHTower.tendsto_neumannShiftFamily_id
GaloisForLFunctions.RHTower.tendsto_resolventFamily_id
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 41 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.
