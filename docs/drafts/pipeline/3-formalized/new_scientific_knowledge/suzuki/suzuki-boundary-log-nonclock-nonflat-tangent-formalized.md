# Suzuki boundary-log non-clock and non-flat tangent theorem — Lean certificate

- **ID:** `suzuki-boundary-log-nonclock-nonflat-tangent-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-boundary-log-nonclock-nonflat-tangent.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/HTGeometry/CfcNormBound.lean`
- `formal/GaloisForLFunctions/HTGeometry/CompactOperatorDiscreteSpectrum.lean`
- `formal/GaloisForLFunctions/HTGeometry/SignedCharFunCentralJet.lean`
- `formal/GaloisForLFunctions/RHTower/SuzukiFiniteShiftNonClock.lean`
- `formal/GaloisForLFunctions/RHTower/SuzukiStrongResolventLimit.lean`
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

`GaloisForLFunctions.HTGeometry.SignedCharFunCentralJet`:

```text
GaloisForLFunctions.HTGeometry.exponentialSourceCombination_pairing
GaloisForLFunctions.HTGeometry.neg_integral_expNeg_mul_deriv
GaloisForLFunctions.HTGeometry.neg_integral_exp_mul_deriv
```

`GaloisForLFunctions.RHTower.SuzukiFiniteShiftNonClock`:

```text
GaloisForLFunctions.RHTower.suzukiBoundaryLogTerm
GaloisForLFunctions.RHTower.suzukiBoundaryPole_ne_log_add_bounded
GaloisForLFunctions.RHTower.tendsto_sub_mul_suzukiBoundaryLog
GaloisForLFunctions.RHTower.tendsto_sub_mul_suzukiBoundaryPole
```

`GaloisForLFunctions.RHTower.SuzukiStrongResolventLimit`:

```text
GaloisForLFunctions.RHTower.tendsto_neumannShiftFamily_id
GaloisForLFunctions.RHTower.tendsto_resolventFamily_id
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 16 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.
