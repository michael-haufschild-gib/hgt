# Suzuki full-frequency Neumann holonomy survivor — Lean certificate

- **ID:** `suzuki-full-frequency-neumann-holonomy-survivor-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-full-frequency-neumann-holonomy-survivor.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/HTGeometry/CompactFourierSineKernel.lean`
- `formal/GaloisForLFunctions/HTGeometry/MomentFunctionalPositivity.lean`
- `formal/GaloisForLFunctions/HTGeometry/SignedCharFunCentralJet.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiFiniteShiftNonClock.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiFullFrequencyNeumannHolonomy.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.HTGeometry.CompactFourierSineKernel`:

```text
GaloisForLFunctions.HTGeometry.evenPart_div_of_odd
GaloisForLFunctions.HTGeometry.integral_const_mul_exp_mul_I_symm
GaloisForLFunctions.HTGeometry.oddPart_div_of_odd
GaloisForLFunctions.HTGeometry.oddPart_normalizedResponse_eq
GaloisForLFunctions.HTGeometry.tendsto_sineKernel_nhdsNE_zero
```

`GaloisForLFunctions.HTGeometry.MomentFunctionalPositivity`:

```text
HTGeometry.momentFunctional_X_pow
```

`GaloisForLFunctions.HTGeometry.SignedCharFunCentralJet`:

```text
GaloisForLFunctions.HTGeometry.contDiff_signedCharFun
GaloisForLFunctions.HTGeometry.deriv_signedCharFun_zero
GaloisForLFunctions.HTGeometry.signedCharFun_reflected_odd
```

`GaloisForLFunctions.RHTower.Suzuki.SuzukiFiniteShiftNonClock`:

```text
GaloisForLFunctions.RHTower.suzukiBoundaryPole_ne_log_add_bounded
GaloisForLFunctions.RHTower.tendsto_sub_mul_suzukiBoundaryLog
GaloisForLFunctions.RHTower.tendsto_sub_mul_suzukiBoundaryPole
```

`GaloisForLFunctions.RHTower.Suzuki.SuzukiFullFrequencyNeumannHolonomy`:

```text
RHTower.IsOddSourceMoments
RHTower.half_integral_neumannResponseDifference_eq_sineKernel
RHTower.momentFunctional_C
RHTower.momentFunctional_neumannResponseDifference
RHTower.momentFunctional_neumannResponseDifference_const
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 17 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.
