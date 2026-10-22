# Suzuki position-torque prime-clock irreducibility — Lean certificate

- **ID:** `suzuki-position-torque-prime-clock-irreducibility-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-position-torque-prime-clock-irreducibility.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiPositionTorquePrimeClockIrreducibility.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiWeilPositionTorqueCurvature.lean`
- `formal/GaloisForLFunctions/HTGeometry/PrimeResidueValuationExactSourceBoundary.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.RHTower.Suzuki.SuzukiPositionTorquePrimeClockIrreducibility`:

```text
RHTower.LSeries_suzukiPositionTorquePrimeFiniteAbscissaSource
RHTower.suzukiPositionTorqueEulerSource_eq_primeSource
RHTower.suzukiPositionTorquePrimeFiniteAbscissaSource
RHTower.suzukiPositionTorquePrimeFiniteAbscissaSource_apply
RHTower.suzukiPositionTorquePrimeSource_nonvanishing_layers_infinite
RHTower.suzukiPositionTorquePrimeSource_primePow_ne_zero
RHTower.suzukiPositionTorquePrimeSource_supportedOnPositivePrimePowers
RHTower.suzukiPositionTorquePrimeUpperEndCarrier
RHTower.suzukiPositionTorquePrimeUpperEndCarrier_differentialIndependent_over_localEulerResidueFusionCompletion
RHTower.suzukiPositionTorquePrimeUpperEndCarrier_hypertranscendentalOver_localEulerResidueFusionCompletion
```

`GaloisForLFunctions.RHTower.Suzuki.SuzukiWeilPositionTorqueCurvature`:

```text
RHTower.suzukiPositionTorqueEulerSource
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 11 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.
