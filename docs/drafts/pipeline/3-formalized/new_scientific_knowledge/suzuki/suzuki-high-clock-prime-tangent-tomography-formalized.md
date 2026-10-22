# Suzuki high-clock prime-tangent tomography — Lean certificate

- **ID:** `suzuki-high-clock-prime-tangent-tomography-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-high-clock-prime-tangent-tomography.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiPrimeTangentTomography.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.RHTower.Suzuki.SuzukiPrimeTangentTomography`:

```text
GaloisForLFunctions.RHTower.Suzuki.SuzukiPrimeTangentNonresonant
GaloisForLFunctions.RHTower.eventually_suzukiPrimeTangentNonresonant
GaloisForLFunctions.RHTower.exists_suzukiPrimeTangentNonresonant_above
GaloisForLFunctions.RHTower.exists_suzukiPrimeTangentTomography_above
GaloisForLFunctions.RHTower.norm_suzukiPrimeTangentPhase
GaloisForLFunctions.RHTower.suzukiCesaroMean
GaloisForLFunctions.RHTower.suzukiCesaroMean_smul
GaloisForLFunctions.RHTower.suzukiCesaroMean_sum
GaloisForLFunctions.RHTower.suzukiFinitePhaseCarrier
GaloisForLFunctions.RHTower.suzukiFiniteSinePhaseCarrier
GaloisForLFunctions.RHTower.suzukiPrimeTangentCarrier
GaloisForLFunctions.RHTower.suzukiPrimeTangentNonresonant_of_log_lt_aperture
GaloisForLFunctions.RHTower.suzukiPrimeTangentNormalize
GaloisForLFunctions.RHTower.suzukiPrimeTangentPhase
GaloisForLFunctions.RHTower.suzukiPrimeTangentScale
GaloisForLFunctions.RHTower.suzukiPrimeTangentScale_eq_reflected
GaloisForLFunctions.RHTower.suzukiPrimeTangentScale_pos
GaloisForLFunctions.RHTower.suzukiPrimeTangentWeight
GaloisForLFunctions.RHTower.suzukiPrimeTangentWeight_ne_zero_iff
GaloisForLFunctions.RHTower.suzukiPrimeTangentWeight_ne_zero_iff_primePow
GaloisForLFunctions.RHTower.tendsto_natCast_inv_complex_zero
GaloisForLFunctions.RHTower.tendsto_suzukiCesaroMean_geometric_one
GaloisForLFunctions.RHTower.tendsto_suzukiCesaroMean_geometric_zero
GaloisForLFunctions.RHTower.tendsto_suzukiFinitePhaseCarrier_bohrCoefficient
GaloisForLFunctions.RHTower.tendsto_suzukiFiniteSinePhaseCarrier_bohrCoefficient
GaloisForLFunctions.RHTower.tendsto_suzukiPrimeTangentCarrier_bohrCoefficient
GaloisForLFunctions.RHTower.tendsto_suzukiPrimeTangentCarrier_normalized_bohrCoefficient
GaloisForLFunctions.RHTower.tendsto_suzukiPrimeTangentCarrier_normalized_bohrCoefficient_of_nonresonant
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 28 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.

## Open gates carried by the paper card

- 3 -> 4: external mathematical novelty review and publication treatment pending

These are research frontier items, not formalization debt.
