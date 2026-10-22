# Displacement--overlap conservation for bicausal tilted-tent transport — Lean certificate

- **ID:** `suzuki-bicausal-displacement-overlap-conservation-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-bicausal-displacement-overlap-conservation.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/HTGeometry/BicausalDisplacementOverlap.lean`
- `formal/GaloisForLFunctions/HTGeometry/TiltedTentTwoFlankSurplus.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiMangoldtLogHaarTransport.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.HTGeometry.BicausalDisplacementOverlap`:

```text
GaloisForLFunctions.HTGeometry.bicausalLeftTarget_inter_rightTarget
GaloisForLFunctions.HTGeometry.bicausalLeftTarget_union_rightTarget
GaloisForLFunctions.HTGeometry.bicausal_intervalIntegral_conservation
GaloisForLFunctions.HTGeometry.volume_bicausalSeam
```

`GaloisForLFunctions.HTGeometry.TiltedTentTwoFlankSurplus`:

```text
GaloisForLFunctions.HTGeometry.cosh_one_lt_seven_div_four
GaloisForLFunctions.HTGeometry.integral_tiltedTentFullProfile
GaloisForLFunctions.HTGeometry.tiltedTentTwoFlankSurplus_critical_eq
GaloisForLFunctions.HTGeometry.tiltedTentTwoFlankSurplus_critical_gt_two
GaloisForLFunctions.HTGeometry.tiltedTentTwoFlankSurplus_eq
```

`GaloisForLFunctions.RHTower.Suzuki.SuzukiMangoldtLogHaarTransport`:

```text
RHTower.mangoldtLogHaarTransportWidth
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 10 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.
