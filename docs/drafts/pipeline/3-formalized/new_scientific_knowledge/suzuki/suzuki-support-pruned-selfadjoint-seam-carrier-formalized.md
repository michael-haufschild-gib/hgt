# Support-pruned prime seams have an exact self-adjoint Hilbert carrier — Lean certificate

- **ID:** `suzuki-support-pruned-selfadjoint-seam-carrier-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-support-pruned-selfadjoint-seam-carrier.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/RHTower/SuzukiSupportPrunedSeamCarrierBounds.lean`
- `formal/GaloisForLFunctions/RHTower/SuzukiSupportPrunedSelfAdjointSeamCarrier.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.RHTower.SuzukiSupportPrunedSeamCarrierBounds`:

```text
GaloisForLFunctions.RHTower.norm_lpCoordinateProjection_le
GaloisForLFunctions.RHTower.norm_suzukiFinitePrimeAdjacency_le
GaloisForLFunctions.RHTower.norm_suzukiGammaPositivePrimeAdjacency_le
GaloisForLFunctions.RHTower.norm_suzukiSeamShift_le
GaloisForLFunctions.RHTower.norm_suzukiSupportPrunedPrimeAdjacency_le
GaloisForLFunctions.RHTower.norm_suzukiSymmetricSeamStep_le
GaloisForLFunctions.RHTower.suzukiFinitePrimeAdjacency_apply
GaloisForLFunctions.RHTower.suzukiSeamShift_adjoint
GaloisForLFunctions.RHTower.suzukiSupportPrunedPrimeAdjacency_apply
```

`GaloisForLFunctions.RHTower.SuzukiSupportPrunedSelfAdjointSeamCarrier`:

```text
GaloisForLFunctions.RHTower.suzukiFinitePrimeAdjacency
GaloisForLFunctions.RHTower.suzukiGammaPositivePrimeAdjacency
GaloisForLFunctions.RHTower.suzukiSeamLocation
GaloisForLFunctions.RHTower.suzukiSeamRoot_left_not_admissible
GaloisForLFunctions.RHTower.suzukiSeamShift
GaloisForLFunctions.RHTower.suzukiSupportPrunedPrimeAdjacency
GaloisForLFunctions.RHTower.suzukiSymmetricSeamStep
GaloisForLFunctions.RHTower.suzukiSymmetricSeamStep_isSelfAdjoint
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 17 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.
