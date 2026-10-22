# Suzuki Screw Cesaro Curvature Recurrence — Lean certificate

- **ID:** `suzuki-screw-cesaro-curvature-recurrence-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-screw-cesaro-curvature-recurrence.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiLargeNegativeShiftCentralFlux.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiScrewCesaroLandauRecurrence.lean`
- `formal/GaloisForLFunctions/RHTower/XiCanonicalProduct.lean`
- `formal/GaloisForLFunctions/RHTower/XiHadamardGrowth.lean`
- `formal/GaloisForLFunctions/RHTower/XiRelativeResolventTrace.lean`
- `formal/GaloisForLFunctions/RHTower/XiWeilPolarization.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiScrewCesaroCurvatureRecurrence.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.RHTower.Suzuki.SuzukiLargeNegativeShiftCentralFlux`:

```text
RHTower.eventually_XiC_curvature_lt_suzukiDyadicNegativeShiftIntercept
RHTower.suzukiDyadicNegativeShiftIntercept
RHTower.tendsto_suzukiDyadicNegativeShiftIntercept_atTop
```

`GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewCesaroLandauRecurrence`:

```text
RHTower.continuousAt_xiSquareResolventSum_zero
RHTower.continuous_xiScrewCosSum
RHTower.continuous_xiSuzukiScrewProfile
RHTower.deriv_xiCanonicalProduct_zero
RHTower.hasDerivAt_logDeriv_canonical_zero
RHTower.integral_xiScrewCosTerm
RHTower.secondDeriv_xiCanonicalProduct_zero
RHTower.summable_integral_norm_xiScrewCosTerm
RHTower.suzukiCurvatureCenteredPrimitive_eq_realWaveTrace
RHTower.xiCopyWaveSpectrum
RHTower.xiCopyWaveSpectrum_waveTrace_one
RHTower.xiScrewCesaroMean_cofinallyCrosses
RHTower.xiScrewCesaroMean_cofinallyCrosses_centralCurvature
RHTower.xiScrewCurvature
RHTower.xiScrewCurvature_eq_central_curvature
RHTower.xiScrewDivisorTerm_eq
RHTower.xiScrewDivisor_eq
RHTower.xiScrewPrimitive_cofinal_sign_change
RHTower.xiSquareResolventSum
RHTower.xiSquareResolventSum_zero
RHTower.xiSuzukiScrewProfile_sub_curvature
```

`GaloisForLFunctions.RHTower.XiCanonicalProduct`:

```text
RHTower.xiSpectralPoint_inv_sq_summable
```

`GaloisForLFunctions.RHTower.XiHadamardGrowth`:

```text
RHTower.XiC_eq_constant_mul_canonicalProduct
```

`GaloisForLFunctions.RHTower.XiRelativeResolventTrace`:

```text
RHTower.logDeriv_xiCanonicalProduct_eq_relativeResolventTrace
RHTower.xiRelativeResolventTrace_eq_reciprocalSquareResolvent
```

`GaloisForLFunctions.RHTower.XiWeilPolarization`:

```text
RHTower.xiSpectralPoint_lineConj
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 29 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.

## Open gates carried by the paper card

- 3 -> 4 publication-ready: standalone theorem + proof + novelty audit

These are research frontier items, not formalization debt.
