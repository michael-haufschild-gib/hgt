# Complementary primitive flux recovers Suzuki's weighted derivative — Lean certificate

- **ID:** `suzuki-complementary-primitive-flux-derivative-recovery-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-complementary-primitive-flux-derivative-recovery.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/HTGeometry/GraphFluxStabilityEstimate.lean`
- `formal/GaloisForLFunctions/RHTower/SuzukiGammaShiftKappa.lean`
- `formal/GaloisForLFunctions/RHTower/SuzukiPrimitiveFluxNonnormalGraphReduction.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.HTGeometry.GraphFluxStabilityEstimate`:

```text
GaloisForLFunctions.HTGeometry.neg_norm_mul_normSq_le_inner_neg_apply
GaloisForLFunctions.HTGeometry.norm_le_of_coercive
```

`GaloisForLFunctions.RHTower.SuzukiGammaShiftKappa`:

```text
GaloisForLFunctions.RHTower.neg_suzukiGammaShiftKappa_le_integral
```

`GaloisForLFunctions.RHTower.SuzukiPrimitiveFluxNonnormalGraphReduction`:

```text
GaloisForLFunctions.RHTower.primitiveFlux_cutoffComplement_sum
GaloisForLFunctions.RHTower.primitiveFlux_eq_cut_flux
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 5 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.

## Open gates carried by the paper card

- construct literal infinite paired-orbit source equation
- verify physical-root value/dipole flux matching
- prove finite paired-chart/small-aperture interior coverage
- pass recurrence-infinite apertures
- prove raw Evans injectivity or whole-Connes no-go

These are research frontier items, not formalization debt.
