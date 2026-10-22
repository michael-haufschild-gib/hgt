# Primitive flux removes Suzuki's nonnormal frequency group from the weighted graph estimate — Lean certificate

- **ID:** `suzuki-primitive-flux-nonnormal-graph-reduction-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-primitive-flux-nonnormal-graph-reduction.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/HTGeometry/GraphFluxStabilityEstimate.lean`
- `formal/GaloisForLFunctions/HTGeometry/ShiftedDerivativeCoercivity.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiGammaShiftKappa.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiPrimitiveFluxNonnormalGraphReduction.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.HTGeometry.GraphFluxStabilityEstimate`:

```text
GaloisForLFunctions.HTGeometry.graphFlux_flux_bound
GaloisForLFunctions.HTGeometry.graphFlux_state_bound
GaloisForLFunctions.HTGeometry.neg_norm_mul_normSq_le_inner_neg_apply
```

`GaloisForLFunctions.HTGeometry.ShiftedDerivativeCoercivity`:

```text
GaloisForLFunctions.HTGeometry.hasDerivAt_normSq_comp
GaloisForLFunctions.HTGeometry.integral_cross_eq_zero
GaloisForLFunctions.HTGeometry.normSq_shifted
GaloisForLFunctions.HTGeometry.sq_mul_integral_normSq_le
```

`GaloisForLFunctions.RHTower.Suzuki.SuzukiGammaShiftKappa`:

```text
GaloisForLFunctions.RHTower.neg_suzukiGammaShiftKappa_le_integral
```

`GaloisForLFunctions.RHTower.Suzuki.SuzukiPrimitiveFluxNonnormalGraphReduction`:

```text
GaloisForLFunctions.RHTower.primitiveFluxSystem_exponential_pointwise
GaloisForLFunctions.RHTower.primitiveFluxSystem_pointwise
GaloisForLFunctions.RHTower.primitiveFlux_absorption_div
GaloisForLFunctions.RHTower.primitiveFlux_absorption_mul
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 12 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.

## Open gates carried by the paper card

- prove flat tempered flux Liouville
- prove source-specific weighted derivative propagation to physical roots
- prove raw Evans injectivity or whole-Connes no-go

These are research frontier items, not formalization debt.
