# Suzuki resolvent-jet homogeneous Plücker tomography — Lean certificate

- **ID:** `suzuki-resolvent-jet-homogeneous-plucker-tomography-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-resolvent-jet-homogeneous-plucker-tomography.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/RHTower/SuzukiHomogeneousBladeDimension.lean`
- `formal/GaloisForLFunctions/RHTower/SuzukiResolventJetHomogeneousPluckerTomography.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.RHTower.SuzukiHomogeneousBladeDimension`:

```text
RHTower.suzukiHomogeneousBlade_finrank
```

`GaloisForLFunctions.RHTower.SuzukiResolventJetHomogeneousPluckerTomography`:

```text
RHTower.suzukiCyclicResolventFilter_realizes_target_fun
RHTower.suzukiHomogeneousBladePairCoordinate_unit_eq_zero
RHTower.suzukiHomogeneousBlade_twoModeDifference_infinity_zero
RHTower.suzukiHomogeneousBlade_twoModeDifference_isolates_pair
RHTower.suzukiSpectralResolventJet_realizes_target
RHTower.suzukiZeroConstantResolventInterpolant_eval
RHTower.suzukiZeroConstantResolventInterpolant_eval_zero
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 8 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.

## Open gates carried by the paper card

- 3 → 4 publication-ready: standalone paper and priority audit

These are research frontier items, not formalization debt.
