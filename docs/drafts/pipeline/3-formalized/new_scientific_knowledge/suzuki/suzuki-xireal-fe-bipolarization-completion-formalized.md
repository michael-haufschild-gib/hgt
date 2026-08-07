# Suzuki Xi-real/FE bipolarization gives exact minimal Krein completion — Lean certificate

- **ID:** `suzuki-xireal-fe-bipolarization-completion-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-xireal-fe-bipolarization-completion.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/RHTower/DeningerBaumslagRationalization.lean`
- `formal/GaloisForLFunctions/RHTower/SuzukiXiRealFEBipolarizationCompletion.lean`
- `formal/GaloisForLFunctions/RHTower.lean`
- `formal/GaloisForLFunctions/RHTower/MobiusLaplaceBoundaryMultiplicity.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.RHTower.DeningerBaumslagRationalization`:

```text
RHTower.DeningerBau.sound
```

`GaloisForLFunctions.RHTower.SuzukiXiRealFEBipolarizationCompletion`:

```text
RHTower.suzukiWeldCompletedNonnegative_isLeast
RHTower.suzukiWeldNegativeLightForm_self_eq_zero_iff
RHTower.suzukiWeldNegativeLightForm_self_nonneg
RHTower.suzukiWeldPositiveLightForm_self_eq_zero_iff
RHTower.suzukiWeldPositiveLightForm_self_nonneg
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 6 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.
