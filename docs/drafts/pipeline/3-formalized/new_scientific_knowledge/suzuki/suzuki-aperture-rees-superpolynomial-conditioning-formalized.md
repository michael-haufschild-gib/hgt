# Suzuki prime-cutoff aperture forces superpolynomial reflected-sewing conditioning — Lean certificate

- **ID:** `suzuki-aperture-rees-superpolynomial-conditioning-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-aperture-rees-superpolynomial-conditioning.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiApertureReesConditioningNoGo.lean`
- `formal/GaloisForLFunctions/RHTower.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.RHTower.Suzuki.SuzukiApertureReesConditioningNoGo`:

```text
RHTower.log_natCast_add_one_le_primeWoldBoundaryVolumeBelow_succ_inv
RHTower.reflectedHellingerSewingOperatorNorm_beyondEverySuzukiAperturePower
RHTower.reflectedHellingerSewingOperatorNorm_not_isBigO_suzukiAperturePower
RHTower.suzukiPrimeCutoffAperture_le_woldScale_succ
RHTower.suzukiPrimeCutoffAperture_pow_isBigO_woldScale_succ_pow
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 5 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.

## Open gates carried by the paper card

- external priority audit

These are research frontier items, not formalization debt.
