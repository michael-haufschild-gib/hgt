# Suzuki low frequencies enter the Gamma seam through two boundary counterterms — Lean certificate

- **ID:** `suzuki-low-frequency-boundary-counterterm-renormalization-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-low-frequency-boundary-counterterm-renormalization.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiPhysicalLogBoundaryMomentLock.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.RHTower.Suzuki.SuzukiPhysicalLogBoundaryMomentLock`:

```text
GaloisForLFunctions.RHTower.boundaryMatchedHigh
GaloisForLFunctions.RHTower.boundaryMatchedHigh_eq_full_sub_lowRemainder
GaloisForLFunctions.RHTower.boundaryMatchedHigh_sub_boundaryMatchedHigh
GaloisForLFunctions.RHTower.boundaryMatchedHigh_zero
GaloisForLFunctions.RHTower.lipschitz_boundaryLogRemainder_le
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 5 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.

## Open gates carried by the paper card

- construct literal two-port moment map
- attach counterterms to the exact valuation/Feshbach carrier
- prove zero-trace matched carrier has no nonzero return
- prove raw Evans injectivity
- RH

These are research frontier items, not formalization debt.
