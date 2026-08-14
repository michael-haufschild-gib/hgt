# The dyadic Suzuki orbit charts cover every finite aperture for \(H^1\) — Lean certificate

- **ID:** `suzuki-dyadic-orbit-chart-h1-coverage-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-dyadic-orbit-chart-h1-coverage.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/HTGeometry/DyadicLatticeCover.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.HTGeometry.DyadicLatticeCover`:

```text
GaloisForLFunctions.HTGeometry.Ioo_subset_endpointWindow
GaloisForLFunctions.HTGeometry.Ioo_subset_endpointWindow_of_invisible_two
GaloisForLFunctions.HTGeometry.dyadicCenter
GaloisForLFunctions.HTGeometry.dyadicCenter_spacing
GaloisForLFunctions.HTGeometry.exists_dyadicCenter_close
GaloisForLFunctions.HTGeometry.exists_finset_dyadicWindow_cover
GaloisForLFunctions.HTGeometry.exists_finset_latticeWindow_cover
GaloisForLFunctions.HTGeometry.exists_latticeCenter_close
GaloisForLFunctions.HTGeometry.iUnion_latticeWindow_eq_univ
GaloisForLFunctions.HTGeometry.latticeCenter
GaloisForLFunctions.HTGeometry.latticeCenter_sub_succ
GaloisForLFunctions.HTGeometry.latticeCenter_zero
GaloisForLFunctions.HTGeometry.le_rpow_mul
GaloisForLFunctions.HTGeometry.log_two_pos
GaloisForLFunctions.HTGeometry.one_le_rpow_one_sub_two_mul
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 15 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.

## Open gates carried by the paper card

- prove weighted analytic admission of the assembled rough-primitive equation
- pass recurrence-infinite apertures
- prove raw Evans injectivity or whole-Connes no-go

These are research frontier items, not formalization debt.
