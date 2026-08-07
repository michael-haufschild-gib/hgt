# Suzuki completed eigenmodes are bounded by atomic-jump coercivity — Lean certificate

- **ID:** `suzuki-completed-eigenmode-atomic-jump-boundedness-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-completed-eigenmode-atomic-jump-boundedness.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/HTGeometry/AtomicJumpForm.lean`
- `formal/GaloisForLFunctions/RHTower/DeningerBaumslagRationalization.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.HTGeometry.AtomicJumpForm`:

```text
GaloisForLFunctions.HTGeometry.jumpForm
GaloisForLFunctions.HTGeometry.jumpForm_eq_two_pairing_sub
GaloisForLFunctions.HTGeometry.jumpForm_truncPos_ge
GaloisForLFunctions.HTGeometry.primePairWeight
GaloisForLFunctions.HTGeometry.primePairWeight_nonneg
GaloisForLFunctions.HTGeometry.sub_mul_truncPos_sub_ge
GaloisForLFunctions.HTGeometry.sum_primePairWeight_jumpForm_nonneg
GaloisForLFunctions.HTGeometry.sum_weighted_jumpForm_nonneg
GaloisForLFunctions.HTGeometry.truncPos
GaloisForLFunctions.HTGeometry.truncPos_mono
GaloisForLFunctions.HTGeometry.truncPos_sub_le
```

`GaloisForLFunctions.RHTower.DeningerBaumslagRationalization`:

```text
RHTower.DeningerBau.sound
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 12 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.

## Open gates carried by the paper card

- extend signed trace to bounded continuous weak solutions
- prove trace-zero completed zero modes enter \(H^1_0\)
- prove two-ended corona no-return
- prove raw Evans positivity
- RH

These are research frontier items, not formalization debt.
