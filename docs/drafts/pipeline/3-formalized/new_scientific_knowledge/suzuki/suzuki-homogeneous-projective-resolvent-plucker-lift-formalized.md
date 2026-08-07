# Suzuki homogeneous projective-resolvent Plücker lift — Lean certificate

- **ID:** `suzuki-homogeneous-projective-resolvent-plucker-lift-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-homogeneous-projective-resolvent-plucker-lift.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/RHTower/SuzukiProjectiveResolventPluckerLift.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.RHTower.SuzukiProjectiveResolventPluckerLift`:

```text
RHTower.suzukiDiagonalProjectiveChord_diagonal_eq_zero
RHTower.suzukiDiagonalProjectiveChord_expansion
RHTower.suzukiDiagonalProjectiveChord_symmetrized
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 3 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.
