# Suzuki homogeneous projective-resolvent Plücker lift — Lean certificate

- **ID:** `suzuki-homogeneous-projective-resolvent-plucker-lift-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-homogeneous-projective-resolvent-plucker-lift.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/HTGeometry/AlternatingChordLaw.lean`
- `formal/GaloisForLFunctions/RHTower/Deninger/DeningerBaumslagRationalization.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiProjectiveResolventBlade.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiProjectiveResolventPluckerLift.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.HTGeometry.AlternatingChordLaw`:

```text
GaloisForLFunctions.HTGeometry.altPair
GaloisForLFunctions.HTGeometry.altPair_chord
GaloisForLFunctions.HTGeometry.altPair_self
GaloisForLFunctions.HTGeometry.exteriorPair_chord
```

`GaloisForLFunctions.RHTower.Deninger.DeningerBaumslagRationalization`:

```text
RHTower.DeningerBau.sound
```

`GaloisForLFunctions.RHTower.Suzuki.SuzukiProjectiveResolventBlade`:

```text
RHTower.suzukiHomogeneousResolventBlade_chord
RHTower.suzukiHomogeneousState_eq
RHTower.suzukiResolventBlade_chord
```

`GaloisForLFunctions.RHTower.Suzuki.SuzukiProjectiveResolventPluckerLift`:

```text
RHTower.suzukiCenteredProjectiveShiftNumerator_eq_projectiveMinor
RHTower.suzukiDiagonalProjectiveChord_diagonal_eq_zero
RHTower.suzukiDiagonalProjectiveChord_expansion
RHTower.suzukiDiagonalProjectiveChord_symmetrized
RHTower.suzukiHomogeneousProjectiveResolventChord
RHTower.suzukiProjectiveResolventMinor
RHTower.suzukiProjectiveResolventMinor_chord
RHTower.suzukiProjectiveResolventMinor_eigenvector_eq_zero
RHTower.suzukiProjectiveResolventMinor_swap
RHTower.suzukiProjectiveResolventMinor_twoResolvents
RHTower.suzukiProjectiveResponse_sub_eq_minor
RHTower.suzukiShiftedAffineSourceNumerator
RHTower.suzukiShiftedAffineSourceNumerator_eq_homogeneous
RHTower.suzukiShiftedAffineSourceProjectiveChord_twoResolvents
RHTower.suzukiTwoModeProjectiveResolventMinor_eq
RHTower.suzukiTwoModeProjectiveResolventMinor_nonneg_iff_orientation
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 24 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.
