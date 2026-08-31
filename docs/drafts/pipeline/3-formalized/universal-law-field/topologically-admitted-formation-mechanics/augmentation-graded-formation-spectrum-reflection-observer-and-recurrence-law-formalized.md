# Augmentation-graded formation spectrum law — Lean formalisation

- **Paper card:** ULF-TAFM-24
- **Stage:** 3-formalized
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.AugmentationGradedFormationSpectrum`
- **Source:**
  `formal/GaloisForLFunctions/HTGeometry/AugmentationGradedFormationSpectrum.lean`
- **Status:** direct Lean check and targeted module build pass; standard axioms only

## Certified statements

The module constructs the closed integral Laurent formation algebra `Z[T,T⁻¹]` and certifies:

1. `invert_augmentationFormationBoundary` — exact reflected-recovery intertwining at every order;
2. `augmentationHistoryReflection_involutive` — lossless involutive history lift;
3. `augmentationFormationBoundary_injective` — common recovery erases no finite history;
4. `augmentationObserverPairing_boundary` — all-order recovery/finite-difference Green law;
5. `augmentationReflection_associatedGraded_parity` — inversion is `(-1)^r` modulo order `r+1`;
6. `augmentationCycleClosure_factorization` and
   `augmentationCycleClosure_firstGradedResidue` — closed period `p` retains winding residue `p`;
7. `augmentationAdjacentGrade_orientationParity` — diagonal energy loses reflection orientation,
   adjacent-grade polarization retains it.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/AugmentationGradedFormationSpectrum.lean
exit 0

lake build GaloisForLFunctions.HTGeometry.AugmentationGradedFormationSpectrum
Build completed successfully
```

`#print axioms` reports only Lean/mathlib standard axioms `propext`, `Classical.choice`, and
`Quot.sound`; the elementary adjacent-grade theorem does not require `Classical.choice`.

No `sorry`, `admit`, project axiom, `opaque`, or `unsafe` declaration is used.

## Scope boundary

This certificate proves the dependency-closed algebraic core of formation-spectrum geometry.  It
does not assert the open differential-Rees/hypertranscendence comparison, literal prime-labelled
source landing, source action estimate `(AF.22)`, or RH.
