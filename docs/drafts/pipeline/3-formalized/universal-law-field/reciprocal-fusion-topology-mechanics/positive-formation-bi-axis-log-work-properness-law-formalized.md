# Positive-formation bi-axis logarithmic-work properness law — Lean certificate

- **Paper theorem:** ULF-RFTM-3B
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutivePositiveFormationProperness`
- **Status:** `[LEAN-PROVED] [NO SORRY] [NO ADDED AXIOMS] [UMBRELLA-WIRED]`

## Formal theorem surface

- `posDef_natPow`
- `natPow_mul_self`
- `positiveFormationAmplified_midpoint`
- `positiveFormationMidpointWork_eq`
- `positiveFormationRelativeWork_eq`
- `cfcLog_eq_zero_iff_posDef`
- `positiveFormationMidpointWork_bounded_iff`
- `positiveFormationRelativeWork_bounded_iff`
- `positiveFormationBiAxisWork_bounded_iff`

The capstone proves that uniform boundedness of complete formation and relative-law amplification
works is equivalent to `R = 1 ∧ Q = 1` for positive-definite complex matrices.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutivePositiveFormationProperness.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutivePositiveFormationProperness
lake env lean /tmp/positive_formation_properness_axioms.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Axiom audit reports only mathlib foundations:

```text
propext
Classical.choice
Quot.sound
```

Scoped scan contains no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
