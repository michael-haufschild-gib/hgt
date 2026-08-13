# Double-sine translation annihilator — formalization certificate

- **ID:** `double-sine-translation-annihilator`
- **Stage:** 3-formalized
- **Paper proof:**
  `other/double-sine-translation-annihilator.md`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/DoubleSineImaginaryRayAnnihilator.lean`
- **Umbrella:** `formal/GaloisForLFunctions/HTGeometry.lean`
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NOT RH]`

## Formalized theorem

For every positive imaginary-ray period frame `i a, i b` with irrational ratio `a/b`, Lean
constructs a genuine meromorphic double-sine source whose two translation defects are the exact
opposite-period cotangent sources. Its translation annihilator modulo the differentially algebraic
sector over `ℂ(z)` is exactly the augmentation ideal. Equivalently, a finite structural translation
operator sends the source into the DA sector exactly when the sum of its coefficients vanishes.

Capstone:

```text
GaloisForLFunctions.HTGeometry.daTranslationAnnihilator_doubleSine_imaginaryRay
```

The theorem constructs its source internally from the imaginary-ray Barnes frame. It does not
assume hypertranscendence, the annihilator classification, or an unproved analytic continuation
statement.

## Verification

- Direct `lake env lean` check passes.
- Targeted `lake build GaloisForLFunctions.HTGeometry.DoubleSineImaginaryRayAnnihilator` passes.
- Scratch `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Module is imported by the `HTGeometry` umbrella.
- No `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declaration occurs in the owning module.

The independent Barnes-reflection construction remains a separate analytic asset; it is not a
premise of this closed imaginary-ray existence theorem.
