# Integral cofinal Tate relative-reflection assembly law — Lean certification

- **ID:** `ULF-ICTRRA-1`
- **Paper card:**
  `completion-index-transgression-mechanics/integral-cofinal-tate-relative-reflection-assembly-law.md`
- **Lean module:**
  `GaloisForLFunctions.RHTower.IntegralCofinalTateRelativeReflectionAssembly`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified declarations

- integral finite Tate basis, forward shift, zero-extension, and top boundary;
- `deningerIntegralTateIntervalForward_inclusion_defect`: integral cofinal Bockstein law;
- `deningerIntegralTateScaledForwardNaturalityDefect_eq_topBoundary`;
- `deningerIntegralTateFlatMinusRawCofinalDefect_eq_topBoundary`;
- `deningerIntegralTateRelativeReflectionCoefficientMatrix_eq`: reciprocal integral clock defects
  reconstruct `C_T`;
- `deningerIntegralCofinalRelativeReflectionOperator`: global direct-sum source operator;
- `deningerIntegralCofinalRelativeReflectionOperator_sq`: global source Clifford law.

## Verification

```text
lake env lean /tmp/integral_tate_assembly_scratch.lean
lake build GaloisForLFunctions.RHTower.IntegralCofinalTateRelativeReflectionAssembly
lake env lean /tmp/integral_tate_assembly_axioms.lean
```

Scratch check, targeted module build, and axiom audit passed. Every certified theorem depends only
on `propext`, `Classical.choice`, and `Quot.sound`. Module is wired into universal-law umbrella; no
umbrella build was run.

## Exact field consequence

Universal curved Tate object is now assembled globally over the integral Laurent source before
any Xi divisor or physical character. Remaining construction is its global Gamma base-change
square; remaining RH-bearing theorem after that is integral strictness of actual Xi completion.
