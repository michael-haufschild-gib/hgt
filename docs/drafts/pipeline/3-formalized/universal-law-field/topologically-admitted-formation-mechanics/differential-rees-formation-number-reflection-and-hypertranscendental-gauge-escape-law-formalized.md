# Differential Rees formation number, reflection, and hypertranscendental gauge escape — formalized

**Card ID:** ULF-TAFM-25  
**Paper source:** `docs/drafts/pipeline/2-fully-proven/universal-law-field/topologically-admitted-formation-mechanics/differential-rees-formation-number-reflection-and-hypertranscendental-gauge-escape-law.md`  
**Lean module:** `GaloisForLFunctions.HTGeometry.DifferentialReesFormationSpectrum`  
**Status:** Formalized in Lean 4

## Certified interface

The module constructs the Laurent derivative internally and proves:

- `laurentFormationDerivative_mul`: exact Leibniz law;
- `laurentFormationDerivative_augmentationGenerator_pow`: derivative of every augmentation power;
- `formationNumber_boundary`: exact Euler connection law
  \(N(d^rP)=r d^rP+d^{r+1}D(P)\);
- `formationNumber_associatedGrade`: grade-\(r\) eigenvalue modulo \(I^{r+1}\);
- `laurentFormationDerivative_invert`: exact reflection Jacobian;
- `formationNumber_invert`: exact twisted reflection covariance;
- `formationNumber_reflection_associatedGrade`: commutation on associated grades;
- `derivationInvariant_of_formationConnection_and_inverseGauge`: recovery of ordinary derivative
  closure from `u ∂` and `u⁻¹` closure;
- `not_mem_finiteFormationState_of_hypertranscendentalOver`: exclusion of HT sources from finite
  states closed under both laws;
- `exists_inverseFormationGauge_escape_of_hypertranscendentalOver`: positive inverse-gauge escape
  witness for every finite formation-stable state containing an HT source.

## Verification

Direct check:

```text
lake env lean GaloisForLFunctions/HTGeometry/DifferentialReesFormationSpectrum.lean
```

passed.

Targeted module build:

```text
lake build GaloisForLFunctions.HTGeometry.DifferentialReesFormationSpectrum
```

passed.  No umbrella or full-project build was run.

`#print axioms` reports only Lean/mathlib standard quotient and classical principles:

```text
propext
Classical.choice
Quot.sound
```

No project axiom, `sorry`, `admit`, `opaque`, or `unsafe` declaration occurs in the module.

## Formal meaning

Certificate separates two claims that must not be conflated:

1. formation number is intrinsic associated-graded spectral data;
2. hypertranscendence forces failure of simultaneous finite closure under formation evolution and
   inverse gauge.

It does not identify hypertranscendence with infinite coefficient support or unspecified
topological noncompactness.
