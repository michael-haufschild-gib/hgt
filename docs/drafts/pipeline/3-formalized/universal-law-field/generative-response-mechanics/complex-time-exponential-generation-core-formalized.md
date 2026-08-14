# Complex-time exponential generation core -- Lean certification

- **ID:** ULF-GRM-3
- **Paper card:**
  `docs/drafts/pipeline/3-formalized/universal-law-field/generative-response-mechanics/complex-time-exponential-generation-phase-recurrence-and-normalization-wall-law.md`
- **Lean modules:** `GaloisForLFunctions.HTGeometry.ComplexTimeGenerativeMechanics`,
  `GaloisForLFunctions.HTGeometry.ComplexTimeEulerShellGeneration`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [HISTORICAL CORE] [SUPERSEDED BY FULL LEAN CERTIFICATION] [NO PROJECT AXIOMS] [NOT RH]

## Certified laws

- finite exponential partition positivity and normalized tilt mass one;
- derivative of partition equals tilted first-moment current;
- derivative of normalized exponential tilt at zero is the centered score tangent;
- centered exponential tangent conserves total probability;
- exact Markov law of total second moment;
- Fisher data processing under every positive row-stochastic kernel;
- zero Fisher loss iff every positive kernel edge preserves the score.
- strict receiver amplification is incompatible with any positive Markov score realization.

The exact identity

```text
source second moment = observed second moment + conditional score loss
```

is the certified conservation law. It gives a falsifiable fourth-organ condition: no positive
observer can report more Fisher second moment than its source.

## Full realization added 2026-08-14

`ComplexTimeEulerShellGeneration` now packages the countable Euler-shell complex partition
`exp(z*mu_sigma) * S_m(sigma+z) / S_m(sigma)`, proves its all-order centered-moment tower, literal
real Gibbs shift, imaginary phase law, countable Fisher conservation/equality, exact negative
lifetime, and divergence at the normalization wall. The full promoted paper card is authoritative;
this companion remains only as the historical record of the earlier finite-core milestone.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ComplexTimeGenerativeMechanics.lean
lake env lean GaloisForLFunctions/HTGeometry/ComplexTimeEulerShellGeneration.lean
lake build GaloisForLFunctions.HTGeometry.ComplexTimeEulerShellGeneration
lake env lean GaloisForLFunctions/HTGeometry/UniversalLawField.lean
```

All checks pass in the foreground. Source-level axiom prints on finite/countable Fisher laws,
source-ratio generation, the derivative tower, wall divergence, and the fusion capstone report only
`propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, custom `axiom`, `opaque`,
`unsafe`, or computation certificate occurs.
