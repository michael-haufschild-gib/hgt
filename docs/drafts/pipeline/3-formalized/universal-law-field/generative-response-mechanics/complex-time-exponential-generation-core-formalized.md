# Complex-time exponential generation core -- Lean certification

- **ID:** ULF-GRM-3
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/generative-response-mechanics/complex-time-exponential-generation-phase-recurrence-and-normalization-wall-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ComplexTimeGenerativeMechanics`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-CERTIFIED CORE] [NO PROJECT AXIOMS] [FOUR-ORGAN MECHANISM] [NOT RH]

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

## Formal boundary

Lean does not yet package the countable Euler-shell complex partition
`exp(z*mu_sigma) * S_m(sigma+z) / S_m(sigma)` or prove its maximal real domain. This card certifies
the universal finite mechanism, not the entire analytic realization.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ComplexTimeGenerativeMechanics.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Both commands pass in the foreground; the umbrella build completes 11,610 jobs. Source-level axiom
prints on exponential-tilt differentiation, exact Fisher conservation, data processing, and the
strict-amplification no-go report only `propext`, `Classical.choice`, and `Quot.sound`. Repository
formal lint passes. No `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, or computation
certificate occurs.
