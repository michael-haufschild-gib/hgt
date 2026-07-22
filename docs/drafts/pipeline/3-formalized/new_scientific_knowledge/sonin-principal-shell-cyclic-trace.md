# Formalization: canonical cyclic trace law for faithful Sonin principal shells

- **ID:** `sonin-principal-shell-cyclic-trace`
- **Stage:** 3-formalized
- **Lean module:**
  `GaloisForLFunctions.RHTower.SoninPrincipalShellCyclicTrace`
- **Source:**
  `formal/GaloisForLFunctions/RHTower/SoninPrincipalShellCyclicTrace.lean`
- **Status:** unconditional; no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`

## Formal theorem surface

- `soninLiveWindowCyclicLogWeight`
- `soninWindowStateCyclicLogTrace`
- `soninWindowStateCyclicLogTrace_compose_comm`
- `soninWindowStateCyclicLogTrace_eq_of_operator_compactEq`
- `soninWindowStateCyclicLogTrace_rotate_three`
- `soninWindowStatePairCyclicTrace`
- `soninWindowStatePairCyclicTrace_comm`
- `soninDiagonalGramFactor`
- `soninGramFactorPrincipalCyclicTrace`
- `soninGramFactorPrincipalCyclicTrace_eq_ite`
- `soninGramFactorPrincipalCyclicTrace_diagonal_eq_log`
- `soninPrimePowerPrincipalCyclicTraceDensity`
- `soninPrimePowerPrincipalCyclicTraceDensity_eq_fluxCoefficient`

## Meaning

Lean proves the identity-displacement logarithmic width is a cyclic trace on the exact faithful
zero/live Sonin normal-state semigroup, not merely on an abstract translation algebra. It is
invariant under compact congruence, extends coefficientwise to the finite algebraic state core,
diagonalizes genuine CCM Gram factors, and returns the exact unsquared von-Mangoldt coefficient
at every prime power.

## Verification

Development check:

```text
lake env lean GaloisForLFunctions/RHTower/SoninPrincipalShellCyclicTrace.lean
```

passed. Final module build and axiom audit are recorded after the final cached audit.

## Scope

This formalizes the principal cyclic/source-value connector. It does not define ordinary trace on
the whole retained principal-relative ideal, attach the Burnol archimedean finite part, prove the
completed lower floor, or prove RH.
