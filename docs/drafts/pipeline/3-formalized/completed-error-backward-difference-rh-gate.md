# Completed-error backward-difference subpower bound forces RH

- **ID:** `completed-error-backward-difference-rh-gate`
- **Stage:** 3-formalized
- **Type:** VALUE RELATION / RH REDUCTION (Lean)
- **Scientific status:** `[FORMALIZATION] [POSITIVE STATEMENT] [NOT AN RH PROOF]`

## Statement

Let

```text
R(h) = 4*sinh(h/2) - sum_{k <= exp(h)} Lambda(k)/sqrt(k).
```

For every integer `n>=2`, Lean proves the exact source identity

```text
W(n) = 2*(1-1/sqrt(2))*sqrt(n)
     + R(log(n)-log(2)) - R(log(n))
     + 2*(sqrt(2)-1)/sqrt(n),
```

where `W(n)=sum_{n/2<k<=n} Lambda(k)/sqrt(k)`. Consequently the requested prime-window
inequality is pointwise equivalent, with no averaging or constant loss, to

```text
R(log(n)-log(2)) - R(log(n)) + 2*(sqrt(2)-1)/sqrt(n)
  <= C_epsilon*n^epsilon.
```

The positive endpoint value is bounded by a fixed multiple of `n^epsilon` for every
`epsilon>0`. Hence the simpler endpoint-free hypothesis

```text
for every epsilon>0, eventually
  R(log(n)-log(2)) - R(log(n)) <= C_epsilon*n^epsilon
```

implies RH.

Pointwise control is stronger than necessary. If

```text
V(n) = max(0,
  R(log(n)-log(2)) - R(log(n)) + 2*(sqrt(2)-1)/sqrt(n)),
```

then either of the following all-epsilon energy conditions also implies RH:

```text
sum V(n)*n^(-1-epsilon) < infinity,
sum V(n)^2*n^(-1-epsilon) < infinity.
```

Thus large positive violations are permitted on sufficiently sparse scales.

## RH leverage

The reduction replaces a moving finite prime sum by a one-sided relation between two values of
one source-defined scalar function. It can therefore be discharged by any future theorem proving
subpower backward variation of `R`; no pointwise prime-window interface is required. The proof
uses the existing axiom-clean dyadic sharp-window continuation and Landau transfer after the exact
value substitution.

The remaining hypothesis is still RH-strength. This card does not claim an unconditional proof
of that subpower value relation.

## Lean implementation

```text
GaloisForLFunctions.RHTower.CCM.CCMSharpPrimeWindow
  sharpPrimeWindowEndpointCorrection_logTwo_logSample
  dyadicWeightedPrimeWindow_eq_main_add_completedErrorDifference
  dyadicWeightedPrimeWindow_upper_iff_completedErrorDifference

GaloisForLFunctions.RHTower.CCM.CCMCompletedErrorDifferenceGate
  riemannHypothesis_of_eventually_completedErrorDifference_upper
  riemannHypothesis_of_eventually_completedError_backwardDifference_upper

GaloisForLFunctions.RHTower.CCM.CCMCompletedErrorVariationEnergyGate
  dyadicWeightedPrimeWindowPositiveExcess_eq_posPart_completedErrorBackwardDifference
  riemannHypothesis_of_completedErrorBackwardPositiveVariationEnergy
  riemannHypothesis_of_completedErrorBackwardPositiveVariationSquareEnergy
```

All touched modules compile. The formal lint gate passes. `#print axioms` for all eight theorem
surfaces reports only `propext`, `Classical.choice`, and `Quot.sound`; there is no project axiom,
`sorry`, `admit`, `opaque`, or `unsafe` declaration.

## Gates

- [x] Exact finite-difference value relation formalized
- [x] Pointwise equivalence to the requested inequality formalized
- [x] Endpoint-free subpower difference criterion implies RH
- [x] Positive-variation Dirichlet-energy and square-energy criteria imply RH
- [x] Narrow build, axiom audit, and formal lint pass
- [ ] Unconditional subpower backward-difference estimate
