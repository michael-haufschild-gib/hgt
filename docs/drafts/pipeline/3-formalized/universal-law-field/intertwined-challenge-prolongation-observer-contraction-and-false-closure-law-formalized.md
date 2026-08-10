# Intertwined challenge prolongation and false closure — Lean certification

- **ID:** ULF-ALG-3
- **Paper card:**
  `../../2-fully-proven/universal-law-field/intertwined-challenge-prolongation-observer-contraction-and-false-closure-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveChallengeProlongation`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified mechanism

For vector spaces over an arbitrary field, promoters `D,E`, observer `q`, and exact intertwining
law `q.comp D = E.comp q`, Lean certifies:

1. `map_challengeProlongation` — every promoted challenge transports exactly;
2. `map_challengeCombination` — every finite coefficient packet transports exactly;
3. `map_challengeSpace` — the image of the source challenge span is exactly the observed span;
4. `finrank_challengeSpace_observer_le` — finite challenge rank cannot increase;
5. `observerRelation_iff_hiddenKernel` — `P(E)qv = 0` iff `P(D)v` lies in `ker q`;
6. `observerRelation_reflects_of_injectiveOnChallengeSpace` — local faithfulness reflects every
   recurrence at the current horizon;
7. `exists_hiddenChallenge_of_observerDependence` — source independence plus observed dependence
   produces a nonzero hidden source challenge in `ker q`;
8. `constitutiveChallengeProlongation_closed` — unconditional capstone.

This is the linear observer data-processing law required by ALG Law V.  It identifies exact lost
challenge content rather than assigning a scalar information loss.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveChallengeProlongation.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveChallengeProlongation
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Direct elaboration and the owned-module build pass without warnings.  `#print axioms` on transport,
rank contraction, kernel equivalence, hidden-witness, and capstone declarations reports only
`propext`, `Classical.choice`, and `Quot.sound`.  No project axiom, `sorry`, `admit`, `opaque`,
`unsafe`, numerical computation, or unresolved premise is used.

## Exact scope

Krylov/prolongation spaces and observability are classical parents.  The theorem does not derive
the promoter from a failure, does not cover nonlinear doctrine revision, and does not establish an
RH result.  The next field gate is source-normal promoter birth plus a law forcing surviving hidden
residuals to become new legal challenges.
