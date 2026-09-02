# Nomological geometry and dynamics — Stage-3 formalization ledger

- **Goal:** formalize every paper-proved theorem in this folder without strengthening premises,
  weakening conclusions, or replacing universal statements by finite examples.
- **Started:** 2026-09-02
- **Status:** active

## Corpus-first audit

| Card | Reusable Lean corpus | Exact remaining obligations |
|---|---|---|
| `native-observer-descent-effectivity-and-constitutive-nondetermination-law` | `NativeObserverDescentEffectivityLaw`; `NomologicalHomotopyGeometry.ObserverDescent` | native descent/effectivity package, pointed-fibre exactness interface, Stokes inertia bound, five explicit non-determination witnesses |
| `perfect-defect-motive-five-shadow-law` | cochain/cohomology and graded trace infrastructure; finite-unitary recurrence | bounded finite-complex Euler, supertrace, superdeterminant, positive-modulus cancellation and countermodels |
| `positive-observer-covariance-hypertranscendence-compact-resolvent-law` | `PositiveObserverCovarianceLaw`; `PositiveObserverCompactResolventLaw`; closed-operator infrastructure | derivation-compatible wrapper, graph-action compact-sublevel iff compact resolvent, GNS splitting/escaping lift, complete connected-defect package |
| `restricted-history-completion-and-robust-polynomial-saturation-law` | `WeightedHistoryCompletionBoundaryLaw`; `PowerOrbitAdditiveSaturation`; `IntegerTranslationDifferentialMatroid`; `HurwitzMonodromyClosureLawstackResonanceRankLaw` | COMPLETE — moved to Stage 3; new arbitrary-group completion/open-lift, polar-history, explicit phase/radial, and `(2,2)` rank modules passed targeted checks/builds and axiom audit |

## Verification policy

1. Search Lean corpus with `scripts/formal_tools.py research` before every new declaration family.
2. Check names in `/tmp` with `lake env lean /tmp/<file>.lean`.
3. Check each edited source with `lake env lean <file>` in foreground.
4. Run `#print axioms` only for declarations created by this sweep.
5. Run one final targeted `lake build <module>` per finished module; never build an umbrella.
6. Append finished module imports to `GaloisForLFunctions.HTGeometry` without building umbrella.
7. Move card and add `-formalized.md` companion only after every exact obligation is green.

## Progress

- [ ] Native observer card
- [ ] Perfect defect motive card
- [ ] Positive observer card
- [x] Restricted history card — `3-formalized/nomological-geometry-and-dynamics/restricted-history-completion-and-robust-polynomial-saturation-law-formalized.md`
