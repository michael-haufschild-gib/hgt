# Nomological geometry and dynamics — Stage-3 formalization ledger

- **Goal:** formalize every paper-proved theorem in this folder without strengthening premises,
  weakening conclusions, or replacing universal statements by finite examples.
- **Started:** 2026-09-02
- **Status:** complete — every theorem card moved to Stage 3

## Corpus-first audit

| Card | Reusable Lean corpus | Exact remaining obligations |
|---|---|---|
| `native-observer-descent-effectivity-and-constitutive-nondetermination-law` | `NativeObserverDescentEffectivityLaw`; `NomologicalHomotopyGeometry.ObserverDescent`; exact winding, Hurwitz, and multiple-Gamma laws | COMPLETE — moved to Stage 3; full descent/effectivity package, pointed-fibre exactness, exact Stokes inertia bound, and five explicit non-determination witnesses passed targeted checks/builds and axiom audit |
| `perfect-defect-motive-five-shadow-law` | cochain/cohomology and graded trace infrastructure; finite-unitary recurrence; dual-number and flat-holonomy witnesses | COMPLETE — moved to Stage 3; exact five-shadow cancellation, unitary recurrence, five countermodels, and `lim¹(ℤ ←² ℤ ←² ⋯) ≃+ ℤ₂/ℤ` passed targeted checks/builds and axiom audit |
| `positive-observer-covariance-hypertranscendence-compact-resolvent-law` | `PositiveObserverCovarianceLaw`; `PositiveObserverCompactResolventLaw`; closed-operator infrastructure | COMPLETE — moved to Stage 3; literal differential jets, graph-action compactness equivalence, completed GNS splitting, universal periodic lifts, and connected-defect package passed targeted checks/builds and axiom audit |
| `restricted-history-completion-and-robust-polynomial-saturation-law` | `WeightedHistoryCompletionBoundaryLaw`; `PowerOrbitAdditiveSaturation`; `IntegerTranslationDifferentialMatroid`; `HurwitzMonodromyClosureLawstackResonanceRankLaw` | COMPLETE — moved to Stage 3; new arbitrary-group completion/open-lift, polar-history, explicit phase/radial, and `(2,2)` rank modules passed targeted checks/builds and axiom audit |

## Verification policy

1. Search Lean corpus with `scripts/formal_tools.py research` before every new declaration family.
2. Check names in `/tmp` with `lake env lean /tmp/<file>.lean`.
3. Check each edited source with `lake env lean <file>` in foreground.
4. Run `#print axioms` only for declarations created by this sweep.
5. Run one final targeted `lake build <module>` per finished module; never build an umbrella.
6. Append finished module imports to `GaloisForLFunctions.HTGeometry` without building umbrella.
7. Move card and add `-formalized.md` companion only after every exact obligation is green.

Repository-wide `scripts/formal_tools.py lint` was also run after completion.  All modules created
by this sweep are reachable from `GaloisForLFunctions.HTGeometry` and produced no forbidden-
declaration error.  The global command remains nonzero because of pre-existing unrelated
unreachable modules under `GaloisForLFunctions.RHTower` and other HTGeometry work; those modules
were not modified by this scoped formalization.

## Progress

- [x] Native observer card — `3-formalized/nomological-geometry-and-dynamics/native-observer-descent-effectivity-and-constitutive-nondetermination-law-formalized.md`
- [x] Perfect defect motive card — `3-formalized/nomological-geometry-and-dynamics/perfect-defect-motive-five-shadow-law-formalized.md`
- [x] Positive observer card — `3-formalized/nomological-geometry-and-dynamics/positive-observer-covariance-hypertranscendence-compact-resolvent-law-formalized.md`
- [x] Restricted history card — `3-formalized/nomological-geometry-and-dynamics/restricted-history-completion-and-robust-polynomial-saturation-law-formalized.md`
