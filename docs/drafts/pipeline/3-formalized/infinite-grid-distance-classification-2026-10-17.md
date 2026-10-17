# Separated polar copies: distance-to-grid classification

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** infinite-grid-tail-rigidity-2026-10-17.md
- **Scope:** Independent BiScaleUncertainty; certified package 3 of 100.

## Exact target

For `T>=2`, derive the nearest logarithmic-grid distance `d(T)` from the two nodes bracketing
`exp T`. A separated nonzero two-copy source satisfying every grid zero exists exactly when
`T` is not a grid node. For `d(T)>0`, every admissible separated copy has normalized energy
at least `exp(-1/2)log(1/d(T))/4`, while an actual smooth compact polar source attains at most
`C+log(1/d(T))`, with one constant `C` independent of `T`.

The class for the unconditional existence endpoint uses correlation radius at most `1/2`;
`T>=2` therefore supplies separation. A more general lower-bound lemma may retain an explicit
support radius and separation condition. Source existence, smoothness, polar balance, and
infinite-grid admissibility must be conclusions of the endpoint.

## Plan

1. Audit current corpus and primary literature; inspect exact reusable APIs.
2. Prove nearest-node geometry, zero-distance obstruction, and both energy estimates on paper.
3. Formalize geometry and source endpoints in disjoint new leaves; derive all analytic inputs.
4. Run leaf checks, scratch axiom audit, umbrella wiring, index generation, and formal lint.
5. Update facts ledger and count one package only after the complete classification is verified.

## Inputs and boundaries

Packages 1–2 supply exact copy expansion, logarithmic translation-increment lower bound,
actual smooth seed, support-aware compression cost, and exact polar-error scaling.
Current search: `/tmp/infinite-grid-distance-current-search.txt`; prior search:
`/tmp/infinite-grid-distance-search.txt`. Logarithmic scaling itself is classical; the target
is the exact center classification and energy law for the entire logarithmic grid.
General polar tails and multiple interfering copies remain separate open problems.

## Proof state

Complete paper proof: `docs/reports/BiScaleUncertainty/InfiniteGridDistanceClassification.md`.
`LogarithmicGridDistance.lean` passed its direct leaf check without diagnostics: the explicit
floor formula is attained, bounds every grid distance, and is positive exactly off-grid.
`InfiniteGridDistanceClassification.lean` contains the general coefficient lower bound,
actual smooth recovery at every off-grid center, and the exact existence equivalence;
its leaf check passed without diagnostics. Neither analytical inputs nor a source-existence
interface remain as assumptions of the construction endpoint. All 15 theorems passed the
scratch axiom audit with only `propext`, `Classical.choice`, and `Quot.sound`. Both modules
are wired; all names appear in the generated API. Global lint reports four concurrent foreign
modules missing umbrella reachability, listed in the paper; neither owned module has an error.

The exact-node no-go has a complete positive survivor: all off-grid centers admit actual smooth
polar sources with logarithmic distance cost. Both paper proof and exact Lean endpoints are complete.

Logs: `/tmp/infinite-grid-distance-{geometry,classification,axioms,index,lint}.log`.
