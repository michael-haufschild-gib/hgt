# Analytic-wall-indexed microstalk functors

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Functorial realization of existing analytic microlocal ranks.

## Target

Index global cellular microstalk functors by actual analytic Stokes walls and specialize them to
coefficient-generated Puiseux branch pairs.

## Dependency-closed paper proof

The analytic wall equivalence supplies a unique cellular label for every phase-zero direction.
Use that label to select the exact global-to-local restriction and directed microstalk functor.
The global exponential boundary restricts to the local exponential germ, so its functor-output
dimension equals the transported analytic micro-rank. Summing active-conormal dimensions over the
actual branch-pair wall set recovers the existing full characteristic multiplicity `2 k d`.

## Lean target

Analytic-wall microstalk functor; rank realization theorem; actual branch-pair global boundary and
analytic-wall functors; functorial full-multiplicity sum.

## Log

- 2026-08-24 — corpus search found scalar analytic micro-ranks and branch-pair multiplicity sums,
  but no analytic-wall-indexed functor producing those modules
- 2026-08-24 — formalized in `StokesAnalyticWallMicrostalkFunctor.lean`; direct Lean check and
  targeted module build pass; all new declarations use only `propext`, `Classical.choice`, and
  `Quot.sound`
