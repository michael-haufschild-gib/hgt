# Analytic functorial Puiseux microlocal index

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Categorical realization of existing Puiseux microlocal index law.

## Target

Realize coefficient-generated directed Morse masses and orbit-normalized mixed Hom indices as
finrank sums of actual analytic-wall microstalk functor outputs.

## Dependency-closed paper proof

For each distinct branch pair, analytic decay walls correspond to the directed half of cellular
Stokes walls. At every wall, the analytic microstalk functor rank equals transported cellular
micro-rank. Summing gives contact numerator times root-space dimension. Diagonal branch pairs have
zero contact and are assigned zero mass. Summing pair masses over orbit fibers and dividing by
common cover degree therefore agrees termwise with existing normalized cellular mass, hence with
mixed Hom irregularity times fiber-rank product.

## Lean target

Distinct-pair directed functor-rank sum, total ordered-pair analytic mass including diagonal,
comparison with cellular directed mass, orbit-normalized analytic mass, and exact Hom-irregularity
formula.

## Log

- 2026-08-24 — corpus search found analytic wall microstalk functors and scalar normalized
  Puiseux mass, but no theorem identifying the scalar pairing with actual functor outputs
- 2026-08-24 — formalized in `StokesAnalyticFunctorialMicrolocalIndex.lean`; direct Lean check and
  targeted module build pass; all new declarations use only `propext`, `Classical.choice`, and
  `Quot.sound`
