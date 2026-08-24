# Cellular boundary restriction to local Stokes germs

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Functorial bridge inside cellular irregular-RH source data.

## Target

Construct restriction from global cyclic `BoundaryCategory` to the local `GermCategory` at each
wall, then identify restriction of `exponentialBoundary` with `exponentialGerm`.

## Dependency-closed paper proof

Every wall has two incident arcs: its labelled outgoing arc and predecessor arc. Precomposition
with this cospan gives a functor from global entrance-path representations to local cospan
representations. Pointwise finite limits and colimits make restriction exact and additive. For the
alternating exponential boundary, outgoing activity is the wall Boolean label and incoming
activity is its complement, so restricted incidence maps are exactly those of the local
exponential germ.

## Lean target

Cyclic predecessor and inverse laws; local cospan inclusion; exact/additive precomposition
restriction functor; exponential-boundary/local-germ comparison isomorphism.

## Log

- 2026-08-24 — corpus search found both categories and their exponential objects but no functor
  connecting global boundary data to local germs
- 2026-08-24 — formalized bridge in `StokesCellularBoundaryRestriction.lean`; direct Lean check and
  targeted module build pass; all new declarations use only standard axioms (`propext`,
  `Classical.choice`, `Quot.sound`) where needed
