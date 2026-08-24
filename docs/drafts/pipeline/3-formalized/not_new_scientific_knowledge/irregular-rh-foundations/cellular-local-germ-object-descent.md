# Cellular local-germ object descent

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Exact essential-image characterization for cyclic cospan descent.

## Target

Characterize local Stokes-germ families arising from global cyclic boundary representations and
construct a global object from compatible local data.

## Dependency-closed paper proof

Every global arc appears twice in predecessor-indexed local germs, so the two corresponding arc
stalks are canonically isomorphic. Conversely, choose an isomorphism for every duplicated arc
pair. Use right arc copies as global arc stalks and predecessor germ centers as wall stalks.
Chosen arc isomorphisms followed by local incidence maps define initial arrows; local right
incidence maps define terminal arrows. The boundary quiver has no composable nonidentity arrows,
so these data freely extend to its path category. Explicit cospan isomorphisms recover each input
germ. Thus compatible arc gluing is exactly membership in simultaneous restriction's essential
image.

## Lean target

Compatible-arc predicate, glued quiver prefunctor and boundary object, local and family recovery
isomorphisms, invariance under family isomorphism, and exact essential-image iff theorem.

## Log

- 2026-08-24 — corpus search found faithful/conservative local restriction and exact morphism
  descent, but no object-level essential-image characterization
- 2026-08-24 — formalized in `StokesCellularGermObjectDescent.lean`; direct Lean check and targeted
  module build pass; all public declarations use only `propext`, `Classical.choice`, and
  `Quot.sound`
