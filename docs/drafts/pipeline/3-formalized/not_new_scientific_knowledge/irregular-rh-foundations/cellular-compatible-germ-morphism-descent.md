# Compatible local-germ morphism descent

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Exact morphism-level essential-image characterization.

## Target

Prove global cyclic boundary morphisms are equivalent to families of local germ morphisms whose
two copies of every shared arc component agree.

## Dependency-closed paper proof

Each arc occurs twice among predecessor-indexed local germs: as one germ's left object and the
successor germ's right object. A global morphism therefore produces equal components on those two
copies. Conversely, a compatible local family supplies one map on every arc and one map on every
wall. Local naturality gives naturality for every incidence arrow; the boundary path category has
no nontrivial paths of length greater than one. Faithfulness gives uniqueness.

## Lean target

Compatibility predicate; canonical compatibility; lift to a global natural transformation;
restriction-after-lift and lift-after-restriction laws; Hom equivalence.

## Log

- 2026-08-24 — all-local restriction proved faithful/conservative; corpus search found no exact
  characterization of its morphism image; formalization started
- 2026-08-24 — necessary duplicated-arc compatibility law formalized and promoted separately;
  sufficiency construction reduced to dependent transport across `nextWall_prevWall` in the
  `BoundaryQuiver` type synonym; no mathematical obstruction found
- 2026-08-24 — resolved dependent transport using `CategoryTheory.Paths.liftNatTrans`; formalized
  canonical lift, restriction-after-lift, unique-lift equivalence, and Hom equivalence in
  `StokesCellularGermCompatibility.lean`; direct Lean check and targeted build pass; all new
  declarations use only `propext`, `Classical.choice`, and `Quot.sound`
