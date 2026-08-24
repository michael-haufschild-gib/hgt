# Irregular RH bordered-space foundation

- **ID:** `irregular-rh-bordered-space-foundation`
- **Stage:** 1-in-progress
- **Type:** FOUNDATION / BRIDGE
- **Route:** irregular microlocal Riemann--Hilbert
- **Started:** 2026-08-24

## Goal

Formalize topological category on which enhanced sheaf theory is built.

1. A bordered space is an open embedding `M → M̂`.
2. A strict morphism is a continuous map on interiors with a continuous ambient extension and a
   commuting inclusion square.
3. General bordered morphisms are interior maps whose graph closure has proper projection to source
   ambient space.
4. Prove identities and composition for both layers and prove every strict morphism induces a
   general bordered morphism under exact separation hypotheses.

## Frontier audit

- `[LITERATURE]` D'Agnolo--Kashiwara define a bordered space as a pair `(M, M̂)` with `M` open in a
  good space `M̂`; a morphism is an interior continuous map whose graph closure in `M̂ × N̂` projects
  properly to `M̂`.
- `[CORPUS]` Ordinary `TopCat` sheaves, direct image, inverse image, stalks, and skyscrapers exist in
  Deninger modules.
- `[CORPUS-GAP]` Corpus search found no bordered-space object/category and no enhanced sheaf
  six-operation layer.

## Exact active checkpoint

`[BRIDGE]` Construct bordered-space objects and strict ambiently extending morphisms. Prove strict
identity, composition, unit laws, and associativity. This is an honest subcategory-level foundation;
it is not yet the full graph-proper bordered category.

## Dependency graph

1. `TopCat`, open embeddings, product topology, graph closure, `IsProperMap`.
2. Strict bordered morphism algebra.
3. General graph-proper morphisms and composition theorem.
4. Bordered-site sheaves and proper direct image.
5. Enhanced quotient/convolution.

## Failure boundary

- Ambient extension is sufficient but not necessary for a bordered morphism.
- Do not label strict morphism category as full bordered category.
- Composition of graph-proper morphisms requires proof; it cannot be inherited from ordinary
  continuous maps without the graph-closure argument.
- Open embedding alone does not encode subanalyticity or good-space hypotheses.

## Gates

- [x] 0 → 1: exact object, morphism, and failure boundary recorded
- [ ] 1 → 2: full graph-proper composition proof dependency-closed on paper
- [ ] 2 → 3: full stated foundation formalized, direct build and axiom audit pass
- [ ] 3 → 4: integrated into enhanced sheaf construction

## Log

- 2026-08-24 — Corpus audit found ordinary sheaves but no bordered/enhanced category. Began strict
  ambient-extension checkpoint before general graph-proper morphisms.
- 2026-08-24 — Added `StokesBorderedSpace.lean`: `TopologicalBorderedSpace`, `ofOpen`, and
  `StrictHom` with identity, composition, unit laws, and associativity. Direct Lean check and
  targeted module build pass. Axiom audit of all three new laws reports only `propext` and
  `Quot.sound`. Card remains in progress: graph-proper morphisms are not yet constructed.
