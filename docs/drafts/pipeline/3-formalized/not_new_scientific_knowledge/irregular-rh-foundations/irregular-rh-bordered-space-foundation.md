# Irregular RH bordered-space foundation

- **ID:** `irregular-rh-bordered-space-foundation`
- **Stage:** 3-formalized
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

## Completed topological checkpoint

`[BRIDGE]` Construct bordered-space objects, strict ambiently extending morphisms, exact general
graph-proper morphisms, and category structure under Hausdorff ambient hypotheses.

## Complete proof of graph-proper composition

Let `C_f ⊆ M̂×N̂` and `C_g ⊆ N̂×P̂` be closed ambient graphs. Form closed fiber product
`F=C_f×_{N̂}C_g`. Properness of `C_g→N̂` is stable under base change, so `F→C_f` is proper;
composing with proper `C_f→M̂` makes `F→M̂` proper. Pairing this map with continuous `P̂`
coordinate gives proper `r:F→M̂×P̂`, hence closed image `R=r(F)`.

Interior graph of `g∘f` lies in `R`, so its closure also lies in `R`. Codomain restriction
`F→R` is a surjective proper map. Properness of `F→M̂` descends to `R→M̂`: for any cluster filter,
pull back along the surjection, use properness upstairs, then map resulting cluster point down.
Finally closed inclusion of closed graph of `g∘f` into `R` is proper, so its projection to `M̂` is
proper. Identity is induced by strict identity ambient extension. Thus Hausdorff bordered spaces and
graph-proper morphisms form a category.

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
- [x] 1 → 2: full graph-proper composition proof dependency-closed on paper
- [x] 2 → 3: full stated foundation is formalized; direct check, targeted build, umbrella wiring,
  prior axiom audit, and authoritative repository lint pass
- [ ] 3 → 4: integrated into enhanced sheaf construction

## Log

- 2026-08-24 — Corpus audit found ordinary sheaves but no bordered/enhanced category. Began strict
  ambient-extension checkpoint before general graph-proper morphisms.
- 2026-08-24 — Added `StokesBorderedSpace.lean`: `TopologicalBorderedSpace`, `ofOpen`, and
  `StrictHom` with identity, composition, unit laws, and associativity. Direct Lean check and
  targeted module build pass. Axiom audit of all three new laws reports only `propext` and
  `Quot.sound`. Card remains in progress: graph-proper morphisms are not yet constructed.
- 2026-08-24 — Added exact closed ambient graph, proper graph-projection predicate, proper base
  change, proper codomain restriction, proper-surjection descent, composition theorem, and
  `HausdorffBorderedSpace` category. Direct Lean check and targeted build pass. Axiom audit of every
  new theorem reports only `propext`, `Classical.choice`, and `Quot.sound`. Promoted paper status to
  Stage 2.
- 2026-08-27 — Full object/strict/general morphism/category surface re-audited; direct check,
  targeted build, umbrella-wiring lint, and authoritative repository lint pass; promoted to Stage 3.
