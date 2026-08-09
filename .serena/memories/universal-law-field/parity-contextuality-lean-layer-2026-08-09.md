# F_2 graph-incidence / parity-contextuality Lean layer (ULF-CTX-1)

Module: `GaloisForLFunctions.HTGeometry.ConstitutiveParityContextuality`
(wired into `HTGeometry.UniversalLawField`). Card promoted to Stage 3.

## What is now corpus-owned (do NOT rebuild)

- `parityBoundary G : (G.edgeSet → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2)` — the **unsigned incidence
  (boundary) map**. Mathlib has no such map; its `SimpleGraph.incMatrix` is a matrix, and the
  corpus's pre-existing `graphCoboundary` (in `GraphCoboundary.lean`, target `V → V → F`) is the
  *dual* object and is NOT usable for solvability of `∂x = b`.
- `walkParity G p` — mod-two edge multiplicity of a walk; `parityBoundary_walkParity` proves its
  boundary is `Pi.single u 1 + Pi.single v 1`.
- `exists_parityBoundary_eq_iff` (connected G): solvable iff `∑ v, b v = 0`;
  `range_parityBoundary`, `parityCokerEquiv`, `finrank_parityCoker` (= 1),
  `finrank_range_parityBoundary` (= |V| − 1).
- `exists_parityBoundary_eq_on_of_ne_univ`, `properFace_blindness`.
- `two_mul_card_fiber_of_flip` — reusable **halving principle**: a `ZMod 2`-valued observable on a
  finite type flipped by an involution has both fibres of half the size. Gives `card_parityFiber`,
  `card_valueFiber`, `card_parityFiber_fixed` (2^(n−2), independent of the fixed value).
- `card_localLaws`, `card_localLaws_fixed`, `localLaw_marginal_prob` (= 1/2 in ℚ),
  `localLaw_marginal_compatible`, `positive_state_no_global_law`.
- `completeBipartiteGraph.instDecidableRelAdj`, `completeBipartiteGraph_connected`,
  `completeBipartiteGraph_degree_inl/inr` — general (any inhabited finite sides). Mathlib has
  none of these. Also `triangle_contextual`, `peresMermin_contextual`.

## Method notes that cost time

- Surjectivity is proved by **support induction pairing odd vertices along connecting walks**, not
  by a spanning-tree rank argument. Much cheaper in Lean; no matrix inversion.
- Elaboration trap: `Pi.single a 1 v + Pi.single b 1 v` fails to elaborate (the family `M : ι → Type`
  is undetermined). Always ascribe the *whole function*: `(Pi.single a 1 + Pi.single b 1 : V → F) v`,
  then `simp only [Pi.add_apply]`.
- `rw` with a lemma whose LHS contains a proof term (`⟨s(u,w), (G.mem_edgeSet).mpr h⟩`) leaves the
  adjacency as a side goal; pass the proof explicitly (`parityBoundary_single_endpoints G h`).
- `ZMod 2` dichotomy has no mathlib lemma: use `ZMod.natCast_rightInverse` + `interval_cases`
  (`zmodTwo_eq_zero_or_one` is now in the module).
- Current names: `ZMod.natCast_eq_zero_iff`, `Finset.card_filter_add_card_filter_not`,
  `Finset.card_insert_of_notMem`, `SimpleGraph.complete_graph_degree`, `SimpleGraph.connected_top`.
  There is no `SimpleGraph.degree_top`.
- The formal lint gate reported two spurious "owned module unreachable" errors while a concurrent
  agent was mid-edit; re-running cleared them. Do not chase such errors before re-running.
