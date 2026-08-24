# Compact-support ind-sheaf foundation

- **ID:** IRRH-COMPACT-IND-SHEAF
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Kashiwara–Schapira definition `I(k_M) = Ind(Modᶜ(k_M))`; mathlib stalk exactness and indization
- **Statement:** Compact support, defined by vanishing stalks outside a compact set, is a Serre property of integer-module sheaves; its full subcategory is abelian, and its small indization is Grothendieck abelian.

## Goal
Construct correct coefficient category for ind-sheaves from compactly supported sheaves, avoiding incorrect `Ind` of all sheaves.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean definitions and theorems in `StokesCompactIndSheaf.lean`, targeted build green, new declarations axiom-audited
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
For a sheaf `F` on `Y`, say `F` has compact support when some compact `K ⊆ Y` contains every point with nonzero stalk; equivalently, every stalk outside `K` is zero.

Zero sheaf has compact support with witness `∅`. If `F ⟶ G` is mono and `G` vanishes outside compact `K`, exactness of stalks makes every stalk of `F` a subobject of zero there, hence zero. Dually, quotients preserve the same compact witness. For a short exact sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0`, choose compact witnesses `K₁,K₃`; outside compact `K₁ ∪ K₃`, exact stalk sequence has zero endpoints, so its middle stalk is zero. Thus compact support is a Serre property.

Finite biproducts are extensions of their two factors; compact support is therefore stable under finite products. The full subcategory of compactly supported sheaves is abelian. Passing to a universe-small equivalent category and taking its indization yields an abelian category satisfying AB5 with a separator, hence a Grothendieck abelian category.

**[PROVED HERE]** Proof uses only exact stalks, compactness under finite unions, abelian full-subcategory construction, and indization theorems.

## Lean realization
- Module: `formal/GaloisForLFunctions/HTGeometry/StokesCompactIndSheaf.lean`
- Support property: `HasCompactSupport`
- Serre instances: `hasCompactSupport_closedUnderSubobjects`, `hasCompactSupport_closedUnderQuotients`, `hasCompactSupport_closedUnderExtensions`, `hasCompactSupport_isSerreClass`
- Abelian compact-support category: `CompactlySupportedSheaf`, `compactlySupportedSheafAbelian`
- Ind-sheaf category: `IndSheaf`, `indSheafAbelian`, `indSheafGrothendieckAbelian`
- Derived-category existence: `indSheaf_hasDerivedCategory`
- Verification: direct `lake env lean`, targeted module build, and `#print axioms` for every new declaration passed. Dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.

## Scope boundary
This constructs integer-coefficient ind-sheaves on a universe-zero topological space. It does not yet construct the six operations, ordinary-sheaf embedding, bordered-space quotient, bounded derived category, or enhanced quotient instantiation.

## Log
- 2026-08-24 — paper proof completed; correct compact-support definition and mathlib indization path audited
- 2026-08-24 — formalized Serre, abelian, Grothendieck, and derived-existence layers; direct check, targeted build, and axiom audit passed
