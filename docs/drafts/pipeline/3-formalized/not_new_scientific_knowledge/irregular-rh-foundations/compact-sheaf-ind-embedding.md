# Compact-sheaf embedding into ind-sheaves

- **ID:** IRRH-COMPACT-IND-EMBEDDING
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Kashiwara–Schapira canonical embedding into `Ind(Modᶜ(k_M))`; mathlib ind-Yoneda
- **Statement:** Compactly supported integer-module sheaves embed fully faithfully and exactly into the ind-sheaf category.

## Goal
Provide canonical coefficient embedding needed before extending sheaf operations to ind-sheaves.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean definitions and theorems in `StokesCompactSheafToInd.lean`, targeted build green, new declarations axiom-audited
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
Pass from the abelian category `Modᶜ(ℤ_Y)` of compactly supported sheaves to its universe-small equivalent category via `AsSmall.up`, then apply the ind-Yoneda embedding into `Ind(AsSmall(Modᶜ(ℤ_Y)))`. Both factors are fully faithful. The universe equivalence preserves all limits and colimits; ind-Yoneda preserves limits and finite colimits. Their composite therefore preserves finite limits and finite colimits, hence is exact between abelian categories.

**[PROVED HERE]** All claims follow from equivalence and ind-Yoneda universal properties.

## Lean realization
- Module: `formal/GaloisForLFunctions/HTGeometry/StokesCompactSheafToInd.lean`
- Embedding: `compactSheafToIndSheaf`
- Fully faithful instances: `compactSheafToIndSheaf_full`, `compactSheafToIndSheaf_faithful`
- Exactness infrastructure: finite-limit, finite-colimit, additive, and homology-preservation instances
- Exact short complexes: `compactSheafToIndSheaf_map_exact`
- Verification: direct `lake env lean`, targeted module build, and `#print axioms` for every new declaration passed. Dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.

## Scope boundary
This embeds compactly supported sheaves only. The standard embedding of every ordinary sheaf into ind-sheaves additionally needs locally compact exhaustion and is not claimed.

## Log
- 2026-08-24 — paper proof completed
- 2026-08-24 — formalized fully faithful exact embedding; direct check, targeted build, and axiom audit passed
