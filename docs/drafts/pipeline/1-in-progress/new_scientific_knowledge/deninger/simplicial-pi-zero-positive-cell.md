# Positive-cell degree-zero invariance in the simplicial model

- **ID:** `simplicial-pi-zero-positive-cell`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) — formalization programme
- **Blocks:** `deninger-selective-positive-cell-h0-preservation` (its `(1)`--`(2)`, `(4)`--`(6)`)
- **Statement:** In simplicial commutative rings, `π₀` preserves pushouts, the free algebra on a
  `1`-connective object has `π₀` the unit, and therefore `π₀(A /\!/ K) ≅ π₀ A`.

## Why this card exists

`deninger-selective-positive-cell-h0-preservation` states `(2)` for connective `E_∞`-ring spectra in
a presentable symmetric monoidal stable `∞`-category.  mathlib has no `∞`-categories, no
`E_∞`-algebras, and no `t`-structures, so that formulation is not writable.  **The card's own
hypotheses are satisfied by simplicial commutative rings**, which mathlib *can* express, and in that
model the proof is adjoint-functor theory rather than higher algebra.

## Key observation making this tractable

`π₀ : sCommRing ⥤ CommRing` is **left adjoint** to the constant-simplicial-object functor.  Left
adjoints preserve colimits, hence pushouts — and mathlib has the adjoint/colimit machinery
(`CategoryTheory.Adjunction.leftAdjoint_preservesColimits`).  So the card's connective pushout
formula `π₀(A' ⊗_A A'') ≅ π₀A' ⊗_{π₀A} π₀A''` is a corollary rather than a theorem to be built from
scratch.

## Decomposition

1. `SimplicialCommRing := SimplicialObject CommRingCat`, with its category structure.
2. `π₀` as the coequalizer of the two face maps `d₀, d₁ : A₁ ⇒ A₀`; functoriality.
3. **`π₀ ⊣ const`**, hence `π₀` preserves colimits, hence pushouts.  **First target.**
4. Connectivity: define `1`-connective (`π₀ K = 0`) and show the free simplicial commutative algebra
   on such a `K` has `π₀` equal to the unit — the positive symmetric powers contribute nothing in
   degree zero.
5. Assemble `(2)`: `π₀(A /\!/ K) ≅ π₀A ⊗_{π₀ Free⁺(K)} π₀(1) ≅ π₀ A`.
6. The equivariant universal property and `(4)`--`(6)` follow as they do in the graded shadow
   already formalized (`DeningerPositiveCellEquivariance`, `DeningerDegreeZeroCell`).

## Log
- 2026-08-14 — created; replaces "needs `∞`-categories" with a model mathlib can express.
