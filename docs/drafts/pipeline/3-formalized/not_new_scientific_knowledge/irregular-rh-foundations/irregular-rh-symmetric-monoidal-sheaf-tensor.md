# Symmetric monoidal integer-module sheaves and the Stokes tensor comparison

## Classification

- Stage: 3 — formalized
- Status: `[LEAN-PROVED]`; exact theorem surface verified
- Scientific status: `[BRIDGE]` / standard category-theoretic infrastructure
- Route: irregular microlocal Riemann--Hilbert foundations
- Novelty claim: none

## Exact claim

For every topological space `Y`, integer-module sheaves on `Y` admit the symmetric
monoidal structure obtained by localising pointwise tensor of presheaves at local
isomorphisms. Sheafification is strong monoidal for this structure. The existing
Stokes `sheafTensorFunctor Y`, defined as forget to presheaves, tensor pointwise,
then sheafify, is naturally isomorphic to the canonical monoidal tensor functor.

Consequently the canonical tensor carries mathlib's coherent associator, left and
right unitors, and braiding, while the existing Stokes tensor has an explicit
comparison to it.

This claim is underived. It does **not** construct K-flat resolutions, a tensor on a
derived category, an enhanced-sheaf tensor, or an irregular Riemann--Hilbert
equivalence.

## Dependency and duplication audit

- `scripts/formal_tools.py research "monoidal sheaf category sheafification associator braiding"`:
  the corpus contains the manually defined Stokes `sheafTensorFunctor`, but no
  monoidal sheaf structure or comparison theorem.
- Mathlib's `CategoryTheory.GrothendieckTopology.W.monoidal` proves that local
  isomorphisms are stable under tensor for closed braided coefficient categories.
- Mathlib's `CategoryTheory.Sheaf.monoidalCategory` and
  `CategoryTheory.Sheaf.symmetricCategory` construct the localisation-induced
  monoidal and symmetric structures.
- Mathlib makes `presheafToSheaf` strong monoidal and supplies its tensorator.
- The sheafification adjunction counit is an isomorphism on every sheaf.

## Paper proof

Let `P` be the category of integer-module presheaves on `Y`, `S` the full category
of sheaves, `L : P ⥤ S` sheafification, and `U : S ⥤ P` the forgetful functor.
Pointwise tensor makes `P` symmetric monoidal. Local isomorphisms in `P` are stable
under tensor, so monoidal localisation along `L` equips `S` with a symmetric
monoidal structure and makes `L` strong monoidal.

For sheaves `F,G`, the inverse tensorator gives

`L(UF ⊗ UG) ≅ L(UF) ⊗ L(UG)`.

The counit isomorphisms `L(UF) ≅ F` and `L(UG) ≅ G`, tensored together, give

`L(UF) ⊗ L(UG) ≅ F ⊗ G`.

Their composite is the objectwise comparison from the existing Stokes tensor to
the canonical tensor. Naturality follows from naturality of the strong-monoidal
cotensorator and the sheafification counit. Hence these components form a natural
isomorphism of bifunctors.

The associator, unitors, and braiding are fields of the localisation-induced
symmetric monoidal structure, so all coherence laws are inherited from that
structure rather than reproved ad hoc.

## Hostile review

- The comparison is a natural isomorphism of underived bifunctors, not equality of
  tensors and not a derived equivalence.
- Symmetric monoidal coherence belongs to the chosen canonical tensor. The manual
  Stokes tensor is related to it by the explicit natural isomorphism; no separate
  monoidal-category instance with the manual functor as a definitional tensor is
  asserted.
- Sheafification's strong-monoidal structure and invertible counit are used, not
  inferred from objectwise formulas alone.
- Integer modules satisfy the closed symmetric-monoidal hypotheses required for
  tensor stability of local isomorphisms.
- This closes an underived coherence gap only. It does not advance the arithmetic
  source theorem required for RH.

## Lean certificate plan

1. Expose chosen monoidal and symmetric structures on integer-module sheaves.
2. Define explicitly typed TopCat sheafification and forgetful wrappers so category
   instances remain stable during comparison proofs.
3. Define canonical tensor and its unit, associator, unitors, and braiding.
4. Build the natural isomorphism from the existing Stokes tensor using the inverse
   sheafification tensorator and counit isomorphisms.
5. Prove naturality from cotensorator and counit naturality.
6. Check only axioms of declarations created here; run direct file check and one
   targeted module build.

## RH relevance and boundary

This removes the underived associator, braiding, and unit-coherence gap beneath the
irregular-RH convolution receiver. K-flat or another source-conservative derived
tensor construction remains open. No zero-independent arithmetic producer is
supplied.

## Lean certificate

- Module: `GaloisForLFunctions.HTGeometry.StokesSymmetricMonoidalSheaf`
- Direct check: `lake env lean GaloisForLFunctions/HTGeometry/StokesSymmetricMonoidalSheaf.lean`
- Targeted build: `lake build GaloisForLFunctions.HTGeometry.StokesSymmetricMonoidalSheaf`
- Result: both passed on 2026-08-24; targeted build completed 8660 jobs in 11 seconds.
- Created declarations: typed sheafification/forgetful wrappers, typed manual tensor,
  canonical localisation tensor and unit, associator, unitors, braiding, objectwise
  comparison, and natural comparison.
- Batched axiom audit of all 13 created declarations:
  `[propext, Classical.choice, Quot.sound]`.
- No `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declaration introduced.
- Authoritative repository lint passed on 2026-08-27.
