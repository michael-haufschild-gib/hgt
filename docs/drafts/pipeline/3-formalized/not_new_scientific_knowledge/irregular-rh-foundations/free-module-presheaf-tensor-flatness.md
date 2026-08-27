# Free module presheaves are tensor-flat

## Classification

- Stage: 3 — formalized
- Status: `[LEAN-PROVED]`; exact theorem surface verified
- Scientific status: `[BRIDGE]` / standard homological-algebra infrastructure
- Route: irregular microlocal Riemann--Hilbert foundations
- Novelty claim: none

## Exact claim

Let `A : Cᵒᵖ ⥤ CommRingCat` and `F : Cᵒᵖ ⥤ Type`. Tensoring on either
side by the free module presheaf `free(A)(F)` preserves finite limits. Since
module-presheaf tensor already preserves colimits, these tensor functors preserve
homology. Their degreewise maps on nonnegative chain complexes therefore send
quasi-isomorphisms to quasi-isomorphisms.

In particular this applies to every free-Yoneda generator by taking `F` to be a
representable presheaf.

This claim does **not** prove that an arbitrary projective module presheaf is flat,
nor that a bounded complex of projectives is K-flat.

## Dependency and duplication audit

- `scripts/formal_tools.py research "free Yoneda flat tensor exact module presheaf"`:
  no corpus theorem establishes tensor-flatness of free module presheaves.
- `StokesPresheafDerivedTensor.lean` supplies left/right tensor additivity and
  free-Yoneda projectivity.
- Mathlib defines a free module presheaf pointwise as a free module and proves a
  free module is flat.
- Mathlib characterizes module flatness categorically by finite-limit preservation
  of tensor and provides pointwise limit construction/reflection for module
  presheaves.
- Mathlib proves exact additive functors preserve homology and consequently map
  quasi-isomorphisms to quasi-isomorphisms.

## Paper proof

At every `X : Cᵒᵖ`, the value of `free(A)(F)` is the free `A(X)`-module on
`F(X)`, hence is flat. Consider a finite diagram of module presheaves and a limit
cone. Evaluation at `X` preserves the limit. Tensoring the evaluated cone by the
flat module `free(A)(F)(X)` again yields a limit cone. Since the family of
evaluation functors jointly reflects limits, tensoring the original presheaf cone
by `free(A)(F)` yields a limit cone. Thus left tensor preserves finite limits.

Symmetry identifies left and right tensor functors, so right tensor preserves
finite limits as well. Both functors preserve all colimits by the existing
module-presheaf monoidal API. They are additive and preserve finite limits and
finite colimits, hence preserve homology. The standard map-on-complexes theorem
then sends every quasi-isomorphism to a quasi-isomorphism.

## Hostile review

- Pointwise flatness is proved only for free module presheaves.
- A projective presheaf is a retract of a free presentation only after constructing
  and tracking a splitting; that closure step is not asserted here.
- Degreewise tensoring by one fixed free object corresponds to a free cell
  concentrated in degree zero. It is not total tensor by an arbitrary complex.
- Closure under shifts, cones, coproducts, retracts, and bounded totalizations is
  still required for a genuine K-flat class.
- No sheaf/enhanced derived tensor follows from this result alone.

## Lean certificate plan

1. Prove each component of a free module presheaf is algebraically flat.
2. Use evaluation preservation and joint reflection to prove left tensor preserves
   finite limits.
3. Transfer finite-limit preservation to right tensor through the braiding iso.
4. Apply homology preservation to quasi-isomorphisms of nonnegative complexes.
5. Check only axioms of declarations created here; run direct file check and one
   targeted module build.

## RH relevance and boundary

This is the first verified quasi-isomorphism-invariance seed for the Stokes
presheaf tensor route. Extending it from degree-zero free cells to bounded
projective/K-flat complexes and then through exact sheafification remains open.
No arithmetic source theorem is supplied.

## Lean certificate

- Module: `GaloisForLFunctions.HTGeometry.StokesFreePresheafTensorFlat`
- Direct check: `lake env lean GaloisForLFunctions/HTGeometry/StokesFreePresheafTensorFlat.lean`
- Targeted build: `lake build GaloisForLFunctions.HTGeometry.StokesFreePresheafTensorFlat`
- Result: both passed on 2026-08-24; targeted build completed 8663 jobs in 7.8 seconds.
- Created declarations: underlying ring-presheaf and free-module-presheaf
  abbreviations, pointwise flatness, left/right finite-limit preservation, and
  left/right quasi-isomorphism preservation.
- Batched axiom audit of all seven created declarations:
  `[propext, Classical.choice, Quot.sound]`.
- No `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declaration introduced.
- Authoritative repository lint passed on 2026-08-27.
