# Projective module presheaves are tensor-flat

## Classification

- Stage: 3 — formalized
- Status: `[LEAN-PROVED]`; exact theorem surface verified
- Scientific status: `[BRIDGE]` / standard homological-algebra infrastructure
- Route: irregular microlocal Riemann--Hilbert foundations
- Novelty claim: none

## Exact claim

Let `A : Cᵒᵖ ⥤ CommRingCat` and let `P` be a projective presheaf of modules over
the underlying ring presheaf of `A`. Every value `P(X)` is a flat `A(X)`-module.
Consequently, tensoring on either side by `P` preserves finite limits and its
degreewise action on nonnegative chain complexes maps quasi-isomorphisms to
quasi-isomorphisms.

This claim does **not** prove total tensor by a bounded complex of projectives is
K-flat, derived descent through sheafification, or any arithmetic source theorem.

## Dependency and duplication audit

- `scripts/formal_tools.py research "projective retract free presentation tensor preserves finite limits"`:
  no corpus theorem proves projective module-presheaf tensor flatness.
- `StokesFreePresheafTensorFlat.lean` proves the free case and supplies the
  finite-limit/quasi-isomorphism proof pattern.
- Mathlib's `PresheafOfModules.freeAdjunction` gives the free-on-underlying
  presentation; its counit is pointwise the usual free-module evaluation map.
- Mathlib's `Projective.factorThru` splits an epimorphism onto a projective object.
- Mathlib's `Module.Flat.of_retract` makes a retract of a flat module flat.

## Paper proof

For `P`, let `U(P)` be its underlying type-valued presheaf and let
`ε : free(A)(U(P)) ⟶ P` be the adjunction counit. At each `X`, `ε_X` sends the
free generator indexed by `p : P(X)` to `p`, so it is surjective. Epimorphisms of
module presheaves are detected pointwise; hence `ε` is epic.

If `P` is projective, factor `𝟙 P` through `ε`. This gives
`s : P ⟶ free(A)(U(P))` with `s ≫ ε = 𝟙 P`. Evaluating at `X` exhibits `P(X)` as
a linear retract of the free, hence flat, module `free(A)(U(P))(X)`. Therefore
`P(X)` is flat by retract closure.

For every finite diagram, evaluation preserves its limit cone. Tensoring the
evaluated cone by `P(X)` preserves that limit because `P(X)` is flat. Evaluation
functors jointly reflect limits, so left tensor by `P` preserves finite limits.
Braided symmetry gives the right-tensor statement. Tensor functors preserve
colimits and are additive, so they preserve homology; degreewise application to
nonnegative chain complexes therefore maps quasi-isomorphisms to
quasi-isomorphisms.

## Hostile review

- Projectivity is used only to obtain a global presheaf splitting; pointwise
  projectivity is neither assumed nor concluded.
- Result concerns tensoring by one projective object concentrated in degree zero.
- No closure under shifts, cones, coproducts, retracts of complexes, or bounded
  totalizations is included.
- No claim about arbitrary complexes of flat objects, K-flat resolutions, sheaves,
  enhanced ind-sheaves, Stokes data, or RH follows.

## Lean certificate plan

1. Define free presentation on the underlying type-valued presheaf and prove it epic.
2. Split it using projectivity and prove pointwise flatness by `Module.Flat.of_retract`.
3. Prove left/right finite-limit preservation from pointwise flatness.
4. Prove left/right quasi-isomorphism preservation for nonnegative complexes.
5. Run direct file check, one targeted module build, and axiom checks only for new declarations.

## RH relevance and boundary

This closes the degree-zero projective-cell step toward a bounded projective/K-flat
tensor calculus. Bounded total tensor and exact sheafification remain open. It
does not supply the zero-independent arithmetic source required for RH.

## Lean certificate

- Module: `GaloisForLFunctions.HTGeometry.StokesProjectivePresheafTensorFlat`
- Direct check: `lake env lean GaloisForLFunctions/HTGeometry/StokesProjectivePresheafTensorFlat.lean`
- Targeted build: `lake build GaloisForLFunctions.HTGeometry.StokesProjectivePresheafTensorFlat`
- Result: both passed on 2026-08-24; targeted build completed 8664 jobs in 21 seconds.
- Created declarations: module/underlying-presheaf abbreviations, canonical free presentation and
  epic instance, projective section and splitting law, pointwise projective flatness, general
  pointwise-flat finite-limit criterion, left/right finite-limit instances, and left/right
  quasi-isomorphism preservation.
- Batched axiom audit of all twelve created declarations:
  `[propext, Classical.choice, Quot.sound]`.
- No `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declaration introduced.
- Authoritative repository lint passed on 2026-08-27; no umbrella build was run.

## Log

- 2026-08-24 — paper proof recorded; Lean formalisation started
- 2026-08-24 — direct check, targeted build, and twelve-declaration axiom audit passed
