# Componentwise-projective total tensor is abelian-exact

## Classification

- Stage: 3 — formalized
- Status: `[LEAN-PROVED]`; exact theorem surface verified
- Scientific status: `[BRIDGE]` / standard homological-algebra infrastructure
- Route: irregular microlocal Riemann--Hilbert foundations
- Novelty claim: none

## Exact claim

Let `P` be a nonnegative chain complex of module presheaves over a commutative
ring presheaf. Total left tensor by `P` preserves finite colimits. If every term
`P_n` is projective, total left tensor by `P` also preserves monomorphisms and is
therefore an exact functor between the abelian categories of nonnegative chain
complexes.

Here “exact” means exact as a functor on the abelian category of chain complexes.
This claim does **not** say that `P ⊗ -` maps quasi-isomorphisms to
quasi-isomorphisms; that distinct K-flat statement still requires a bounded
filtration, cone induction, or spectral-sequence argument.

## Dependency and duplication audit

- `scripts/formal_tools.py research "bounded complex projective total tensor quasi-isomorphism K-flat homological complex"`:
  no corpus theorem proves total-tensor K-flatness or this exactness layer.
- `StokesPresheafComplexTensor.lean` supplies the standard nonnegative total tensor.
- `StokesProjectivePresheafTensorFlat.lean` proves each projective term is
  tensor-flat and its ordinary tensor functor preserves monomorphisms.
- Mathlib expresses total degree `n` as a coproduct over the finite antidiagonal
  `{(i,j) | i+j=n}` and proves a finite coproduct of monomorphisms is mono.
- Chain-complex limits and colimits are computed degreewise.

## Paper proof

Fix a morphism `f : X ⟶ Y` of nonnegative chain complexes. In degree `n`, the
map induced by total left tensor is the finite coproduct, over `i+j=n`, of
`P_i ⊗ f_j`. If every `P_i` is projective, each `P_i` is pointwise flat and
`P_i ⊗ f_j` is mono whenever `f_j` is mono. A finite coproduct of monomorphisms
in the abelian module-presheaf category is mono. Monomorphisms of chain
complexes are detected degreewise, so total left tensor preserves monos.

For finite colimits, form in each degree `n` the functor into diagrams indexed
by the finite antidiagonal, with component `X ↦ P_i ⊗ X_j`. Evaluation at `j`
and ordinary tensor by `P_i` preserve finite colimits. Pointwise detection gives
finite-colimit preservation of the antidiagonal diagram functor, and its finite
coproduct preserves finite colimits. This coproduct functor is naturally
isomorphic to total tensor followed by degree-`n` evaluation. Degreewise
reflection then proves total tensor preserves finite colimits.

An additive functor between abelian categories that preserves finite colimits
and monomorphisms preserves categorical homology, equivalently is exact. Apply
this to total left tensor by `P`.

## Hostile review

- Projectivity is termwise; no projectivity of `P` as an object of the
  chain-complex category is asserted.
- Abelian exactness of an endofunctor on `ChainComplex` does not automatically
  commute with the internal homology of each chain complex.
- Therefore no quasi-isomorphism preservation, K-flatness, derived tensor, or
  derived-category bifunctor is claimed.
- The missing next proof must use bounded filtration/cone induction or a
  convergent first-quadrant spectral sequence, not a typeclass rename.
- No sheafification, enhanced category, arithmetic source, or RH result follows.

## Lean certificate

- Module: `formal/GaloisForLFunctions/HTGeometry/StokesProjectiveComplexTensorExact.lean`
- `totalTensorLeftPreservesMonomorphisms` proves the termwise-projective mono result.
- `totalTensorLeftPreservesFiniteColimits` proves the degreewise antidiagonal result.
- `componentwiseProjectiveTotalTensorLeftPreservesHomology` packages categorical
  homology preservation.
- `componentwiseProjectiveTotalTensorLeft_map_exact` proves preservation of exact
  short complexes.
- Direct Lean check: pass.
- Targeted module build: pass.
- Axiom audit of all 14 declarations created in the module: each depends only on
  `propext`, `Classical.choice`, and `Quot.sound`.
- Authoritative repository lint passed on 2026-08-27; no umbrella build was run.

## RH relevance and boundary

This supplies exactness needed by a future bounded filtration proof, but leaves
the genuine K-flat/quasi-isomorphism step open. It does not supply the
zero-independent arithmetic source required for RH.

## Log

- 2026-08-24 — paper proof and strict exactness/K-flatness distinction recorded
- 2026-08-24 — Lean formalisation completed, checked, targeted-built, and axiom-audited
- 2026-08-27 — Exact abelian-exact tensor surface re-audited; direct check, targeted build, umbrella-wiring lint, and authoritative repository lint pass; promoted to Stage 3.
