# Exact sheafification for integer-module complexes

## Classification

- Status: fully proven on paper and formalised in Lean 4
- Scientific status: `[BRIDGE]` / standard sheaf-theoretic infrastructure
- Route: irregular microlocal Riemann--Hilbert foundations
- Novelty claim: none

## Exact claim

For any topological space `Y`, sheafification from presheaves of integer modules on
`Y` to sheaves of integer modules on `Y` is additive and exact. Its degreewise
extension to nonnegative chain complexes therefore maps quasi-isomorphisms to
quasi-isomorphisms.

## Dependency and duplication audit

- `scripts/formal_tools.py research "presheafToSheaf preserves finite limits exact sheafification module presheaf"`
  found no project theorem packaging exact sheafification or its complex-level
  quasi-isomorphism consequence.
- `StokesSymmetricMonoidalSheaf.lean` supplies the typed `topPresheafToSheaf` functor.
- Mathlib's `HasSheafify` instance gives finite-limit preservation.
- The sheafification adjunction makes the functor a left adjoint, hence it preserves
  finite colimits.
- Presheaves and sheaves of integer modules are abelian categories.

## Paper proof

Sheafification preserves finite limits by the left-exact sheafification theorem. As
a left adjoint to the fully faithful inclusion of sheaves into presheaves, it
preserves all existing colimits, hence finite colimits. Preservation of binary
coproducts and zero morphisms makes it additive. For an additive functor between
abelian categories, preservation of finite limits and finite colimits is equivalent
to preservation of categorical homology and exact sequences. Applying the functor
degreewise to nonnegative chain complexes therefore preserves their homology objects,
so it maps quasi-isomorphisms to quasi-isomorphisms.

## Hostile review

- Exact sheafification does not make sheaf tensor exact; tensor still needs flat or
  K-flat inputs.
- This is constant-coefficient integer-module sheafification on a topological site,
  not sheafification of modules over an arbitrary ring presheaf.
- No derived tensor bifunctor, proper-support direct image, enhanced quotient, or RH
  statement follows.

## Lean certificate

- Module: `formal/GaloisForLFunctions/HTGeometry/StokesExactSheafification.lean`
- `topPresheafToSheafPreservesFiniteLimits` and
  `topPresheafToSheafPreservesFiniteColimits` expose both exactness halves.
- `topPresheafToSheafPreservesHomology` and `topPresheafToSheaf_map_exact`
  package exact sheafification.
- `topPresheafToSheaf_map_quasiIso` proves the complex-level consequence.
- Direct Lean check: pass.
- Targeted module build: pass.
- Axiom audit of all nine declarations created in the module: each depends only on
  `propext`, `Classical.choice`, and `Quot.sound`.
- Global lint and umbrella build intentionally not rerun.

## RH relevance and boundary

This closes exact descent through sheafification for future derived tensor models.
It does not close total-tensor K-flatness or the zero-independent arithmetic source.

## Log

- 2026-08-24 — corpus/API audit and dependency-closed paper proof recorded
- 2026-08-24 — Lean formalisation completed, checked, targeted-built, and axiom-audited
