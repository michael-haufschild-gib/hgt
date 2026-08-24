# Exact functors preserve bounded derived objects

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Generic categorical infrastructure needed to match the bounded
derived categories used in irregular Riemann--Hilbert theory.

## Target

For an exact additive functor `F : C ⥤ D` between abelian categories, prove that the canonical
unbounded derived functor sends canonically bounded objects to canonically bounded objects, and
restrict it to `D^b(C) ⥤ D^b(D)`.

## Dependency-closed paper proof

Let `X` be cohomologically bounded below by `a` and above by `b`. Canonical truncation gives a
cochain complex `K`, strictly supported in degrees `[a,b]`, and an isomorphism `X ≅ Q(K)` in the
unbounded derived category. The degreewise complex `F(K)` is strictly supported in the same range:
outside `[a,b]` its terms are images under `F` of zero objects, and an additive functor preserves
zero morphisms and hence zero objects. Exactness supplies the derived functor `D(F)` and the
canonical factorization isomorphism

`D(F)(Q(K)) ≅ Q(F(K))`.

Transporting strict lower and upper support across this isomorphism proves that `D(F)(X)` has the
same cohomological bounds. Therefore `D(F)` restricts along the full inclusions to a functor
`D^b(C) ⥤ D^b(D)`, with a canonical comparison isomorphism after inclusion.

## Lean status

`StokesExactFunctorBoundedDerived` proves generic preservation of `DerivedCategory.IsGE`,
`DerivedCategory.IsLE`, and `TStructure.t.bounded`, and defines the induced triangulated functor on
`DerivedCategory.Bounded`. `StokesDerivedEnhancedIndPullback` specializes it to compactly generated
ind-sheaves on `X × EReal`. Direct Lean checks and targeted module builds passed. All new
declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-08-24 — paper proof closed; Lean formalization started
- 2026-08-24 — generic and enhanced-ind-sheaf bounded derived functors formalized
