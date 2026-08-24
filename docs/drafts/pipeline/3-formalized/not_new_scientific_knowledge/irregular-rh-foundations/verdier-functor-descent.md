# Functorial descent between Verdier quotients

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Generic quotient calculus for enhanced ind-sheaf operations.

## Target

Given a triangulated functor `F : C ⥤ D` carrying a thick triangulated property `P` into `Q`,
construct the induced triangulated functor `C/P ⥤ D/Q` and its canonical comparison square.

## Dependency-closed paper proof

A morphism belongs to the Verdier class for `P` exactly when one, hence every, distinguished cone
belongs to `P`. If `F` carries `P`-objects to `Q`-objects, triangulatedness carries a distinguished
cone triangle for `f` to a distinguished cone triangle for `F(f)` whose cone lies in `Q`.
Therefore `F` maps the `P`-Verdier class into the `Q`-Verdier class and defines a morphism of
localizers. The localization universal property gives an induced functor `C/P ⥤ D/Q` and a
canonical 2-commutative square with quotient functors. Compatibility with shifts descends through
localization. Since the quotient functor is triangulated and essentially surjective on arrows, the
comparison square implies that the induced functor is triangulated.

## Lean status

`StokesVerdierFunctorDescent` formalizes the Verdier localizer morphism, induced localized functor,
canonical comparison square, shift compatibility, and triangulatedness. Direct Lean check and
targeted module build passed. All declarations use only `propext`, `Classical.choice`, and
`Quot.sound`.

## Log

- 2026-08-24 — paper proof closed; Lean formalization started
- 2026-08-24 — quotient-functor descent formalized and axiom-audited
