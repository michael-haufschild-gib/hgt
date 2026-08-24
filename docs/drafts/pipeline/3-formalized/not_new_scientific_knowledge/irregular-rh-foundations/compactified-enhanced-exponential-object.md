# Compactified enhanced exponential object

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Standard exponential object for compact-base enhanced ind-sheaves.

## Target

Construct the compactified epigraph of a continuous real phase, its integral sheaf, compact-support
and ind-sheaf realizations, degree-zero derived realization, and objects in bounded and unbounded
generated enhanced quotients.

## Dependency-closed paper proof

For continuous `φ : X → ℝ`, the subset of `X × EReal` cut out by `φ(x) ≤ t` is closed because the
extended-real order relation is closed. It contains the positive bordered point and excludes the
negative bordered point. Push the constant integral sheaf on this closed subtype into the ambient
compactification.

When `X` is compact, `X × EReal` is compact, so every sheaf on it satisfies the stalkwise
compact-support predicate by choosing the whole ambient space as support. The compact-support
sheaf therefore embeds in the ind-category, then in degree zero of bounded and unbounded derived
categories, and finally in their generated Verdier quotients.

## Lean target

Compactified epigraph topology and exponential objects at sheaf, compact-support, ind, derived,
bounded-derived, and quotient levels.

## Log

- 2026-08-24 — corpus search found ordinary real epigraph sheaves but no compactified enhanced
  exponential object; paper proof drafted; Lean formalization started
- 2026-08-24 — formalized compactified epigraph topology, translation covariance, and sheaf,
  compact-support, ind, bounded/unbounded derived, and quotient objects in
  `StokesEnhancedExponentialObject.lean`; direct Lean check and targeted module build pass; all new
  declarations use only `propext`, `Classical.choice`, and `Quot.sound`
