# Additive action of enhanced translation pullback

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Coherence infrastructure for enhanced ind-sheaf translation.

## Target

Upgrade finite-translation pullback endofunctors to identity- and composition-compatible additive
actions on small models, ind-sheaves, derived categories, and generated enhanced quotients.

## Dependency-closed paper proof

Inverse image along the identity is the identity by uniqueness of left adjoints. Restriction to
compact support follows by cancelling the fully faithful inclusion. Universe-small transport,
covariant ind-extension, and derived localization preserve the identity and composition
comparisons.

The topological law `T_c ; T_d = T_(c+d)` converts contravariant pullback composition into the
additive functor law (commutativity of real addition removes the order reversal). On Verdier
quotients, lift these derived identity and composition isomorphisms uniquely through localization,
using the canonical comparison squares defining quotient translation.

## Lean target

Identity and composition isomorphisms at compact/small/ind/derived and bounded derived levels,
plus both generated quotient levels.

## Log

- 2026-08-24 — corpus search found topological action and translation endofunctors but no functorial
  action coherence; paper proof drafted; Lean formalization started
- 2026-08-24 — closed identity pullback and derived-identity dependencies; formalized zero and
  composition isomorphisms through small, ind, unbounded derived, bounded derived, and both
  generated quotient levels in `StokesEnhancedTranslationAction.lean`; direct Lean check and
  targeted module build pass; all new declarations use only `propext`, `Classical.choice`, and
  `Quot.sound`
