# Enhanced translation autoequivalences

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Categorical packaging of finite enhanced translations.

## Target

Show translation by `c` is an equivalence, with inverse translation by `-c`, at every constructed
sheaf, ind-sheaf, derived, and enhanced-quotient level.

## Dependency-closed paper proof

The established comparison isomorphisms identify translation by zero with the identity and the
composite at parameters `c,d` with translation at `c+d`. Setting `d=-c` and `c=-d` gives both
inverse composites. These two isomorphisms package translation by `c` and translation by `-c` as
an equivalence. No separate associativity-coherence equation is required for this inverse claim.

## Lean target

A generic equivalence constructor for unital/compositional functor families, then translation
autoequivalences for compact sheaves, small models, Ind, unbounded derived, bounded derived, and
both generated Verdier quotients.

## Log

- 2026-08-24 — corpus search found zero/composition comparison isomorphisms but no packaged
  translation autoequivalences
- 2026-08-24 — formalized all seven categorical levels in
  `StokesEnhancedTranslationEquivalence.lean`; direct Lean check and targeted module build pass;
  all new declarations use only `propext`, `Classical.choice`, and `Quot.sound`
