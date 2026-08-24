# Global wallwise microstalks

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Global-to-local cellular microlocal bridge.

## Target

Microlocalize any global cyclic Stokes boundary object at a chosen wall and compute both directed
microstalk ranks for the alternating exponential boundary.

## Dependency-closed paper proof

Restrict a boundary representation to the two arcs incident to a wall, then apply local cellular
microlocalization. The quotient definition gives the arc-to-nearby-to-vanishing exact sequence for
every object. The global exponential boundary restricts to the local exponential germ, whose two
microstalk ranks are complementary: one is `d`, the other zero, according to wall orientation.

## Lean target

Wallwise microstalk functor; exact local sequence for arbitrary global objects; comparison
isomorphism and left/right rank formulas for `exponentialBoundary`.

## Log

- 2026-08-24 — corpus search found local microstalks and global boundary objects but no composed
  wallwise functor
- 2026-08-24 — formalized in `StokesGlobalMicrostalkRestriction.lean`; direct Lean check and
  targeted module build pass; all new declarations use only `propext`, `Classical.choice`, and
  `Quot.sound`
