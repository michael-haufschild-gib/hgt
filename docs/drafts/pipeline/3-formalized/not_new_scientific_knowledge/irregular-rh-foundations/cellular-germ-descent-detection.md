# Cellular germ descent detection

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Exact and conservative global-to-local cellular descent layer.

## Target

Restrict a global cyclic Stokes boundary representation simultaneously to every wall germ and
prove local germs jointly detect global morphisms and isomorphisms.

## Dependency-closed paper proof

Every global arc occurs as the right object of its own predecessor-indexed germ, and every wall
occurs as the central object of its predecessor germ. Hence equality of all restricted natural
transformations implies componentwise equality globally. Likewise, if every restricted morphism
is invertible, every global component is invertible, so the original natural transformation is an
isomorphism. Limits and colimits are pointwise, making simultaneous restriction exact/additive.

## Lean target

Local-germ family category; simultaneous restriction functor; finite-limit/colimit preservation,
additivity, faithfulness, reflection of isomorphisms; exponential-family comparison.

## Log

- 2026-08-24 — corpus search found individual local restrictions but no simultaneous descent or
  conservativity result
- 2026-08-24 — formalized in `StokesCellularGermDescent.lean`; direct Lean check and targeted
  module build pass; all new declarations use only `propext`, `Classical.choice`, and `Quot.sound`

## Survivor

All-local restriction loses no global morphism or isomorphism. Essential-image/fullness
compatibility remains separate and is not claimed here.
