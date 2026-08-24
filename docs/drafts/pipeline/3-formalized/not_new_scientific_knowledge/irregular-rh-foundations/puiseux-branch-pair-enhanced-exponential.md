# Puiseux branch pairs as enhanced exponential objects

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Bridge from coefficient-generated Puiseux branch pairs and their
analytic Stokes walls to enhanced ind-sheaf objects.

## Target

Attach actual compactified exponential objects to every distinct branch pair in a finite Puiseux
family and transport cellular wall labels to zero-level enhanced support.

## Dependency-closed paper proof

A distinct branch pair has a nonzero leading difference coefficient at its positive contact
numerator. Substituting those data into the continuous analytic Stokes phase on `Real.Angle`
produces ind-sheaf, unbounded-derived, bounded-derived, and both generated enhanced-quotient
objects. Existing cellular-to-analytic wall equivalence sends every wall label to a phase-zero
direction; phase zero satisfies the compactified epigraph inequality at enhanced level zero.

## Lean target

Branch-pair phase and continuity; objects at every constructed categorical level; analytic and
cellular wall incidence with zero-level support.

## Log

- 2026-08-24 — corpus search found generic analytic phase objects and branch-pair wall realization,
  but no bridge attaching enhanced objects to actual Puiseux pairs
- 2026-08-24 — formalized bridge in `StokesPuiseuxEnhancedExponential.lean`; direct Lean check and
  targeted module build pass; all new declarations use only `propext`, `Classical.choice`, and
  `Quot.sound`
