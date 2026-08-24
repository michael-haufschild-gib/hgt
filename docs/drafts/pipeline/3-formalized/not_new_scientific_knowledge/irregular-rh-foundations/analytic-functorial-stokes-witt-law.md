# Analytic-functorial Stokes--Witt law

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Functorial analytic realization of existing polarized coarea law.

## Target

Express coefficient-generated Stokes pairing, Cartan index, and one-port Witt decomposition using
finrank sums of actual analytic-wall microstalk functor outputs.

## Dependency-closed paper proof

Orbit-normalized analytic functor mass agrees termwise with existing cellular microlocal mass.
Therefore their polarized pairings agree. Existing contact-pairing and coefficient coarea laws
then identify analytic-functorial pairing with orbit contact, rewrite Cartan polarization as
terminal energy plus physical-rank square minus functorial pairing, and yield positive local
channels minus one global rank channel. Rank-zero positivity and graded-channel norm follow from
same coefficient-generated coarea datum.

## Lean target

Analytic-functorial pairing, comparison to cellular and contact pairings, Cartan-index formula,
one-port coarea identity, and complete polarized Stokes--Witt law with analytic functor masses.

## Log

- 2026-08-24 — corpus search found scalar categorical Stokes--Witt law but no version stated using
  actual analytic-wall functor outputs
- 2026-08-24 — formalized in `StokesAnalyticFunctorialWittLaw.lean`; direct Lean check and targeted
  module build pass; all new declarations use only `propext`, `Classical.choice`, and `Quot.sound`
