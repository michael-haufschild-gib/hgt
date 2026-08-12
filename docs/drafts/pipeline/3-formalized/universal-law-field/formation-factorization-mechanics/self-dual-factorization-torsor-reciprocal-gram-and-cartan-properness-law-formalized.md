# Self-dual factorization and Cartan properness — Lean certificate

- **Source card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/formation-factorization-mechanics/self-dual-factorization-torsor-reciprocal-gram-and-cartan-properness-law.md`
- **ID:** ULF-FFM-2-CORE
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/ConstitutiveSelfDualFactorizationGeometry.lean`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Stage:** 3 — formalized
- **Date:** 2026-08-12

## Certified mechanism

Lean proves four connected laws.

1. `ExactRecoveryFactorization G` is the type of group-valued semantic/lineage pairs with exact
   common recovery. `exactRecoveryFactorizationEquiv` proves this entire fibre is canonically
   equivalent to the gauge group `G`; no carrier scalar appears.
2. For every involutive star-group, adjoint reversal is involutive and
   `exactRecoveryFactorization_reverse_fixed_iff` proves its fixed locus is exactly
   `star s * s = 1`.
3. `semanticGramGauge_mul_lineageGramGauge` proves the two positive algebraic leg reporters are
   reciprocal. `lineageGramGauge_reversal_eq_semanticGramGauge` proves reversal exchanges them.
4. `cartanModeWork x = 4 sinh(x)^2` is nonnegative, even, and zero exactly at zero.
   `eq_zero_of_bounded_cartanPacketWork` proves that a finite radial packet whose work is uniformly
   bounded at every natural formation depth is the zero packet.

This is the first exact ULF formation theorem in which carrier blindness, recovery gauge,
self-duality, positive reconstruction, and global properness occupy distinct typed roles. It does
not construct the arithmetic source map required for RH selection.

## Verification

- Direct foreground check:
  `lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveSelfDualFactorizationGeometry.lean`
- Leaf build:
  `lake build GaloisForLFunctions.HTGeometry.ConstitutiveSelfDualFactorizationGeometry`
- Umbrella build:
  `lake build GaloisForLFunctions.HTGeometry.UniversalLawField`
- Umbrella build passed with 11,840 jobs.
- Axiom audit of classification, reversal fixed locus, reciprocal conservation, and bounded-work
  selection reports only `propext`, `Classical.choice`, and `Quot.sound`.
- No declaration uses `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`.

## Boundary

Lean does not yet certify the paper card's finite-dimensional Hilbert-space singular-value formula,
topological compactness of work sublevels, or recurrence of arbitrary unitary one-parameter groups.
The certified bounded-natural-depth theorem is already a global formation/properness selector once a
source realization supplies its hypotheses.
