# Ramified top-conormal cocone on actual rational-Witt stages

- **ID:** `deninger-ramified-top-conormal-finite-stage-cocone`
- **Stage:** 3-formalized
- **Paper proof:**
  `../2-fully-proven/new_scientific_knowledge/deninger/deninger-ramified-top-conormal-finite-stage-cocone.md`
- **Lean module:**
  `GaloisForLFunctions.RHTower.DeningerRamifiedTopConormalFiniteStageCocone`

## Formalized capstones

- `DeningerFiniteFrobeniusStageHilbert` and
  `DeningerRamifiedFiniteFrobeniusStageHilbert` retain exact arithmetic
  quotient labels and add one explicit finite conormal grade;
- `deningerRamifiedFiniteFrobeniusStageHilbertGaugePullback_comp` proves
  strict extended gauge-transition composition;
- `deningerRamifiedFiniteFrobeniusStageHilbertGaugePullback_injective`
  proves every extended transition remains faithful;
- `deningerRamifiedFiniteStageGaugePullback_topConormalEmbedding` and
  `deningerTopConormalResidue_ramifiedFiniteStageGaugePullback` prove both
  refinement squares;
- `mem_deningerRamifiedFiniteStageTopConormalAdmittedSector_iff` identifies
  admitted sector exactly with top-conormal embedding range;
- `deningerTopConormalResidue_injectiveOn_admittedSector` and
  `deningerRamifiedFiniteStageGaugePullback_mem_admittedSector` prove
  residue faithfulness and refinement stability;
- `deningerRamifiedFiniteStageToAlgebraic_topConormalEmbedding`,
  `deningerRamifiedFiniteStageToAlgebraic_transition`, and
  `deningerRamifiedFiniteStageToAlgebraic_injectiveOn_admittedSector`
  construct strict coefficient-faithful cocone into literal algebraic
  Calderon--Witt source packet;
- `inner_deningerRamifiedFiniteStageTopConormalEmbedding_left` specializes
  literal conormal dagger to every actual finite stage.

All theorems are unconditional. No Xi location, RH, zero simplicity,
source annihilation, or completed Gamma comparison is assumed.

## Verification

- direct foreground check:
  `lake env lean GaloisForLFunctions/RHTower/DeningerRamifiedTopConormalFiniteStageCocone.lean`
  passed;
- umbrella import added to `GaloisForLFunctions/RHTower.lean`;
- targeted build:
  `lake build GaloisForLFunctions.RHTower.DeningerRamifiedTopConormalFiniteStageCocone`
  passed;
- `#print axioms` on eight finite-stage capstones reports only `propext`,
  `Classical.choice`, and `Quot.sound`;
- module contains no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`;
- global lint remains blocked by six unrelated pre-existing umbrella-reachability
  errors recorded in parent formalization audit.

## Scientific consequence

Local ramified block is no longer conflated with unit-only rational-Witt
stages. Minimal top-conormal thickening now exists on exact stage quotient
labels, respects genuine gauge refinement, has concrete admitted sector,
and lands faithfully in actual algebraic packet used by Calderon--Witt cup.

Remaining theorem is intrinsic-source realization: prove framed
rational-Witt coefficient itself supplies added conormal grade and compare
its cocone with nonannihilating completed Xi Gamma/co-Poisson Cartier
transport. Free thickening alone does not imply this.
