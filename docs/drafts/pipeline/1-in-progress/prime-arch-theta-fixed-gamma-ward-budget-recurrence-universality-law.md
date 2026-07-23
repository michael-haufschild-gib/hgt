# Prime--Arch theta fixed-Gamma Ward/budget/recurrence universality law

## Status

`[LEAN PROVED — LITERATURE AUDITED]`

## Lean-derived conjecture

The substitution `t = exp (2x)` does more than give separate incomplete-Gamma formulas for the
dominant theta source and first Liouville--Gibbs atom. On the single fixed half-line `(1,∞)` it
simultaneously exposes:

1. an all-order exact Ward bridge from every positive even source moment to two consecutive Gibbs
   log-Gamma moments;
2. the half-density clock budget for the first three source Gamma coordinates;
3. the all-positive-order equipartition recurrence, and its rational coefficient consequence, for
   the Gibbs Gamma coordinates.

Thus source moments and Gibbs moments are not independent numerical boxes after Gamma transport:
they form one exact constrained coordinate hierarchy.

## Corpus inputs

- `thetaCuspAtomRawEvenMoment_one_eq_gammaIntegral`
- `thetaCuspLiouvilleGibbsMoment_eq_singleGammaIntegral`
- `thetaCuspAtomRawEvenMoment_succ_eq_liouvilleGibbs`
- `thetaCuspFirstAtomMomentTriple_le_halfDensityBudget`
- `thetaCuspFirstAtomLiouvilleGibbsMoment_succ_equipartition_upper`
- `twelve_mul_thetaCuspFirstAtomLiouvilleGibbsMoment_succ_le`

## New connector

The first two coordinate theorems use the same change of variables and the same integration
domain, but the corpus does not transport the Liouville--Ward source/Gibbs identity, the
half-density budget, and the Gibbs equipartition recurrence into that shared Gamma coordinate.
Doing so yields one universal all-order hierarchy rather than unrelated moment statements.

No numerical computation is used.

## Novelty protocol

Literature search was deferred until the theorem passed

`lake env lean GaloisForLFunctions/RHTower/PrimeArchThetaFixedGammaWardBudgetRecurrenceUniversalityLaw.lean`.

Nearest sources found:

- Berenstein and Hulsey, *Anomalous Bootstrap on the half line*, arXiv:2206.01765, derives
  boundary-anomalous moment recursions for half-line quantum bootstraps;
- Sukumar, *Generalised Virial theorems in Classical and Quantum Physics*, arXiv:1410.5592,
  derives generalized virial/matrix-element relations;
- NIST DLMF §8.8 catalogs standard incomplete-Gamma recurrences;
- Polson, *Incomplete Gamma Representations of the Riemann Xi Function: a Thorin Bernstein
  Framework*, SSRN 6954119 (2026), studies incomplete-Gamma representations of Xi and their
  probabilistic structure.

None states the exact dominant-theta law proved here: one normalized fixed half-line coordinate
hierarchy simultaneously carrying the all-order source/Gibbs Liouville--Ward bridge, the
three-source-coordinate half-density budget, and both sharp and rational all-positive-order Gibbs
recurrences.

## Lean target

`formal/GaloisForLFunctions/RHTower/PrimeArchThetaFixedGammaWardBudgetRecurrenceUniversalityLaw.lean`
