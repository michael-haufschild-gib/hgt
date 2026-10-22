# Integer-string/QED/thermal/zeta six-gauge-class universality law

- **ID:** integer-string-qed-thermal-zeta-six-gauge-class-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated cross-domain closure of integer-string dimensional-QED
  classification, finite Gamma-orbit hypertranscendence, and thermal/QED/zeta superselection
- **Statement:** At every integer string channel, the string class and five exact Gamma-charge
  sectors—scalar QED, spinor QED, their spin-statistics ratio, thermal/de Sitter reconstruction,
  and centered-zeta reconstruction—form six pairwise distinct nonzero
  differential-algebraic multiplicative gauge classes.

## Goal

The corpus has two overlapping classifications. One separates integer strings, scalar QED, and
spinor QED; another separates thermal/de Sitter, the QED spin-statistics/beta class, and centered
zeta. Their shared QED clocks expose a larger finite Gamma-charge atlas, but no theorem checks all
cross-pairs. Classify them together without treating the two old certificates as a conjunction.

## Gates

- [x] 0 → 1 in-progress: integer-string, dimensional-QED, QED clock, finite Gamma-orbit, and
  thermal/beta/zeta terminal components read and corpus-searched
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check
- [x] 3 → 4 novelty audit: post-proof literature search found no collision

## Corpus inputs

- `integerStringDimensionalQED_threeGaugeClassUniversality`
- `hypertranscendentalOver_gammaOrbitProductMero`
- `gammaOrbitProductMero_ne_zero`
- `thermalDeSitterQEDSpinCrossRatioMero_eq_gauge_mul_combinedQED`
- `centeredZetaGammaIntensity_sq_div_phase_eq_positiveFourth`
- nonzero DA-gauge equivalence and quotient-obstruction lemmas

## Proof

**[PROVED HERE]** Use the three translation-orbit representatives
`(1/4, 1/2, 1)` and attach the five charge vectors

`(0,1,0), (0,0,1), (0,-1,1), (0,0,2), (4,0,0)`.

These encode scalar QED, spinor QED, their ratio, thermal reconstruction modulo its explicit
nonzero DA recurrence/exponential gauge, and centered zeta. The vectors are injectively labelled.
For two distinct labels, their difference has a nonzero coordinate. The three shifts are pairwise
separated modulo integer translation, so the finite signed Gamma-product theorem makes the
quotient of the corresponding carriers hypertranscendental. A hypertranscendental quotient
forbids a nonzero DA multiplicative gauge; hence all five Gamma sectors are pairwise inequivalent.

The integer-string theorem makes generalized-spin/open/closed carriers one nonzero DA class.
Every one of the five nonzero charge vectors similarly has a nonzero separated Gamma coordinate,
so its carrier is hypertranscendental and cannot be gauge-equivalent to the DA string class.

The QED definitions identify the first three atlas carriers exactly. The zeta reconstruction is
exactly the fourth power of the quarter-shift carrier. For thermal/de Sitter, multiply the known
thermal/QED cross-ratio identity by the nonzero spin-statistics ratio: the scalar factor cancels,
leaving the explicit nonzero DA cross gauge times the square of the unit-shift spinor carrier.
Thus all physical representatives occupy the six certified atlas classes. ∎

## Strict gain over corpus endpoints

Existing results prove two different three-class partitions and only three of the fifteen
cross-pair separations among the five non-string Gamma sectors. The charge atlas proves every
cross-pair at once and places the DA integer-string class beside them, yielding one six-class
classification across HTGeometry and RHTower.

## Lean formalization

- Charge atlas and carriers:
  `qedThermalZetaGammaOrbitShifts`, `qedThermalZetaGammaOrbitCharges`,
  `qedThermalZetaGammaOrbitCarrier`
- Pairwise theorem:
  `qedThermalZetaGammaOrbitCarrier_pairwiseGaugeSeparated`
- Certificate:
  `IntegerStringQEDThermalZetaSixGaugeClassCertificate`
- Main theorem:
  `integerStringQEDThermalZeta_sixGaugeClassUniversality`
- Module:
  `GaloisForLFunctions.RHTower.IntegerStringQEDThermalZetaSixGaugeClassUniversalityLaw`
- Verification:
  `lake env lean GaloisForLFunctions/RHTower/IntegerStringQEDThermalZetaSixGaugeClassUniversalityLaw.lean`
  passed without warnings.
- Umbrella:
  imported by `GaloisForLFunctions/RHTower.lean`.
- Cache discipline:
  the uncached terminal integer-string module was not built early; its short collapse/nonzero
  certificate was reconstructed from cached lower connectors.

## Novelty audit

Post-proof searches found differential-transcendence results for Gamma functions, physical
Gamma-function formulas in QED and (anti-)de Sitter models, and zeta-regularized effective
actions. No source gives the three-translation-orbit charge atlas or its six pairwise
DA-multiplicative gauge classes spanning integer strings, scalar/spinor QED, thermal/de Sitter,
and centered zeta. Novelty remains a negative-search conclusion, not a claim of bibliographic
completeness.

## Log

- 2026-07-23 — overlapping Gamma-gauge terminal classifications read in full and corpus-searched.
- 2026-07-23 — three-orbit/five-charge atlas and six-class paper proof completed before Lean
  source or literature search.
- 2026-07-23 — exact-file Lean verification passed without warnings; module wired into the
  RHTower umbrella.
- 2026-07-23 — post-proof literature audit found no exact or equivalent classification.
