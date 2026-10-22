# CCM first-clock asymptotic Bohr completeness

- **ID:** `ccm-first-clock-asymptotic-bohr-completeness`
- **Stage:** `3-formalized/needs-audit`
- **Type:** THEOREM / source-only RH equivalence with explicit asymptote
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [AXIOM-AUDITED] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent paper card:** `../../2-fully-proven/ccm-first-clock-asymptotic-bohr-law.md`
- **Whole-corpus HT source:** `HTGeometry/SummableSpectrumScrewRecurrence.lean`

## Exact theorem

Let

```text
F(L) = L * ccmPublishedSourceSineCoefficient(L/2, 2*pi/L).
```

Then

```text
(exists continuous Bohr-almost-periodic P : R -> R,
  F(L)-P(L) -> 0 as L -> +infinity) <-> RiemannHypothesis.
```

Left side names only literal published CCM source. It contains no zero-location condition.

Under RH explicit witness is

```text
P(L) = 2 * sum_q (1-cos(gamma_q*L))/gamma_q^2,
gamma_q = Re(xiSpectralPoint q).
```

## New formal mathematics

1. Every nonnegative summable-frequency screw series is Bohr almost periodic, with no frequency
   independence or nonzero-frequency premise.
2. For `L >= 2*pi`, each first-clock moving-denominator term exceeds screw term and error is at most
   `(2/15)*(2*pi/L)^2/gamma_q^2`.
3. Summing over multiplicity-exact Xi divisor gives explicit `O(L^-2)` asymptote.
4. Every point of complete relation-hull interval is approximated by scaled literal source with
   bounded gaps after one threshold.
5. Absolute endpoint equals `4*sum_q gamma_q^-2` exactly when every finite integral relation among
   ordinates has even total coefficient. No simplicity or rational independence.

## Lean implementation

- `formal/GaloisForLFunctions/HTGeometry/SummableSpectrumScrewAlmostPeriodic.lean`
- `formal/GaloisForLFunctions/RHTower/CCM/CCMFirstClockAsymptoticBohrLaw.lean`

Capstones:

```text
isBohrAlmostPeriodic_screwSeries
ccmFirstClockScaledSource_sub_explicitScrew_tendsto_zero_of_rh
ccmFirstClockScaledSourceAsymptoticallyBohrAlmostPeriodic_iff_rh
exists_eventual_window_ccmFirstClockScaledPublishedSource_near_of_rh
ccmFirstClockAsymptoticHullMax_eq_absoluteBound_iff_parity_of_rh
```

Both theorem-area umbrellas import new modules.

## Audit

Green commands:

```text
lake env lean GaloisForLFunctions/HTGeometry/SummableSpectrumScrewAlmostPeriodic.lean
lake env lean GaloisForLFunctions/RHTower/CCM/CCMFirstClockAsymptoticBohrLaw.lean
lake build GaloisForLFunctions.RHTower.CCM.CCMFirstClockAsymptoticBohrLaw
lake env lean /tmp/ccm_asymptotic_bohr_axioms.lean
```

All five audited capstones depend only on:

```text
[propext, Classical.choice, Quot.sound]
```

Corpus lint reaches unrelated pre-existing umbrella failures for `HTGeometry.BohrUniqueness` and
`HTGeometry.CountableSeparableInteractionSaturationLaw`; both new modules are reachable.

## Frontier status

This does not prove RH. It converts RH exactly into a source-only asymptotic dynamical regularity
statement and identifies full conditional value dynamics. Remaining premise is to prove asymptotic
Bohr behavior of literal source without assuming RH, or derive contradiction from its failure.
