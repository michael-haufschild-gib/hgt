# Arithmetic Counting Positivity

- **ID:** ACP-FOUNDATIONS
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** ../../../../docs/reports/review-2810/obstacles-summary.md, sections 2.7–2.8
- **Statement:** Develop independent arithmetic counts producing selective positivity, including all five mechanisms and structural questions in the source report.

## Goal

Own folder and umbrella `formal/GaloisForLFunctions/ArithmeticCountingPositivity`;
foundational README; significant unconditional Lean contributions; full research
scope preserved until the stated mechanisms and questions are resolved. Do not
use `hgtl7`. No numerical experiments or trusted computation proofs.

## Gates

- [x] 0 → 1: source report read; mathematical scope and countermodel battery specified.
- [ ] 1 → 2: dependency-closed paper proofs for individual contributions.
- [ ] 2 → 3: corresponding Lean theorems, foreground `lake --old env lean` audits,
  transitive `#print axioms` checks, umbrella wiring.
- [ ] Complete programme: selective overlap; arithmetic Herglotz; integer-side
  auxiliary counting; finite-rank renormalization; exact inertia counting;
  five structural questions answered; all calibrations and exhaustion proved.

## Approach

Start from exact arithmetic incidence counts, track the signed correlation they
retain, and audit parity twisting before any global positivity claim. Search the
corpus for the sharp walk gap, counting constructions and previously proved
obstructions. Give every new inequality an explicit scope and positive survivor.

## Current evidence

Thirty-three own Lean leaves contain 195 audited public theorems. Signed harmonic
counts pay uniform gaps; exact prime-parity and finite-prime counts identify
their harmonic densities. The parity Ramanujan expansion exhausts unit mass,
with error uniform in the integer horizon. Those counted coordinates determine
the entire actual finite prime-matrix resolvent, hence the exact greatest
single-prime gap `min(2 log 2,alpha_p)`. For p=2,3,5,7 it is the explicit secular
root; every gap is strictly below `p log p/(p+3)`.

The independent valuation-box branch proves maximal attainment for p>=11 in
`LargePrimeFlipsAttainTheMaximalGap.lean`. Preserve that researcher's source and
card. The combined cutoff equivalence and new exact classification audit the
imported endpoint transitively with standard axioms. The user rejected the
redundant p>=41 endpoint; its draft and separate two-mode helper were removed.
Do not recreate them.

Finite flips are positively gapped, whereas every cofinite flip has greatest
gap zero. Their two harmonic exhaustion limits differ. Even maximal discrete
gaps, multiplicativity and polar matching do not select complete Weil
positivity. The failed-route card records its positive survivors, now including
the full single-prime classification.

## Open obligations

All producer mechanisms remain open. An RH-equivalent or quasi-RH-equivalent
estimate is not an available input. Do not close this card merely because a
finite arithmetic construction or README is finished.

## Verification handoff

All thirty-three own leaves are installed, individually checked and wired into
`ArithmeticCountingPositivity.lean`. `MainTheorems.lean` imports that umbrella;
no umbrella was compiled. All 195 transitive audits use only `propext`,
`Classical.choice`, and `Quot.sound`. Thirty own stage-three proof cards have adjacent
`-audit.txt` files with exact commands, source hashes and actual axiom output.

| Own leaves | Public endpoints | Stage-three card stem |
|---|---:|---|
| HarmonicCorrelationPaysThePrimeGap; SparsePrimeFlipsRetainPositiveGaps; PrimeParityPairing; NearMaximalGapsDoNotForceWeilPositivity | 28 | arithmetic-counting-pole-angle |
| PrimeParityRamanujanCoordinates | 7 | arithmetic-counting-prime-parity-ramanujan |
| HarmonicParitySpectralCoordinates | 14 | arithmetic-counting-harmonic-spectral-coordinates |
| FinitePrimeFlipsHavePositiveHarmonicDensity | 6 | arithmetic-counting-finite-prime-density |
| FinitePrimeExhaustionLosesUniformGaps | 5 | arithmetic-counting-finite-flip-exhaustion |
| SmallPrimeFlipsLieBelowTheMaximalGap | 3 | arithmetic-counting-small-prime-gap-boundary |
| PrimeParityIsExhaustedByItsRamanujanTower | 8 | arithmetic-counting-parity-spectral-mass |
| CofinitePrimeFlipsHaveZeroGap | 12 | arithmetic-counting-cofinite-flip-exhaustion |
| TheParityTowerHasAUniqueSecularRoot | 5 | arithmetic-counting-parity-secular-data |
| FiniteReciprocalMassControlsTheHyperplane | 6 | arithmetic-counting-finite-secular-criterion |
| TheParityTowerDeterminesTheFiniteResolvent | 6 | arithmetic-counting-parity-resolvent-limit |
| TheParitySecularRootDeterminesTheGap | 8 | arithmetic-counting-small-prime-secular-gap |
| FinitePrimeFlipsHaveUnitConductorMass | 8 | arithmetic-counting-finite-prime-spectral-mass |
| FinitePrimeCountsDetermineTheConductorCoordinates | 8 | arithmetic-counting-finite-prime-spectral-coordinates |
| FinitePrimeCountsDetermineTheFullResolvent | 4 | arithmetic-counting-finite-prime-resolvent-limit |
| TheFinitePrimeSecularSignsDetermineTheGap | 8 | arithmetic-counting-finite-prime-gap-criterion |
| InteriorSecularRootsForceStrictPrimeGapDecrease | 5 | arithmetic-counting-finite-prime-root-rigidity |
| PrimeTailExhaustionHasVanishingGreatestGaps | 5 | arithmetic-counting-prime-tail-gap-collapse |
| OneDyadicProbeSelectsTheFinitePrimeSource | 3 | arithmetic-counting-dyadic-gap-selection |
| ConductorMassBoundsGapLossAndProbePrecision | 7 | arithmetic-counting-gap-stability-and-probe-precision |
| FinitePrimeConductorMomentsBoundTheGreatestGap | 3 | arithmetic-counting-finite-prime-energy-moment |
| PrimeTailGapsHaveAnInverseLogCubeBound | 3 | arithmetic-counting-prime-tail-gap-rate |
| DivisibilityCountsControlInfinitePrimeFlips | 5 | arithmetic-counting-summable-prime-exhaustion |
| PrimeStrippingHasAnAdditiveHarmonicError | 2 | arithmetic-counting-uniform-prime-stripping |
| EveryPrimePatternHasItsEulerProductHarmonicMean | 4 | arithmetic-counting-all-prime-pattern-harmonic-density |
| PositiveEulerDensityIsExactlyHarmonicCutoffCompleteness | 5 | arithmetic-counting-prime-pattern-cutoff-boundary |
| InfinitePrimeCountsHaveAZeroOrUnitConductorMass | 6 | arithmetic-counting-infinite-conductor-mass-boundary |
| EveryPrimePatternHasActualConductorCoordinates | 6 | arithmetic-counting-all-pattern-actual-conductor-coordinates |
| PrimeCountsDetermineEveryBoundedSpectralMass | 3 | arithmetic-counting-all-pattern-bounded-spectral-mass |
| EveryPrimePatternHasItsFullArithmeticResolvent | 2 | arithmetic-counting-all-pattern-resolvent-limit |

Latest closure: the complete actual resolvent for every prime pattern.
Both endpoints have standard transitive axioms; scratch 37381 and canonical
79210 exited zero without diagnostics. Thirty proof cards plus the finite-set
synthesis give thirty-one own stage-three cards.

Required oleans were built only when an actual new import needed them. Existing
oleans must never be rebuilt. In particular the parity spectral, finite-density,
finite-exhaustion, parity-tower, root-data, finite-criterion, resolvent and
small-prime-boundary oleans exist. The exact-gap leaf has no required olean yet.
Preserve every other researcher's source and artifacts.

## Next research

The finite-set classification is closed in
`../3-formalized/arithmetic-counting-finite-prime-secular-gap.md`. It includes
unit weights, actual coordinate and resolvent transfer, the exact gap
criterion, attainment, the unique interior root and the strict inclusion law.
Qualitative collapse is closed in
`../3-formalized/arithmetic-counting-prime-tail-gap-collapse.md`.
The exact finite-prime selector is closed in
`../3-formalized/arithmetic-counting-dyadic-gap-selection.md`.
Its quantitative precision is closed in
`../3-formalized/arithmetic-counting-gap-stability-and-probe-precision.md`.
Do not infer cutoff-gap convergence merely from pointwise cofinite convergence.
The exact energy moment and gap upper bound are closed in
`../3-formalized/arithmetic-counting-finite-prime-energy-moment.md`.
The explicit prime-tail rate is closed in
`../3-formalized/arithmetic-counting-prime-tail-gap-rate.md`.

The source report was fully reread. It emphasizes arithmetic Krein–Langer,
coalescent pair counts, index-carrying completion and structural precision.
Other researchers own HKT and full separated-Weil spectral work. The original
counting programme stays active; the completed discrete classification does
not resolve its full producer obligations. No numerical experiments; do not
use hgtl7.

## Active formalization

All 33 own installed leaves are checked, with 195 standard-axiom public
endpoints. The full actual-resolvent source, paper, audit, README, umbrella
and positive survivor are saved. Scratch 37381 and canonical 79210 passed.
Bounded spectral mass passed its first required olean 84622. Existing
oleans are preserved. The full actual-resolvent first olean passed
session 38089, exit zero without diagnostics, for the actual draft below.
No other missing dependency is known.

The next complete paper proof is
../2-fully-proven/arithmetic-counting-positive-density-exact-cutoff-gap.md.
Its immediate nine-endpoint draft is
/tmp/acp-positive-density-exact-cutoff-gap-check.lean. Positive density
gives the exact secular gap criterion and equivalence with all finite
cutoff gaps; hence their greatest gaps decrease to the actual greatest gap.
Unconditional greatest-gap attainment is proved directly from the epsilon
definition for every prime pattern, including zero density. The draft has
not yet been checked.

Corpus search for positive-density exact gaps returned the finite-prime
criterion. Its full source and the interior-root continuity source were
read. The draft reuses the finite form isometry and Hermitian reciprocal
criterion pointwise at the exact horizon cutoff. No fixed-support limit
theorem is used on a growing family. All transient completed searches
have been cleaned after recording their mathematical leads on the card.

The absolute zero resolvent limit does not determine eventual sign; the
relative ground/positive-tail balance and zero-density optimal gaps remain
open. The HKT source-selection theorem is a selection criterion, not an
independent positivity producer. No numerical experiment was run. All
broader counting producer obligations remain open; do not mark the
programme complete.
