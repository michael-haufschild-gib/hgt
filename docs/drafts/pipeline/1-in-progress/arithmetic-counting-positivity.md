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

Thirty own Lean leaves contain 184 audited public theorems. Signed harmonic
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

All twenty-six own leaves are installed, individually checked and wired into
`ArithmeticCountingPositivity.lean`. `MainTheorems.lean` imports that umbrella;
no umbrella was compiled. All 184 transitive audits use only `propext`,
`Classical.choice`, and `Quot.sound`. Twenty-seven own stage-three proof cards have adjacent
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

Latest closure: sharp conductor-weight summability, zero/unit normalized
mass, and actual harmonic Ramanujan coefficients for every prime pattern.
All six endpoints have standard transitive axioms; scratch 51739 and
canonical 12533 exited zero without diagnostics. Twenty-seven proof cards
plus the finite-set synthesis give twenty-eight own stage-three cards.

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

All 30 own installed leaves are checked, with 184 standard-axiom public
endpoints. Uniform stripping, all-pattern means, the cutoff boundary and
conductor mass have closed paper/source/axiom/canonical audits. Their
transient drafts, logs and closed searches are cleaned. The stripping,
infinite-count, all-pattern-mean and gap-stability first oleans passed
82142, 36233, 4666 and 36820; audits are saved. Preserve all existing oleans.
The cutoff-boundary leaf has no required olean.

The next exact proof is
../2-fully-proven/arithmetic-counting-all-pattern-actual-conductor-coordinates.md.
Its immediate six-endpoint draft is
/tmp/acp-all-pattern-actual-conductor-coordinates-check.lean.
It reuses finite-vector identities pointwise on F_N, then the proved
all-pattern mixed mean and sign-independent quasimode residuals. It claims
actual unit vectors, exact/limiting inner products, projected squared
coordinates, simple windows and actual index sequences for every P.
The first scratch check 77312 passed without diagnostics, with all six
transitive axiom audits containing only standard axioms. The installed
source is written and its canonical check is next. Its actual import of the newly closed
InfinitePrimeCountsHaveAZeroOrUnitConductorMass leaf requires that leaf's
first olean passed 46359, with audit saved. No other missing dependency is known.

The following bounded-window/full-resolvent research plan is preserved in
arithmetic-counting-all-pattern-bounded-spectral-mass.md. The exact actual
spectral sublevel count and finite-energy properness sources were fully
read. Search evidence is /tmp/acp-all-pattern-bounded-energy-count-search.json.
No all-pattern bounded-window or full-resolvent theorem is claimed yet.
The zero-density relative ground/positive-tail balance remains open.

The HKT source-selection module was fully read after its corpus search.
It states universal tower index zero iff RH and the exact von Mangoldt
weight; it supplies no independent positivity producer closing this goal.
It is not imported into the new proofs. No numerical experiment was run.
All broader counting producer obligations remain open; do not mark the
programme complete for this batch.
