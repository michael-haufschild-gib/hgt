# Unconditional formalization of every leftover paper card

- **ID:** leftovers-unconditional-formalization
- **Stage:** 1-in-progress
- **Type:** FORMALIZATION PROGRAMME
- **Source:** user attachment `7b8e0d61-b048-4085-aa55-1ca6d2ead9d1/pasted-text-1.txt`
- **Scope:** Every proven theorem in all 14 cards initially in
  `docs/drafts/pipeline/2-fully-proven/leftovers/`, including their referenced paper proofs.

## Completion requirements

Preserve exact statements and constants. Supply every missing mathematical dependency;
do not replace producers with implications assuming their conclusions. No new axioms,
admissions, trusted computation, computations, or raised Lean limits. Search the project
corpus before mathlib or new proof code. Compile each changed leaf directly with
`lake --old env lean`, one foreground process at a time. Audit transitive dependencies
with `#print axioms`. Wire leaves into their owning umbrellas without compiling umbrellas.
Move each card to stage 3 only after every theorem on that card is covered and audited.
Existing unrelated worktree changes must be preserved.

## Inventory and current evidence

| Card | Required completion / current evidence |
|---|---|
| `biscale-dyadic-joint-coercivity-1810` | Exact integer-window upper/lower bounds, tent and additive-only witnesses, realization, and stated perturbation gate. Paper read; Lean coverage not yet audited. |
| `biscale-finite-cycle-recovery-1810` | Arbitrary positive collar recovery, mesh count, actual derivative controls, distant-copy controlled-class obstruction; audit existing singular-energy recovery. Paper read. |
| `biscale-perturbed-incidence-1810` | Exact-incidence exclusion, log gaps, weighted comparison, sharpness, common-model realization, continuum distinction. Paper read. |
| `compact-physical-box-producers` | **DONE, moved to `3-formalized/compact-physical-box-producers.md`.** Exact construction and all limits retained; two new leaves checked, 110 public axiom audits passed, umbrella wired. Referenced report absent; complete convergence proof supplied on card. |
| `nonvacuous-independence-and-polarization-import-law` | Audit small-eigenvalue witness, complete actual Selberg-zeta dictionary and nonvacuous clauses. Historical log reports witness complete; current source audit pending. Import table explicitly an observation. |
| `nyquist-critical-finite-part-2026-10-18` | Finite part, signed broad-test expansion, actual-source classification and witnesses. Existing 591-line leaf inspected: cell discrepancy, nodal finite part, source mass and zero-mean witness are present; continuous primitive and signed broad-test expansion are absent. Header's completion claim is premature. |
| `pm-long-modulus-quadrature` | Actual integrable Möbius producer, exact long/tail quadrature identity and bounded short-head pronic energy. Paper read. |
| `route-e-cofactor-amplified-e3-token-supply` | Exact all-interval supply with all elementary bounds; shared Matomäki–Teräväinen/DI analytic input. Full historical-log and current-source audit pending. |
| `route-e-forbidden-support-e3-stability` | Exact forbidden-support all-interval count with shared analytic input. Full historical-log and current-source audit pending. |
| `route-tt-structural-theorems-2026-10-14` | All actual theorem statements, corrected T3, T5, L7, exact T2 exponent and later proven addenda. Historical coverage list is evidence to investigate, not completion. Explicit conjectures/gapped sketches must stay labelled. |
| `smooth-stein-order-two-autonomous-ade-frequency-rank` | Actual Stein/CR/contact/Reeb geometry, Weinstein input, dimension theorem and ADE hull corollary. Paper read; no theorem-shaped assumptions allowed. |
| `twisted-minimum-principle` | Audit existing TMP and consequence; construct the explicit primal annihilator, corner/Dirichlet/Green ingredients, and audit rigidity claim. Paper read. |
| `verified-height-one-zero-turing-extension` | Exact endpoint `768044885196911/256`, unconditional verified prefix and increment. External Arb/Platt–Trudgian numbers do not constitute Lean proofs; generic implication does not close this card. No computations authorized. Current corpus re-audit pending. |
| `weil-cone-pole-duality-anatomy` | Actual automorphic/Dirichlet/curve Weil functionals and A–C, precise conductor thresholds, and proved spectral addenda. Paper read; generic cone abstractions alone insufficient. |

## Working record

- 2026-10-26: attachment read; 14-card inventory established. Root/formal instructions read.
  Initial broad corpus search was partial and unhelpful; targeted lexical search located
  compensated-producer, Nyquist, and energy-cycle leaves. No absence inference.
- Search evidence: `/tmp/leftovers-existing-leaves-search.json`.
- First active leaf: finish actual convergence and compact-source forms for the compensated
  physical producer, reusing the existing construction. This is one dependency-complete
  card within the full programme; the other 13 remain in scope.
- The missing compensated-producer paper report was not found under `docs/`; its exact
  convergence argument is now written on the original card. A new convergence leaf is
  being checked; no card has been promoted on the basis of uncompiled source.

## Completed physical-producer verification

- New leaf: `BiScaleUncertainty/CompensatedPhysicalProducerConvergence.lean`.
  First direct check reached all declarations and found only elaboration/rewrite errors;
  explicit pointwise powers, function composition reductions and square-zero rewrites
  were repaired. Second direct check (tool session `43673`) exited 0 with no diagnostics.
- Downstream leaf written: `BiScaleUncertainty/CompensatedPhysicalProducerFormLimits.lean`.
  It proves actual source/jump energy limits, beyond convergence in the form error.
  The convergence leaf's missing olean was built successfully (session `77026`, exit 0)
  solely for this import. Downstream direct check (`17384`) found one explicit
  `Iic`-membership elaboration error; repaired, along with two deprecated lemma names.
  Updated-source scratch audit (`24204`) exited 0, no diagnostics. All 110 axiom
  lists contain only `propext`, `Classical.choice`, `Quot.sound`.
  Final direct downstream check (`24077`) exited 0, empty log.
- Both leaves wired into `BiScaleUncertainty.lean`; exact statement audit complete.
  Card moved to stage 3. Global lint: 19 unrelated structural errors, 416 existing
  size warnings; neither new leaf has a diagnostic. Corpus index returns new limits.
- Public declaration inventory so far: `/tmp/leftovers-physical-public-names.json`
  (16 restriction, 67 construction, 21 convergence, 6 downstream declarations).
  Audited scratch source: `/tmp/leftovers_physical_axioms.lean`.
- `scripts/check_axioms.sh` imports the package umbrella and audits unrelated names.
  Use a targeted `#print axioms` scratch file covering every public declaration of
  the exact leaves instead; do not claim that the global script was run.
- Additional corpus leads for the later Nyquist/cycle cards are in
  `/tmp/leftovers-nyquist-kernel-search.json`, `/tmp/leftovers-smooth-autocorrelation-search.json`
  and `/tmp/leftovers-autocorr-increment.json`. No new Nyquist/cycle proof code written.
## Active Nyquist checkpoint

- Nyquist broad-test proof mechanism: freeze the test at each cell's left endpoint.
  The discrepancy contribution is bounded by `6 D Lip(H)/L`, using
  `log n ≤ 2 sqrt(n)` and the existing power-tail bound at exponent `-3/2`.
  Cell oscillations contribute `(2 D + 4 c) Lip(H)/L`, using positivity and
  the power-tail bound at exponent `-2`. This recovers the exact paper constant
  `8 D + 4 c` without differentiating a Lipschitz test. Complete proof record is
  on the card; formalization still pending, no completion or novelty claim.
- Nyquist completion proof now recorded on its stage-2 card, including continuous
  primitive, exact broad-test constant, source classification and witnesses.
  Primitive scratch check (`89244`) reached all declarations, exposing two `0+k`
  reductions, one explicit set-membership elaboration and one rational-expression
  normalization issue. All repaired. Source is now
  `BiScaleUncertainty/NyquistCriticalPrimitive.lean`.
  First olean attempt (`76728`) found a line-broken field-notation elaboration
  issue in the local-integrability helper. Replaced it with typed local facts.
  Recheck/build (`98466`) exited 0 with no diagnostics; primitive olean now exists
  for the cell-bound import. Log `/tmp/leftovers-nyquist-primitive-build.log`.
  Final direct source check and axiom audit remain.
  Cell-error and summable-majorant prototype: `/tmp/leftovers_nyquist_cell_bounds.lean`
  (scratch check now active; imports `NyquistCriticalPrimitive`). Intended module name:
  `NyquistCriticalTestCellBounds`.
  Signed expansion prototype: `/tmp/leftovers_nyquist_broad_tests.lean` (not checked;
  imports planned `NyquistCriticalTestCellBounds`), intended module name
  `NyquistCriticalBroadTests`. Covers arbitrary compact Lipschitz tests and all
  positive scales, both half-line and full-line residual integrals.
  Unused guessed-name probe inventory and obsolete physical draft were removed;
  the actual primitive scratch proof checked the relevant APIs directly.
  Existing Nyquist parent olean is present. No new Nyquist umbrella import yet.
- Source-classification reuse leads: `RHTower.LogWindowPrimeNumberTheorem`
  has `RHTower.WeilOneSided.exists_autoCorr_constants` and `abs_autoCorr_sub_le`,
  proved from source Lipschitz control, with the minus-lag autocorrelation convention.
  Use `autocorr f x = WeilOneSided.autoCorr f (-x)` to transport it, rather than
  duplicate the proof. `ArithmeticCriticalityTheory.ShiftAveragedKernel` has
  `integral_Ioi_eq_half_of_even`. `UnitEnergySmallSources` has
  `autocorr_eq_zero_of_source_radius`, useful for the actual lag-4 witness.
  All three existing oleans were checked present. Source-classification prototype
  is now `/tmp/leftovers_nyquist_sources.lean` (not checked), intended module
  `NyquistCriticalSourceClassification`. It includes normalized correlation,
  source-derived Lipschitz constant, exact mean-square slope, actual rescaled-source
  residual, full quantitative expansion, finite-part and slope limits, both mean
  alternatives and vanishing normalized energy.
  Actual signed-witness prototype `/tmp/leftovers_nyquist_witnesses.lean` is now
  written (not checked), intended module `NyquistCriticalSignedWitnesses`. It proves
  smoothness for every `r : ℕ∞` (not analytic order), nonzero source values, positive
  bump mean, normalized lag-four value `-1/2`, and the connected two-source dichotomy.
- Once primitive olean succeeds: check `/tmp/leftovers_nyquist_cell_bounds.lean`,
  repair and migrate to `NyquistCriticalTestCellBounds.lean`; build its missing
  olean for the broad-test prototype. Continue in dependency order through broad
  tests, source classification and witnesses. Every final project leaf still
  requires direct source check, axiom audit and umbrella wiring before promotion.

## Later-card read-only preparation

- PM corpus search: `/tmp/leftovers-mobius-quadrature-search.json` and
  `/tmp/leftovers-pm-centered-prefix-search.json`. Actual centered prefix is
  `RHTower.pmPowerDampedCenteredDivisorPrefix` in `PMPowerDampedMobiusDiscreteEnergy`.
  Its exact floor identity is in
  `ArithmeticContinuationAndCriticalEnergy/TheEscapeIsATailPhenomenon.lean`.
  `SignedArithmeticEnergyIncidence/ShortIntervalSumsOfTheDampedDivisorCoefficients.lean`
  defines the exact harmonic `moebiusTail` and proves a related centered-prefix
  decomposition, with `density_re_eq_tsum` and the existing `sum_rpow_neg_head_le`
  mechanism. Read the first 240 lines of that leaf and the escape leaf.
  These do not yet certify the requested long-modulus integrable producer.
  No PM source edits or new paper theorem have been made.

- Nyquist cell-bound check `2836` failed only elaboration: missing `NNReal` scope,
  partially applied majorant definition, numeric tail simplification, `0+k`,
  and unspecified integral measures. Repaired in scratch; check `34323` running.
- Further PM reuse: exact `sum_Ioc_mul_natDiv_eq_sum_Icc_Ioc` in
  `BezoutValuationIncidence/HyperbolaCancellationWithDivisorBoundedCoefficients`;
  generic `HTGeometry.integrable_tsum_of_summable_integral_norm` in
  `HTGeometry/L1PeriodizationFourier`. Both statements and proofs inspected;
  existing oleans present. No duplicate generic integration lemma needed.
  Actual PM producer prototype `/tmp/leftovers_pm_integrable_producer.lean` written,
  not compiled: exact floor cutoff, pointwise indicator series, integrability,
  and full signed harmonic-tail integral. PM card remains unfinished.
