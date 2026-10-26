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

## Current checkpoint (authoritative over chronological notes)

- No full card is certified complete after recovered-report scope audit.
- Active Lean: `87480`, quantitative Nyquist scratch plus 79 axiom queries;
  `/tmp/leftovers-nyquist-quantitative-check.log`.
- Nyquist canonical successful oleans: Primitive, TestCellBounds, BroadTests,
  SourceClassification. Do not rebuild these. PrimitiveTail has a successful
  final source check and no olean. All five are wired into the umbrella.
- Physical retains 110 audited declarations; three supplementary unchecked
  drafts in `/tmp/leftovers_physical_{tail_identity,quantitative,form_bounds}.lean`.
- PM has four unchecked drafts in `/tmp/leftovers_pm_*.lean` (producer, sampling,
  decomposition, short energy). No canonical PM files yet.
- Next dependency order: quantitative Nyquist check/fix → its canonical olean
  for witness → signed witnesses and remaining exact-source/axiom audits.
  Finish physical supplements and PM, then remaining eleven cards.
- Superseded Nyquist source-classification and primitive-tail scratch copies
  removed; canonical sources are authoritative. Existing pending drafts retained.

## Inventory and current evidence

| Card | Required completion / current evidence |
|---|---|
| `biscale-dyadic-joint-coercivity-1810` | Exact integer-window upper/lower bounds, tent and additive-only witnesses, realization, and stated perturbation gate. Paper read; Lean coverage not yet audited. |
| `biscale-finite-cycle-recovery-1810` | Arbitrary positive collar recovery, mesh count, actual derivative controls, distant-copy controlled-class obstruction; audit existing singular-energy recovery. Paper read. |
| `biscale-perturbed-incidence-1810` | Exact-incidence exclusion, log gaps, weighted comparison, sharpness, common-model realization, continuum distinction. Paper read. |
| `compact-physical-box-producers` | **REOPENED after recovered-report audit.** Main construction and limits retain 110 clean axiom audits; card returned to `2-fully-proven/leftovers`. Exact two-tail identity and additional quantitative corollaries from the original report still require completion. |
| `nonvacuous-independence-and-polarization-import-law` | Audit small-eigenvalue witness, complete actual Selberg-zeta dictionary and nonvacuous clauses. Historical log reports witness complete; current source audit pending. Import table explicitly an observation. |
| `nyquist-critical-finite-part-2026-10-18` | Finite part, signed broad-test expansion, actual-source classification and witnesses. Existing 591-line parent inspected. Primitive, signed cell bounds, exact broad tests and source classification pass Lean. Primitive-tail leaf passes its final direct check. Quantitative energy/local-uniform source draft is checking with 79 axiom queries; signed witness is drafted. No complete-card certificate yet. |
| `pm-long-modulus-quadrature` | Four complete unchecked prototypes: actual integrable Möbius producer, exact integer sampling, all-cutoff long/tail decomposition, exact square-root-head pronic bound. Endpoint formula retains tail past max(n,D). |
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

- Cell check `34323` reached all declarations. Numeric bounds passed; repaired
  integral function elaboration with typed sum/difference integrability facts,
  supplied width positivity explicitly, and used `abs_add_le`. Canonical leaf
  is now `BiScaleUncertainty/NyquistCriticalTestCellBounds.lean`; missing olean
  build `48915` active for its downstream broad-test import.
- PM sampling prototype `/tmp/leftovers_pm_sampling.lean` written, not compiled;
  uses the existing exact hyperbola-swap theorem, retains every positive integer
  sample and the entire harmonic tail. Intended imports are the producer leaf
  `ArithmeticContinuationAndCriticalEnergy/LongModulusIntegrableProducer` and
  the existing hyperbola-cancellation leaf. No PM olean built or source promoted.

- PM exact-decomposition prototype `/tmp/leftovers_pm_exact_decomposition.lean`
  written, not compiled. It supplies the unconditional all-cutoff prefix identity
  and the long-sawtooth/full-tail identity when the natural cutoff lies below `n`.
  The first prototype now exposes `pmLongModulusIndicatorTerm` publicly, so its
  exact series statement does not leak a private definition. All PM drafts remain
  `/tmp` prototypes; no completion claim.

- Nyquist cell-bound olean build `48915` exited 0, empty log. The exact
  summable majorant and signed cell bound are kernel checked. Broad-test scratch
  `/tmp/leftovers_nyquist_broad_tests.lean` is now checking.
- PM short-head search found `abs_oscillatingShortSawtooth_le` and
  `pronicNorm_oscillatingShortSawtooth_le`; these use `oscillatingSmoothPower`,
  whose coefficient definition must be checked before reuse for actual Möbius.
  Their public generic bound `sum_sq_le_of_abs_le_sqrt_rpow` may discharge the
  exact pronic constant even when the oscillating coefficient is different.

- PM oscillating coefficient is `d^(-ε) cos(t log d)`, not Möbius; do not
  identify it with the actual source. Reuse only the public generic
  `sum_sq_le_of_abs_le_sqrt_rpow`, whose exact pronic constant was inspected.
  `/tmp/leftovers_pm_short_energy.lean` now supplies the actual Möbius finite-head
  bound, exact floor-square-root exponent (including `n=0`) and all-horizon
  energy. Uncompiled. It imports the existing generic majorant leaf (olean
  present), not the large oscillating-source leaf (olean absent).
  Four PM prototypes cover the complete paper statement; they remain unchecked.

- Broad-test scratch check `57515` failed only two local elaboration details:
  explicitly typed `G`'s integrability with Lebesgue measure and reduced the
  function application before the zero-kernel rewrite. Canonical leaf now
  `BiScaleUncertainty/NyquistCriticalBroadTests.lean`; missing olean build `11180`
  active for source classification. Source-classification and witness drafts
  remain uncompiled. Superseded primitive/cell scratch files removed safely.
- Later dyadic-card audit: `FiniteHorizonPositiveCoercivity.doubling_window_coercivity`
  supplies the stronger upper bound `6N` on all integer windows. Read its
  statement and relevant path/native-edge arguments, plus the entire
  `FiniteHorizonCoercivityClassification` leaf. Its cosine witness only supplies
  lower constant `N/6144` for `N≥1024`, so it does not discharge the paper's
  exact dyadic tent or `N/4096` bound on all `N=2^(h+4)-1`. No dyadic source edits.

- Dyadic read-only follow-up: native energies and `biScaleJointEnergy_eq_zero_iff_const`
  inspected in `UniversalRamanujanCovarianceAndBiScaleRigidity` (lines 575–680).
  Two long semantic queries returned partial results with semantic deadline errors;
  short rephrasings completed. Returned tent hits do not establish the requested
  integer-mantissa tent. Scoped lexical energy and variance searches are saved
  under `/tmp/leftovers-*-lexical.json`. No absence claim.
- Possible later tent proof mechanism (not yet implemented): define the normalized
  triangle on each dyadic level; prove increment bound `1/q` for `q≤n<2q`.
  Since `n(n+1)<4q²`, its squared increments are at most `4/(n(n+1))`.
  The root increment is zero; telescoping from `n=2` gives the paper's strict
  additive energy bound `<2` without reindexing every complete level. Exact
  high/low last-level counts still required for `N/4096`. This is a planning
  observation, not a new theorem certificate or replacement of the requested witness.

- The next Nyquist source prototype's half-line integral now explicitly types
  Lebesgue integrability, avoiding the same elaboration error just found in
  broad tests. `exists_autoCorr_constants` was rechecked: its constant is
  source Lipschitz bound times `∫|f|`, then normalization divides by `∫f²`.
- Dyadic common-model lead `ArithmeticEdgeSieveFamily.signal_realization` was
  inspected, but concerns prescribed arithmetic edge coordinates rather than
  arbitrary integer window values; it is not yet accepted as the requested
  common-window realization. Further inversion searches pending.

- Broad-test olean build `11180` exited 0, empty log. Exact signed expansion
  holds for every compact Lipschitz test and all positive scales, in half-line
  and full-line forms. Source prototype corrected two visible issues before
  checking: target the lag variables in `abs_sub_comm`, and supply nonzero
  squared value (rather than positivity) to the compact-integral positivity API.
  Canonical broad source and olean retained; final direct audit remains.

- Current owned Lean command: source-classification scratch check `59754`,
  log `/tmp/leftovers-nyquist-sources-check.log`; it imports the successfully
  built broad-test leaf. All search sessions from this batch have completed.
  Three checked Nyquist leaves are now wired into `BiScaleUncertainty.lean`;
  no umbrella compilation. Broad scratch removed after byte comparison with
  the canonical checked source. Final direct checks and axiom audit remain.
- PM card now labels its old significance deferral as historical and records
  current authorization and unverified prototypes. No mathematical statement
  or gate was weakened or marked complete.

## Recovered report audit

- Missing current-tree reports exist in Git history. Both were deleted by
  `80971df8c`; their latest retained text is at `727dc15d1`. Read the full
  Nyquist report there. It additionally states: primitive error is absolutely
  integrable with exponential tails; every source Lipschitz constant gives the
  explicit normalized constant `K_f ∫|f|/∫f²`; exact first-moment energy bound;
  locally uniform normalized correlation convergence; `|H|≤1`; and the signed
  witness's negative lag occurs at `4L`. Existing drafts do not yet expose all
  these statements, so Nyquist promotion remains blocked on their formalization.
  This is additional required coverage, not a weakened theorem.
- The physical report at the same commit is being re-audited against its
  completed certificate. Its stage-3 status must be reconsidered if that
  report contains an uncovered theorem. No claim of exhaustive historical
  report coverage should be made until this comparison is complete.

- Full physical report read at `727dc15d1`. Its additional explicit claims are
  not all covered by the 110 audited declarations: equation (14), separate tail
  limits, square-root norm and derivative bounds, physical-interval uniform
  convergence and combined exact-coefficient form bounds. Card moved back to
  stage 2 and status corrected. Existing checked proofs and umbrella imports
  retained. No card is now certified complete for the recovered full-report
  scope; finish these corollaries before restoring physical promotion.
- Source scratch `59754` exited 1: only missing `integral_div_const`, a lower
  neighborhood orientation and one redundant `ring`. Repaired, then expanded
  the source leaf with exact source-derived Lipschitz constants, pointwise
  normalized scaling and every-source-Lipschitz-constant error bound. Canonical
  `NyquistCriticalSourceClassification.lean` (250 lines) is building in `27290`;
  log `/tmp/leftovers-nyquist-sources-build.log`. No other Lean process owned.

- Source build `27290` exited 1 with two elaboration errors: continuous-map
  coercion prevented the autocorrelation bridge rewrite, and a beta-redex
  prevented the normalized-scaling rewrite. Both repaired by explicit `change`;
  redundant sequential tactic removed. Retry `57154` is running, log still empty.
- New unchecked Nyquist drafts: `/tmp/leftovers_nyquist_primitive_tail.lean`
  (absolute tail admission, exponential absolute-integral bound, uniqueness,
  exact width-dependent cell variation), `/tmp/leftovers_nyquist_source_quantitative.lean`
  (absolute normalized bound, exact energy identity/ceiling for every source
  Lipschitz constant, bounded-interval uniform convergence, mean-zero iff).
  Witness draft extended with support-boundary vanishing, exact mass/lag, and
  normalized negative lag `4L`; now imports planned quantitative leaf.
- Physical historical-report follow-up: existing `PhysicalBoxProfile` directly
  proves local absolute continuity, a.e. derivative, and L² membership;
  `PhysicalBoxAverage.physicalBoxDerivative_norm_le` supplies the derivative norm.
  Reuse these, do not re-prove generic box regularity. Exact two-tail draft
  `/tmp/leftovers_physical_tail_identity.lean` now contains the general interval
  identity, specified exponential truncation identity, separate squared/norm
  tail limits and complete separate-tail producer error. Unchecked.

- Source-classification canonical build `57154` exited 0, empty log; olean now
  exists and must not be rebuilt. Quantitative draft may import it. Current
  owned Lean check is primitive-tail scratch `57108`, log
  `/tmp/leftovers-nyquist-primitive-tail-check.log` (empty so far).
- Physical unchecked drafts now also include `/tmp/leftovers_physical_quantitative.lean`
  (exact square-root norm, continuous/a.e./L²/local-AC profile regularity,
  derivative norm, all-real affine norm, physical trace bound and uniform
  convergence including zero) and `/tmp/leftovers_physical_form_bounds.lean`
  (general exact combined coefficient, finiteness, explicit three-term
  approximation cost, affine cost and separate error-form limits). Both import
  checked convergence; no new olean needed unless a downstream source requires it.

- Read the complete finite-cycle recovery leaf (478 lines) and reread its card.
  Existing `EnergyCycle` uses actual signed products, a floor mesh (including
  zero radius), and source-independent recovery; its elementary scalar and
  power-difference lemmas are private. Exact card coverage still needs arbitrary
  κ, explicit observation count, derivative-energy source controls and distant
  copies. The marked singular-energy gate is not an exact-constant certificate:
  existing collar exponent is `32 max(K,0)/c`, while the card states `8E/c`.
  Prove the latter from the first-order deficit bound; do not silently substitute
  the former. Existing finite mesh can be reused; no new finite-cycle code yet.
- Refreshed nonvacuous-dictionary search found spectral-parameter arithmetic and
  Selberg-conjecture status, not the actual cofinite Selberg-zeta zero dictionary.
  This ranked search is only a lead, not an absence proof. Card's residual
  eigenvalue symmetry caveat remains material; full dictionary audit required.

- PM endpoint audit added the all-cutoff exact formula to its decomposition
  prototype: quadrature equals the long sawtooth minus the full harmonic tail
  past `max n D`. This reduces to the usual tail past `n` for `D≤n`; for `D>n`
  the floor sum is empty and the tail begins at `D`. The centered-prefix
  decomposition already covered every natural `D`. This makes the domain
  boundary explicit without adding an analytic premise.
- Primitive-tail scratch `57108` exited 1 with two local elaboration errors
  (newline field notation parsed at the wrong argument; pointwise function
  subtraction not reduced before `linarith`). Repaired and migrated to
  `NyquistCriticalPrimitiveTail.lean`; final direct check `86169` active,
  log `/tmp/leftovers-nyquist-primitive-tail-final.log`. No tail olean created.
- Source quantitative scratch now includes a trailing axiom audit for 78 public
  declarations across the existing Nyquist parent and five expansion/source
  leaves. Manifest `/tmp/leftovers-nyquist-public-names.json`; strip its marked
  audit suffix when migrating the canonical quantitative source.

- Removed superseded `/tmp/leftovers_nyquist_sources.lean`; canonical checked
  source is authoritative. A mathematical-comment wording cleanup was made
  afterward (no proof change and no olean rebuild). Final direct audit remains.
- Quantitative source draft now also states local uniform convergence for the
  literal normalized autocorrelations of `sourceRescale`, not only the equal
  scaled test `H(x/L)`. Its pending axiom manifest now has 79 declarations.
- Later finite-cycle derivative-control leads: vendor Sobolev translation bound
  `DifferentialGeometry.Analysis.Sobolev.eLpNorm_translate_sub_le_smul_eLpNorm_fderiv`
  (smooth Euclidean source, `Tools/Translation.lean:392`, proof inspected near
  lines 340–430); main-corpus `ArithmeticIncidencePositivity.hasDerivAt_autoCorrelation`
  in `LagChebyshevAbelSummation.lean:1292` (not yet inspected). A direct physical
  box-difference argument could reuse the already certified box contraction,
  but check these precise existing inputs before writing a new translation bound.

- Finite-cycle source derivative lead inspected: the main-corpus
  `ArithmeticIncidencePositivity.hasDerivAt_autoCorrelation` is for arbitrary
  real compact C¹ functions and gives exactly `∫ F(x) F'(x+t)`; its underlying
  correlation convention matches `autocorr`. Vendor translation theorem is
  specialized to `EuclideanSpace ℝ (Fin d)`, so it needs a transport to ℝ and
  is not a drop-in real-source lemma. Prefer reuse of the existing real
  derivative/cross-correlation inputs if they close the exact energy constants.
- Dyadic planning refinement, not a certificate: the exact mantissa tent can be
  represented on each closed dyadic level `q≤n≤2q` by `min(n-q,2q-n)/q`,
  with both endpoint representations zero. This handles the level boundary in
  the adjacent difference bound. For variance, pairing `q+j` and `3q/2+j`
  for `0≤j<q/8` gives value separation at least `1/4`, hence a uniform
  two-point squared-error lower bound. Summing these disjoint pairs would
  imply the required conservative `N/2048` bound without weakening the actual
  specified tent. Formal level identities and counting still required.

- Primitive-tail canonical final check `86169` exited 0, empty log. Wired its
  import into the field umbrella without compiling the umbrella. No olean
  generated. Its five public declarations still need the axiom audit.
- Current owned Lean check: quantitative source scratch `87480`. Command logs to
  `/tmp/leftovers-nyquist-quantitative-check.log` and includes the 79-declaration
  transitive axiom audit. Only one owned Lean process runs.
