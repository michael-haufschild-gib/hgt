# Recursive Stage 2 unconditional Lean formalization

- **ID:** stage-two-recursive-unconditional-formalization
- **Stage:** 1-in-progress
- **Type:** FORMALIZATION PROGRAMME
- **Scope:** Every proven theorem on every card under `docs/drafts/pipeline/2-fully-proven/`, recursively; include cards added while the programme remains active.
- **Statement:** Exact paper statements receive complete unconditional Lean certificates and completed cards move to matching Stage 3 paths.

## Completion requirements

Preserve every mathematical clause and the original domains. Prove missing analytic infrastructure rather than assuming it. Intrinsic capstones must have no unproved mathematical hypothesis parameters. No added axioms, proof placeholders, computational certificates, numerical experiments, heartbeat increases, full builds, or umbrella builds. Preserve unrelated concurrent work.

Use one owned foreground Lean/build process at a time. Refresh only necessary leaf artifacts with `lake --old build +<module>:olean`; final source audit uses `lake env lean <file>`. Audit exact capstones with `#print axioms` in `/tmp`. Wire finished leaves into their area umbrellas, run the authoritative formal lint gate, remove owned scratch files, and repair references to moved cards. Never promote partial coverage.

## Work plan

- [x] Inventory every recursive Stage 2 file, distinguish theorem cards from supporting ledgers, and identify exact existing certificate candidates.
- [ ] Audit each card's complete theorem surface; close all missing proofs and infrastructure without weakening.
- [ ] Verify affected leaves, axioms, umbrella reachability, and formal lint; promote fully covered cards.
- [ ] Re-inventory remaining Stage 2 cards and perform requirement-by-requirement completion audit.

## Evidence log

- 2026-09-29 — Attached objective read in full. Initial recursive inventory contains 102 Markdown files. Existing Stage 2 direct-only ledgers do not cover this scope. `docs/architecture.md` and `docs/testing.md` are absent. Repository has unrelated concurrent edits and active external Lean checks; no external process is owned by this programme.
- 2026-09-29 — Three PM cards have exact candidate leaves already wired into `RHTower.lean`: `FermiNymanDyadicDifferenceRank`, `FermiNymanCorrelationKernel`, and `FermiNymanBoundedSpuriousClassification`. Source coverage inspected; compilation and axiom certification pending. Start with these exact statements, then retain the full recursive queue below.

## Recursive inventory

Historical audit rows remain after cards move. Matching Stage 3 basenames require complete exact certificate audits before certification.

| Stage 2 path | Audit status |
|---|---|
| `02-analytic-da-entire-functions/README.md` | support ledger; Stage 3 candidate |
| `02-analytic-da-entire-functions/_STAGE3-LEDGER.md` | support ledger |
| `02-analytic-da-entire-functions/smooth-stein-order-two-autonomous-ade-frequency-rank.md` | exact audit pending |
| `03-ht-translation-projective-geometry/README.md` | support ledger; Stage 3 candidate |
| `03-ht-translation-projective-geometry/_SWEEP-LEDGER.md` | support ledger; Stage 3 candidate |
| `03-ht-translation-projective-geometry/combination-mode-reducibility-baker-bridge.md` | exact audit pending |
| `03-ht-translation-projective-geometry/projective-horizon-hankel-secant-stratification.md` | exact audit pending |
| `04-rg-stochastic-quantum-fields/README.md` | support ledger; Stage 3 candidate |
| `04-rg-stochastic-quantum-fields/_SWEEP-LEDGER.md` | support ledger; Stage 3 candidate |
| `11-rh-zero-divisor-geometry/README.md` | support ledger; Stage 3 candidate |
| `11-rh-zero-divisor-geometry/verified-height-one-zero-turing-extension.md` | exact audit pending |
| `11-rh-zero-divisor-geometry/weil-cone-explicit-real-producer.md` | exact audit pending |
| `11-rh-zero-divisor-geometry/weil-cone-finite-type-uniqueness.md` | exact audit pending |
| `11-rh-zero-divisor-geometry/weil-cone-singular-deficit-law.md` | exact audit pending |
| `11-rh-zero-divisor-geometry/weil-cone-zero-free-window-rigidity.md` | moved externally to Stage 3; complete exact certificate audit pending |
| `beurling-prime-deletion-perron-region.md` | exact audit pending |
| `li-even-euler-jet-small-mass-crossover.md` | moved externally out of Stage 2; exact certificate audit pending |
| `li-actual-clock-sine-growth-boundary.md` | newly added; exact audit pending |
| `li-mass-calibrated-score-floor-obstruction.md` | newly added; exact audit pending |
| `li-clock-central-prime-gamma-contour.md` | moved externally to Stage 3; exact certificate audit pending |
| `li-clock-paired-eta-central-source.md` | moved externally to Stage 3; exact certificate audit pending |
| `li-clock-finite-eta-deflation.md` | moved externally to Stage 3; exact certificate audit pending |
| `li-clock-off-line-negative-response.md` | moved externally to Stage 3; exact certificate audit pending |
| `li-clock-damped-endpoint-sum-rule.md` | moved externally to Stage 3; complete exact certificate audit pending |
| `theta-derivative-packet-full-score-floor.md` | moved externally to Stage 3; exact certificate audit pending |
| `pm-bounded-spurious-classification.md` | certified; moved to Stage 3 |
| `pm-correlation-jet-kernel.md` | certified; moved to Stage 3 |
| `pm-dyadic-defect-rank.md` | certified; moved to Stage 3 |
| `route e/_lean-programme.md` | support ledger |
| `route e/route-e-cofactor-amplified-e3-token-supply.md` | exact audit pending |
| `route e/route-e-forbidden-support-e3-stability.md` | exact audit pending |
| `rw-free-lag-trace-boundary-layer.md` | exact audit pending |
| `rw-prime-curvature-compact-source-onset.md` | certified; moved to Stage 3 |
| `theta/_lean-programme.md` | support ledger |
| `theta/causal-mobius-theta-boundary-criterion.md` | exact audit pending |
| `theta/causal-mobius-theta-primorial-transition.md` | exact audit pending |
| `theta/theta-cdf-crossfrequency-rvm-capacity.md` | exact audit pending |
| `theta/theta-cdf-no-finite-range-symmetrizer.md` | exact audit pending |
| `theta/theta-chronological-boundary-positive-transfer.md` | exact audit pending |
| `theta/theta-compact-inverse-zero-jordan-history.md` | actual Jordan/history/quotient/Riesz/Fourier/prime-deletion results, exact interweight law (5), weighted properness and q=0 endpoint (7), real/off-real tempered boundary, canonically normalized all-order quotient decay, actual finite-Dirac-jet Xi kernel, explicit unscaled physical source-jet transport, genuine Schwartz complex translation derivative, exact scalar source jets and derivative/translation annihilator equivalence certified; full tempered annihilator/multiplicity classification (8) open |
| `li-clock-infinite-partition-critical-transition.md` | externally moved to Stage 3; complete updated 589-line card read; exact critical Gaussian transition for both literal kernels, ratios/gaps, signed/absolute/complex-norm errors and shared quarter-disk obstructions retain every original target; all five groups and all 64 externally claimed declarations require this ledger's complete exact proof/API and whole-card audit |
| `li-clock-infinite-partition-supercritical-window.md` | moved externally to Stage 3; complete exact certificate audit pending for both literal complex exterior bounds and numerator/polynomial refinements, all weighted error limits and shared disk obstructions |
| `11-rh-zero-divisor-geometry/weil-cone-random-discrete-granularity-threshold.md` | externally moved to Stage 3 with partial endpoint coverage; complete updated 131-line card read; both sharp directions for every admissible κ, all-height high-probability positivity, actual discrete Weil producer and full sharp fluctuation growth still require complete paper/exact Lean audits; external κ = 2^(−26) and κ = 1 components are not an owned whole-card certificate |
| `li-clock-infinite-partition-supercritical-ratio.md` | externally moved to Stage 3; complete updated 569-line card read, claiming 37 public exports across three leaves; all 23 original/exposed equations and targets, actual/reference positive prefactors and arbitrary qualified-sequence full ratio, angular asymptotic, periodic endpoint averaging, logarithmic rates and separate parameter boundary limits retained pending this ledger's exact whole-card proof/API certification |
| `theta/theta-deletion-cutoff-commutator-collapse.md` | exact audit pending |
| `theta/theta-prime-deletion-graded-terminal-admission.md` | certified; moved to Stage 3 |
| `theta/theta-prime-deletion-moving-cusp-dual-source.md` | exact audit pending |
| `theta/theta-quantile-critical-one-port-rigging.md` | exact audit pending |
| `theta/theta-quantile-resistance-network.md` | exact audit pending |
| `universal-law-field/constitutive-dilation-mechanics/laplace-formation-defect-history-recovery-and-passive-reconstruction-law.md` | exact audit pending |
| `universal-law-field/constitutive-reflection-space-mechanics/selfadjoint-dyson-word-reversal-twisted-reflection-realization-and-joint-selection-no-go.md` | exact audit pending |
| `universal-law-field/constitutive-reflection-space-mechanics/twisted-antipode-response-reflection-fusion-grade-reconstruction-and-joint-properness-law.md` | exact audit pending |
| `universal-law-field/direct-subunit-anchor/formation-anchored-cubic-homotopy-defect.md` | exact audit pending |
| `universal-law-field/direct-subunit-anchor/restricted-unitary-cubic-relative-index.md` | exact audit pending |
| `universal-law-field/eigen-pair-prime-identification-derivation.md` | exact audit pending |
| `universal-law-field/formation-compactification-mechanics/poisson-dust-formation-compactification-cumulant-separation-and-equivariant-neutrality-law.md` | exact audit pending |
| `universal-law-field/formation-excess-mechanics/ramification-gibbs-gns-defect-spectral-information-and-boundary-work-law.md` | exact audit pending |
| `universal-law-field/formation-laplacian-properness-mechanics/formation-quotient-interchange-tight-recovery-and-residual-coverage-law.md` | exact audit pending |
| `universal-law-field/formation-laplacian-properness-mechanics/source-response-laplacian-properness-pluecker-and-adaptive-escape-law.md` | exact audit pending |
| `universal-law-field/formation-tangent-geometry/prime-harmonic-logarithmic-end-haar-frame-trichotomy.md` | exact audit pending |
| `universal-law-field/law-generated-polarization-dynamics/legendre-residual-transduction-fusion-work-and-cubic-response-law.md` | exact audit pending |
| `universal-law-field/local-exponential-test-closure-mechanics/local-exponential-complete-order-fusion-and-euler-shell-witness-escape-law.md` | exact audit pending |
| `universal-law-field/nomological-homotopy-geometry/length-three-partial-flattening-holonomy-spectrum-recurrence-and-properness-law.md` | exact audit pending |
| `universal-law-field/nonvacuous-independence-and-polarization-import-law.md` | exact audit pending |
| `universal-law-field/odd-coordinate-mechanism-universal-law-set.md` | exact audit pending |
| `universal-law-field/orbit-induction-selection-mechanics/atomless-phase-formation-ideal-escape-rank-and-entropy-law.md` | exact audit pending |
| `universal-law-field/orbit-induction-selection-mechanics/character-transgression-positive-resonance-and-small-divisor-formation-law.md` | exact audit pending |
| `universal-law-field/orbit-induction-selection-mechanics/conditional-orbit-information-and-essential-coupling-no-cancellation-law.md` | exact audit pending |
| `universal-law-field/orbit-induction-selection-mechanics/mixed-spectral-formation-atomic-retention-continuous-escape-and-closed-range-law.md` | exact audit pending |
| `universal-law-field/ordered-fusion-chronology-mechanics/permutation-averaged-first-failure-symmetric-convolution-tomography-and-compact-properness-law.md` | exact audit pending |
| `universal-law-field/poisson-scale-history-completion-mechanics/burnol-frame-completion-classification.md` | exact audit pending |
| `universal-law-field/poisson-scale-history-completion-mechanics/integral-nuclear-boundary-scale-germ-pythagorean-law.md` | exact audit pending |
| `universal-law-field/poisson-scale-history-completion-mechanics/prime-log-congruence-ideal-exit-law.md` | exact audit pending |
| `universal-law-field/poisson-scale-history-completion-mechanics/purification-boundary-transfer-interchange-anomaly-law.md` | exact audit pending |
| `universal-law-field/poisson-scale-history-completion-mechanics/spectral-aperture-cone-wiener-hopf-transgression.md` | exact audit pending |
| `universal-law-field/polarized-contact-formation-geometry/primitive-work-character-transmutation-and-wold-signature-wall-law.md` | exact audit pending |
| `universal-law-field/polarized-contact-formation-geometry/reflection-contact-parity-minimal-oriented-rank-and-recovery-neutrality-law.md` | exact audit pending |
| `universal-law-field/projective-gamma-completion-mechanics/theta-prime-beta-gamma-projective-recovery.md` | exact audit pending |
| `universal-law-field/reciprocal-fusion-topology-mechanics/reciprocal-fusion-work-classification-weighted-compactness-and-factorization-law.md` | exact audit pending |
| `universal-law-field/recurrent-boundary-density-geometry/common-radial-subunit-harmonic-completion.md` | exact audit pending |
| `universal-law-field/recurrent-boundary-density-geometry/phase-quotient-stationary-completion-homotopy.md` | exact audit pending |
| `universal-law-field/recurrent-boundary-density-geometry/recurrent-prime-boundary-density-transgression.md` | exact audit pending |
| `universal-law-field/restricted-grassmannian-formation-geometry/burnol-graph-action-filtration.md` | exact audit pending |
| `universal-law-field/restricted-grassmannian-formation-geometry/burnol-graph-cap-area.md` | exact audit pending |
| `universal-law-field/restricted-grassmannian-formation-geometry/determinant-line-lifted-action-deck-law.md` | exact audit pending |
| `universal-law-field/restricted-grassmannian-formation-geometry/minimal-hadamard-provenance-double.md` | exact audit pending |
| `universal-law-field/restricted-grassmannian-formation-geometry/physical-overlap-plucker-integral-nuclear-homotopy-defect.md` | exact audit pending |
| `universal-law-field/restricted-grassmannian-formation-geometry/plucker-covariance-purification-observer-subunit-defect.md` | exact audit pending |
| `universal-law-field/restricted-grassmannian-formation-geometry/prime-poisson-third-sector-integral-nuclear-homotopy-defect.md` | exact audit pending |
| `universal-law-field/restricted-grassmannian-formation-geometry/theta-mellin-six-holonomy-integral-nuclear-formation.md` | exact audit pending |
| `universal-law-field/restricted-grassmannian-formation-geometry/zero-distance-infinite-action-formation-defect.md` | exact audit pending |
| `universal-law-field/reversible-formation-dilation-mechanics/endpoint-neutral-path-singular-functional-equation-reset-dilation-law.md` | exact audit pending |
| `universal-law-field/reversible-formation-dilation-mechanics/functional-equation-history-extension-obstruction-and-four-entropy-conservation-law.md` | exact audit pending |
| `universal-law-field/route-q-ratio-gate-decision.md` | exact audit pending |
| `universal-law-field/scale-mautner-formation-mechanics/scale-mautner-pure-point-blindness-compact-resolvent-fracture-and-cross-fibre-spectral-law.md` | exact audit pending |
| `universal-law-field/source-complete-defect-corona-mechanics/source-complete-trace-defect-corona-transience-and-properness-selection-law.md` | exact audit pending |
| `universal-law-field/source-generated-orbit-gramian-mechanics/causal-delay-radial-drift-work-cusp-and-information-undercapacity-law.md` | exact audit pending |
| `universal-law-field/source-generated-orbit-gramian-mechanics/cyclic-heat-orbit-gramian-lyapunov-properness-and-corona-selection-law.md` | exact audit pending |
| `universal-law-field/source-generated-orbit-gramian-mechanics/euler-hellinger-gamma-relative-mellin-anomaly-law.md` | exact audit pending |
| `universal-law-field/source-generated-orbit-gramian-mechanics/euler-stokes-aperture-capacity-and-singular-sixth-boundary-law.md` | exact audit pending |
| `universal-law-field/source-generated-orbit-gramian-mechanics/prime-hodge-cubic-orbit-birth-faithfulness-and-self-financing-law.md` | exact audit pending |
| `universal-law-field/source-generated-orbit-gramian-mechanics/prime-hodge-full-idempotence-defect-and-bounded-multiplicative-horizon-no-go.md` | exact audit pending |
| `universal-law-field/source-generated-orbit-gramian-mechanics/spectral-hardy-trace-formation-admission-and-radial-capital-wall-law.md` | exact audit pending |
| `universal-law-field/source-response-signature-mechanics/all-grade-flag-determinant-subset-phase-conservation-and-arity-properness-fracture-law.md` | exact audit pending |
| `universal-law-field/source-response-signature-mechanics/arithmetic-prime-shift-duhamel-commutator-normalization-and-ordered-scale-memory-law.md` | exact audit pending |
| `universal-law-field/source-response-signature-mechanics/base-norm-formation-measure-isometry-and-hilbert-observer-fracture-law.md` | exact audit pending |
| `universal-law-field/source-response-signature-mechanics/character-coinvariant-defect-green-properness-and-reflection-formation-selection-law.md` | exact audit pending |
| `universal-law-field/source-response-signature-mechanics/character-twisted-coinvariant-laplace-fisher-reconstruction-and-origin-atom-properness-law.md` | exact audit pending |
| `universal-law-field/source-response-signature-mechanics/dyson-volterra-source-response-reconstruction-lyapunov-and-global-properness-law.md` | exact audit pending |
| `universal-law-field/source-response-signature-mechanics/formation-grade-properness-inversion-prime-log-crowding-and-finite-prolongation-no-go.md` | exact audit pending |
| `universal-law-field/source-response-signature-mechanics/permutohedral-grade-four-hurwitz-exactification-and-fifteen-phase-properness-law.md` | exact audit pending |
| `universal-law-field/source-response-signature-mechanics/permutohedral-grade-three-alternant-subset-green-and-seven-phase-properness-law.md` | exact audit pending |
| `universal-law-field/source-response-signature-mechanics/relative-grade-green-exactification-hypoexponential-formation-and-global-pair-properness-law.md` | exact audit pending |
| `weil-cone-order-comparable-rigidity.md` | exact audit pending |

## Verified PM completion — 2026-09-29

Three cards promoted after exact coverage audit: bounded-spurious classification, correlation-jet kernel, and dyadic-defect rank. Targeted `lake --old build` passed exit 0; final direct source checks on all three leaves passed exit 0. One scratch axiom audit covered all 52 declarations in `FermiNymanCorrelationJets`, `FermiNymanMultiplicityIndex`, `FermiNymanDyadicDifferenceRank`, `FermiNymanCorrelationKernel`, and `FermiNymanBoundedSpuriousClassification`; every axiom set is a subset of `[propext, Classical.choice, Quot.sound]`. Existing umbrella imports confirmed. No new Lean code was needed for these three exact source certificates.

Global formal lint failed only on concurrent unrelated reachability gaps: `CCMApertureChainProfile`, `CCMApertureTranslationChains`, `CCMExponentialRampPrimeMoment`, `CCMExponentialRampSourceDissipation`, `CCMExponentialRampTerminalEntropy`, `CCMRetainedChainKernelLower`, `MoebiusMollifiedCriticalMoment`, `MoebiusMollifiedErrorThreeLines`, `ThetaMovingShellFirstOrderPhase`, and `ZetaZeroDensityPowerSaving`. Preserve those proof scopes. Do not report global lint as passing.

Next exact construction: `rw-prime-curvature-compact-source-onset.md`. Existing strict-aperture plateau covers its negative side; closed-endpoint rate equality, positive Schur block and exact real six-sample kernel remain to formalize. Partial corpus search inspected both `candidate_lemmas` and `source_arguments`; candidates verified directly in current sources.

## Verified compact-source onset — 2026-09-29

New leaf `RHTower/CCMPrimePoleCurvatureCompactOnset.lean` closes every mathematical clause of the boundary-onset card. Literal closed cutoff and four-row equality, exact logarithmic bounds, positive Schur complement, both support-forced endpoint zeros, the full six-real-sample kernel, and the all-strict-aperture constrained sharp negative stencil are proved. Intrinsic capstone has no analytic premise. Targeted --old leaf build and final direct Lean passed without warnings; all 16 public declarations axiom-audit to the standard baseline. Wired into RHTower. Card moved to Stage 3. Formal lint has no finding on the new leaf; global failures concern concurrent unreachable leaves, now including new LI mass-series leaves.

Next: exact LI small-mass crossover. Live corpus now contains `LiEvenCrossEulerMassSeries`, `LiEvenCrossEulerMassJetSeries`, and `LiEvenCrossEulerSmallMassRemainder`. Their literal series and uniform remainder proof sources were inspected. Do not edit these concurrent leaves; build necessary artifacts and construct a disjoint `LiEvenCrossEulerSmallMassCrossover.lean` for exact two-term decomposition, uniform growing-order estimate, first-negative-index bounded-offset/slope law, and sequence profile. All original card clauses remain required before promotion.

### Concurrent scope and next owned construction

The live LI programme now records a delegated least-negative-index capstone and contains `LiEvenCrossEulerSmallMassProfile.lean`; its exact series split and uniform-error proofs were inspected. The RW programme has begun its second-age-moment Abel proof. Preserve both concurrent write scopes and audit their completed certificates when available.

Owned next card: `theta/theta-prime-deletion-graded-terminal-admission.md`. Full paper statement read, relevant theta history/deletion memories read, and prior corpus searches launched. Required construction, without replacing the literal source:

- [x] Exact envelope asymptotic and arbitrary finite arithmetic-shift terminal cusp ratio.
- [x] Literal power-weighted `L²` admission iff `q < 2 / b²`, including equality failure.
- [x] Exact finite-prime terminal coefficient and positive-cusp ratio, plus prime-square case.
- [x] Finiteness of admitted prime sets and cofinal exponent escape.
- [x] Admitted finite deletion belongs to the actual closed derivative history; build required weighted analytic-translation infrastructure.
- [x] Targeted leaf builds, final direct source checks, complete axiom audits, umbrella wiring and full-clause promotion.

No partial core is a Stage-3 certificate. The Hankel secant and Baker bridge cards were inspected for remaining work: normality/rational singularities and effective Baker respectively remain actual infrastructure obligations, not importable premises.

Five modules now certify the complete arithmetic admission and cofinal escape surface: `ThetaArithmeticTerminalCusp.lean`, `ThetaPowerWeightedSource.lean`, `ThetaPrimeDeletionTerminalCusp.lean`, `ThetaArithmeticWeightedAdmission.lean`, and `ThetaPrimeDeletionWeightedAdmission.lean`. Named --old leaf builds passed. Final `lake env lean FILE` checks passed for all five sources without warnings. A scratch-file axiom audit covered all 58 public declarations; only `propext`, `Classical.choice`, and `Quot.sound` appeared, with no missing reports. All five modules are wired into the umbrella. The full card and recursive goal remain incomplete because actual derivative-history membership still needs construction.

#### Remaining weighted-history construction

The arithmetic and prime specialization modules are now certified, including the prime-square threshold, finite admission sets, terminal-product divergence, vanishing admitting weights, and eventual exclusion at every fixed positive weight. The full card's derivative-history clause remains pending.

The exact final card clause is membership in the closed span of the actual derivative vectors in `Lp ℂ 2 (thetaPowerWeightedMeasure q)`. Required source infrastructure:

1. **Certified:** retain the full Gaussian exponent in the complex strip. For `0 ≤ δ < π/4`, put `c = π cos(2δ) > 0`. For `Re z = x ≥ 0`, the existing pointwise atom bound and `(n² - 1)(exp(2x) - 1) ≥ 0` give
   `‖k(z)‖ ≤ Cδ exp(9x/2) exp(-c exp(2x))`.
   The explicit finite constant comes from the already summable Gaussian majorant `(n⁴+n²) exp(-c n²)`, with prefactor `2π(2π+3) exp(c)`. The zero atom is zero. Modular reflection extends the bound to `|Re z|`. `ThetaCuspComplexGaussianEnvelope.lean` now proves this exact bound through `norm_thetaCuspStripSource_le_gaussian_envelope`. Its named --old leaf build and final direct source check passed without warnings; a separate scratch audit covered all four public declarations with standard axioms only. The module is wired into the umbrella. Total new theta certificates: six final sources, 62 public declarations.
2. For terminal shift `A = log b` and `q < 2 / b²`, choose a slightly wider real aperture and a small imaginary aperture retaining `q < 2 exp(-2A') cos(2δ)`. The full source's positive lower envelope then gives a uniform, genuinely integrable weighted square majorant for all translations in this complex rectangle.
3. Construct the actual Hilbert-valued holomorphic translation map there, identify its Taylor coefficients with the actual weighted derivative vectors, and use its connected-domain identity theorem plus closed-span separation. This proves every constituent shift `log d`, hence their exact finite signed sum, lies in derivative history.

Corpus check: lexical research found complex-strip holomorphy, fixed-weight divisor vectors, and ordinary `L²` cyclicity. It returned no candidate lemmas or source arguments implementing this power-weighted holomorphic translation map. Direct `rg` in mathlib's `LpSpace` and `L2Space` found no analytic or differentiable parameter-map theorem; the required bridge remains a real infrastructure obligation. The card stays in Stage 2 until this clause and every final gate pass.

**2026-09-30 discovery:** a broader deep query found existing repository infrastructure outside the earlier Theta module filter. `HTGeometry/L2CauchyHolomorphy.lean` proves `GaloisForLFunctions.HTGeometry.differentiableAt_l2Family_of_cauchy_dominated` for the actual `Lp ℂ 2 μ` class, from pointwise holomorphy, measurable sections, and a common `MemLp` majorant on a parameter ball. Its complete source and dependencies `L2DominatedContinuity.lean` and `CauchyDominatedIntegralHolomorphy.lean` were read. Its needed named leaf build passed. `RHTower/AnalyticDominatedL2Sections.lean` also has a fully proved locally dominated family and weak holomorphy theorem. The query was partial: stale/pending compiler coverage and malformed local judging JSON were reported; these hits were inspected directly, not assumed verified by the search.

The concrete next obligation is therefore a common theta `MemLp` majorant. For `A ≥ 0`, take
`H(x) = Cδ exp(9(|x|+A)/2) exp(-π cos(2δ) exp(2(|x|-A)))`.
Triangle bounds and the certified full strip envelope dominate every actual complex translate with `|Re z| ≤ A`, `|Im z| ≤ δ`. When `q < 2 exp(-2A) cos(2δ)`, its literal weighted energy is continuous and even, and its positive-tail ratio to the exact integrable exponential model tends to `Cδ² (4π²)^(-q)` by the certified complete-source asymptotic. This supplies the majorant for the existing strong `L²` lifting theorem. The remaining derivative-vector identification is still required: the currently exported generic theorem gives differentiability; its proof contains the concrete derivative representative, which should be exposed or proved explicitly before identifying the actual derivative history.

Generated Lean API, gaps, overview, and lexical search index were refreshed successfully after these six modules. Authoritative `scripts/formal_tools.py lint` still exits 1 on ten existing, concurrently developed modules unreachable from the RHTower umbrella: `CCMApertureChainProfile`, `CCMApertureTranslationChains`, `CCMExponentialRampPrimeMoment`, `CCMExponentialRampSourceDissipation`, `CCMExponentialRampTerminalEntropy`, `CCMRetainedChainKernelLower`, `MoebiusMollifiedCriticalMoment`, `MoebiusMollifiedErrorThreeLines`, `ThetaMovingShellFirstOrderPhase`, and `ZetaZeroDensityPowerSaving`. No new theta module has a lint finding. Global lint is not claimed green.

## Verified terminal admission and actual derivative history — 2026-09-30

The terminal-admission card is fully certified and moved to
`docs/drafts/pipeline/3-formalized/theta/theta-prime-deletion-graded-terminal-admission.md`.
All original clauses are preserved. The literal complete theta source, exact
power-weighted measure, finite Möbius Euler polynomial, and equality exclusion
are unchanged.

Four further RHTower leaves close the final history obligation:

- `ThetaPowerWeightedComplexTranslations.lean`: explicit full-Gaussian rectangle majorant, exact weighted energy asymptotic, actual `MemLp` domination of every source translate.
- `AnalyticDominatedL2Derivatives.lean`: Cauchy estimates keep actual derivative families locally dominated; every Hilbert jet is the class of its actual pointwise jet. Connected-domain analytic uniqueness proves closed-span membership.
- `ThetaPowerWeightedDerivativeHistory.lean`: real and complex complete-source jets coincide; every actual derivative is admitted for `0 < q < 2`; admitted real translations belong to their literal closed span.
- `ThetaPrimeDeletionDerivativeHistory.lean`: finite sums commute with the genuine L² quotient, proving exact admitted arithmetic-word and finite Euler-deletion history membership.

The existing `HTGeometry/L2CauchyHolomorphy.lean` proof was strengthened to expose
its actual derivative representative. The previous differentiability theorem
retains its signature and follows from the stronger result. No analytic premise
is assumed by the concrete theta capstones.

Needed named --old leaf builds passed. Final direct source checks passed without
warnings for all four new leaves and the modified Cauchy dependency; the earlier
six theta leaves already passed their final checks. A scratch audit checked all
48 public declarations in these five final files, with 48 reports, no missing
reports, and standard axioms only. Together with the earlier 62 audited theta
declarations, this gives 110 audited declarations. All ten RHTower leaves are
wired into the umbrella. Generated API, gaps, overview, and search index refreshed.
References to the moved card in the moving-cusp card, prime-square card, and xi
ledger were repaired. No full or umbrella build was run.

Latest authoritative lint exits 1 only on 16 unrelated concurrent unreachable
leaves. RHTower: `CCMApertureChainProfile`, `CCMApertureTranslationChains`,
`CCMExponentialRampPrimeMoment`, `CCMExponentialRampSourceDissipation`,
`CCMExponentialRampTerminalEntropy`, `CCMRetainedChainKernelLower`,
`HalfGaussTransformDerivative`, `HeatGaussianTiltedMoments`,
`LiEvenCrossActualClockTopFrequency`, `MoebiusMollifiedCriticalMoment`,
`MoebiusMollifiedErrorThreeLines`, `ThetaMovingShellFirstOrderPhase`,
`XiHorizontalLogDerivativeModel`, `XiHorizontalStripComparison`, and
`ZetaZeroDensityPowerSaving`. HTGeometry: `LogLinearGronwallModel`.
No owned new module has a lint finding. Global lint is not green.

Next exact audit: `theta/theta-compact-inverse-zero-jordan-history.md`. Its full
theorem and derivative-admission/action proof through line 133 have now been
read, together with the earlier translation-history section and concluding
status. The newly certified weighted-history infrastructure covers a substantial
part of that card, but its actual pinned inverse, mean-zero quotient, infinite
Jordan chain, dense ranges, quasinilpotent history restriction, and nonzero
spectral multiplicity quotient still require complete exact coverage audits.
Do not promote it from a full-inverse no-intertwiner lemma alone.

The complete paper audit now includes every clause through line 425: literal
derivative admission and independence; full and orthogonally centered zero
Jordan chains; both dense-range/adjoint/no-intertwiner conclusions; proper
invariant history and quasinilpotence; exact preservation of every nonzero Xi
eigenvalue and its algebraic multiplicity; sharp real-translation boundary and
prime exclusion; proper weighted histories and the dense unweighted endpoint;
the exact tempered annihilator with multiplicity jets; and rapid quotient decay
of normalized source eigenmodes. The existing smooth-core `thetaCenterProjection`
is not the orthogonal projection required by the card.

Owned construction starts with literal source derivative classes at weight one,
their integrable derivatives and vanishing two-ended limits. The fundamental
theorem gives the exact centered source primitive; the existing actual quantile
inverse identity then supplies the Jordan action. Orthogonal projection supplies
the centered chain without changing the source or introducing premises. A direct
deep prior-research search completed with full inventory coverage; all 20
candidate lemmas and all 20 source arguments were inspected. Candidate compiler
freshness is mixed and applicability unverified, so source inspection and native
Lean checks remain authoritative. The three needed existing leaf targets built
successfully; no full or umbrella build was run.

Five owned cards are now certified: three PM cards, compact-source curvature
onset, and terminal weighted admission. The full recursive objective remains
active and far from complete; all remaining cards still require complete audits.

Checkpoint cleanup removed all 21 recorded owned scratch files, with every exact
path verified absent. A raw `rm -f` call was automatically rejected; bounded
regular-file checks and explicit-path deletion completed cleanup. No owned job
remains running.

### Actual zero-Jordan and proper-history checkpoint

`HedenmalmThetaDerivativeJordan.lean` now certifies 34 public declarations:
literal complex source derivatives; their continuity, integrability and
two-ended limits; zero total integral and exact pinned primitive; actual
weight-one source classes and quantile images; the constant zeroth vector;
both infinite zero-Jordan chains; nonzero and linearly independent full and
centered families; dense orthogonally centered range; injective centered
adjoint; absence of every bounded injective centered symmetrizer; finite
nilpotent power laws; and invariance of the closed actual derivative history.
The projection here is the orthogonal projection onto the constant mode's
orthogonal complement, not the older smooth-core centering projection.

`HedenmalmThetaDerivativeHistorySpectrum.lean` certifies ten more public
declarations. It constructs the actual compact restriction to derivative
history, proves its spectrum is exactly `{0}`, and proves history is proper
using Hardy's actual real Xi zeros. The spectral proof uses compactness of
the adjoint: any nonzero adjoint eigenvalue annihilates every lowering-chain
generator, hence the closed history and its own eigenvector. No additional
premise, numerical certificate or heartbeat adjustment was introduced.

Both exact native leaf targets and both final direct source audits passed
without warnings. A 68-name API witness scratch check passed. All 44 new
public declarations and four existing full-operator capstones had complete
axiom reports: 48 expected, 48 reported, no missing or extra reports, and no
axioms outside `propext`, `Classical.choice`, and `Quot.sound`. Both new
leaves are wired into `RHTower.lean`; the generated API, gaps, overview and
search index were refreshed. No full or umbrella build was run.

The card remains Stage 2. Required next work: exact nonzero spectral quotient
and algebraic multiplicities; sharp arbitrary real translation boundary and
closed-history identity; properness at every positive weight and dense
unweighted endpoint; the exact tempered annihilator and local multiplicity
jet classification; and rapid normalized eigenmode decay in the quotient.
The recursive programme and its remaining card audits are still active.

The current exhaustive inventory remains 98 Markdown files, including nine
support files and 89 theorem cards. Added `li-clock-central-prime-gamma-contour.md`
to the audit queue. The theta derivative-packet score-floor card has moved
externally to Stage 3; that move is not an owned certificate audit.

Final formal lint exits 1 on eleven unrelated concurrent unreachable leaves:
`CCMApertureChainProfile`, `CCMApertureTranslationChains`,
`CCMExponentialRampPrimeMoment`, `CCMExponentialRampSourceDissipation`,
`CCMExponentialRampTerminalEntropy`, `CCMRetainedChainKernelLower`,
`LiClockCentralSineContour`, `MoebiusMollifiedCriticalMoment`,
`MoebiusMollifiedErrorThreeLines`, `ThetaMovingShellFirstOrderPhase`, and
`ZetaZeroDensityPowerSaving`. Neither new owned leaf has a lint finding.
The initial lint stderr was not captured in its log; a complete captured
rerun supplied this exhaustive diagnostic list. Baseline large-file warnings
remain. Global lint is not green.

Checkpoint cleanup removed all eleven exact owned scratch paths, verified each
absent, and left no owned foreground job running. Five previously completed
owned cards remain certified in Stage 3; this continuation adds infrastructure
and exact card clauses without promoting the unfinished history card.

Fresh exhaustive inventory contains 98 Stage 2 Markdown files. Three new cards
were added to the queue: `li-actual-clock-sine-growth-boundary.md`,
`li-mass-calibrated-score-floor-obstruction.md`, and
`theta-derivative-packet-full-score-floor.md`. The LI small-mass crossover card
also moved externally out of Stage 2; its full certificate still needs the
programme's exact audit. External movement alone is not certification.

### Exact nonzero spectral quotient construction

Current proof target is the literal Hilbert quotient by actual derivative
history, with every nonzero generalized root space and algebraic multiplicity
preserved. For a nonzero scalar `lam`, the certified spectrum `{0}` makes
`B|R - lam I` invertible. The quotient map intertwines shifted powers. If a
quotient vector is killed by the `n`th shifted power, lift it to `x`; that power
of `x` lies in `R`. Invert the same power on `R` and subtract its preimage.
The corrected lift belongs to the full `n`th root space. Intersection with `R`
is zero by invertibility, so the lift is unique. This proves an exact linear
equivalence for every finite root level and their maximal union, hence the
same algebraic multiplicity used by the existing determinant theorem.

- [x] Certify reusable algebraic quotient/root-space transport.
- [x] Construct the continuous operator on the literal quotient and prove
  compactness using its bounded orthogonal section.
- [x] Discharge invertibility from actual theta-history spectrum `{0}`;
  certify every nonzero spectral value and root multiplicity in the quotient.
- [x] Wire leaves; check final sources and all exported axioms; refresh the
  index, run formal lint, and remove owned scratch artifacts.

The direct deep prior-research search completed with full inventory coverage;
all twenty candidate lemmas and all twenty source arguments were inspected.
Compiler freshness is mixed and candidates are source-only. Local source
inspection and current-toolchain Lean checks remain authoritative. This
construction adds no premise to the actual theta result and does not promote
the unfinished history card.

### Full nonzero derivative-history quotient checkpoint

`GeneralizedEigenspaceQuotient.lean` certifies eleven public declarations.
Over any commutative ring, an invertible shifted restriction makes quotient
projection a linear equivalence on every generalized root level, including
the maximal union. The proof corrects a quotient lift using the inverse
shifted power on the invariant subspace. It certifies injectivity,
surjectivity, canonical forward projection, exact finranks, and preservation
of eigenvalues.

`CompactInvariantQuotient.lean` certifies eight public declarations. It
constructs the continuous operator on the literal quotient, identifies its
linear map with `Submodule.mapQ`, and constructs an isometric bounded
orthogonal section. Factoring through this section proves compactness.

`HedenmalmThetaDerivativeHistoryQuotient.lean` certifies twenty-two more
public declarations. Actual history spectrum `{0}` discharges every shifted
invertibility obligation. The quotient kills the actual derivatives,
intertwines the full compact inverse, identifies all nonzero generalized
root spaces, and preserves every nonzero spectral value. Canonical source
eigenmodes remain nonzero. The exact existing determinant law identifies
the quotient's algebraic multiplicity with analytic Xi order at every
complex zero and with every divisor-support multiplicity. No RH premise,
new mathematical hypothesis, numerical certificate, or heartbeat change
was introduced.

All three native leaf targets and all three final direct source audits
passed without warnings. A 47-name API witness passed. All 41 new public
declarations and four existing capstones have 45 complete axiom reports:
45 expected, 45 reported, no missing or extra reports, and only `propext`,
`Classical.choice`, and `Quot.sound`. The imported operator identities need
explicit `change` to the continuous operator or the existing endomorphism
model; `simpa` can leave unresolved coercion-instance diamonds. Both generic
leaves use `noncomputable section` so their exported equivalence and section
definitions also appear in the generated API. Their proof bodies are unchanged.

The exact finite-level correction proof is now recorded on the paper card.
The card remains Stage 2. Explicit bounded left Fourier functional and
Riesz-projection annihilation certificates remain pending, together with
sharp real-translation admission and closed-span identity, arbitrary
finite positive-prime translation exclusion, all positive-weight properness,
the dense unweighted endpoint, the exact tempered annihilator and
multiplicity jets, and rapid normalized quotient eigenmode decay.

Next spectral detail has a direct paper proof: a Riesz projector commutes
with `B`, so its image of each derivative generator is both a generalized
zero vector and a nonzero-eigenvalue root vector. Disjointness forces zero;
continuity extends annihilation to closed history. Its literal projector
and root-range/commutation facts must be supplied from the actual compact
operator, without adding projector hypotheses to the theta capstone.

The exhaustive inventory before cleanup contained 100 Stage 2 Markdown files:
nine support files and 91 theorem cards. Added
`li-clock-paired-eta-central-source.md` to the full audit queue.
Two further cards appeared during final verification:
`li-clock-finite-eta-deflation.md` and
`li-clock-off-line-negative-response.md`; both are now queued for exact audit.
The central prime-gamma contour card moved externally to Stage 3; its
exact certificate audit remains pending. Five previously completed owned
cards remain certified; this checkpoint adds exact infrastructure and card
clauses without promoting the unfinished history card.

Final generated API contains all 41 new exports: 41 expected, 41 catalogued,
no missing or extra entries. The scope-marker layout adjustment justified
rebuilding the affected leaf artifacts and repeating the final three source
audits and 45 complete axiom reports. The refreshed index also includes
concurrent external source changes. No full or umbrella build was run.

Final authoritative formal lint exits 1 on fourteen unrelated concurrent
unreachable RHTower leaves: `CCMApertureChainProfile`,
`CCMApertureTranslationChains`, `CCMExponentialRampPrimeMoment`,
`CCMExponentialRampSourceDissipation`, `CCMExponentialRampTerminalEntropy`,
`CCMRetainedChainKernelLower`, `MoebiusMollifiedCriticalMoment`,
`MoebiusMollifiedErrorThreeLines`, `RiemannAutocorrFourier`,
`ThetaMovingShellFirstOrderPhase`, `WeilDeviationTranslationBound`,
`WeilFullConeNearNullPositiveDefinite`, `XiRealZeroFejerSum`, and
`ZetaZeroDensityPowerSaving`. All diagnostics were inspected; none belongs
to the three new owned leaves. Baseline large-file warnings remain. Global
lint is not green. Earlier fifteen-error diagnostics were superseded by
this final fourteen-error snapshot as concurrent work changed.

Checkpoint cleanup removed all eleven explicit owned scratch paths and
verified each absent. No owned foreground job remains running. The recursive
goal remains active; every remaining card and every pending history-card
clause still requires its complete exact certificate.

After cleanup, the paired eta central-source card moved externally to Stage 3.
Its exact certificate audit remains pending. The final exhaustive snapshot
contains 99 Stage 2 Markdown files, nine support files and 90 theorem cards;
every current path is represented in the audit queue. External Stage 3 moves
continue to require the programme's complete certificate audit.

### Literal theta Riesz projection work plan

- [x] Reuse and check the existing actual compact theta contour projection,
  its isolating radius, finite root range, and idempotence.
- [x] Prove it annihilates every derivative generator, then the entire
  closed derivative history by continuity.
- [x] Descend that literal projection to the actual history quotient;
  certify complementary range/kernel decomposition and the unchanged
  finite nonzero root block.
- [x] Build only needed leaf targets; audit final sources and every public
  axiom report; wire the completed leaf and refresh its complete API.
- [x] Record exact paper/Lean coverage, authoritative lint diagnostics,
  exhaustive current card inventory, and owned scratch cleanup.

The direct deep prior-research search returned twenty candidate lemmas and
twenty source arguments; all were inspected. Inventory coverage is complete
and `partial` is false, but compiler metadata is mostly pending/source-only,
refresh is incomplete because the background indexer is running, and semantic
coverage was not measured. Current-toolchain source checks remain required.
The existing `HedenmalmEssentialInverseFlowTrace.lean` already defines the
literal theta contour projection and certifies its complete finite root range.
The existing generalized-eigenvector contour lemma applies directly at zero:
the chosen radius is strictly below the nonzero spectral point's norm, and
each actual derivative is killed by a finite power of the compact inverse.
Continuity and closed-span minimality then kill the whole history. This is
the same paper mechanism without additional projector premises or duplicate
radius choices. The unfinished history card remains Stage 2.

### Literal derivative-history Riesz checkpoint

`HedenmalmThetaDerivativeHistoryRiesz.lean` certifies 24 public declarations.
It reuses the actual compact theta contour projector, whose chosen radius
excludes zero. The finite zero-Jordan power law and existing contour lemma
annihilate every derivative generator; closed-kernel minimality annihilates
their entire closed history. The literal projector factors as a bounded map
out of the actual quotient and induces a commuting idempotent there.

Both full and quotient projectors give topological range/kernel direct sums.
The quotient projector's range is exactly its complete nonzero generalized
root block. Its kernel is exactly the quotient image of the original kernel.
Quotient projection itself gives the equivalence of both finite Riesz ranges,
preserves the source operator action, and retains analytic Xi multiplicity
at every divisor-support point. The exact contour argument and decomposition
are recorded on the paper card. The card remains Stage 2, with bounded left
Fourier functional, sharp real translation/closed-span law, finite positive
prime translation exclusion, all positive-weight properness, dense unweighted
endpoint, tempered annihilator/multiplicity jets, and rapid quotient
eigenmode decay still pending.

Only the needed existing projector leaf and new Riesz leaf were built.
The final new native leaf build and direct source audit passed without
warnings. A 22-name infrastructure witness and a 24-export witness passed.
All 24 new exports and seven existing capstones have 31 complete axiom
reports: 31 expected, 31 reported, no missing/extra declarations, and only
`propext`, `Classical.choice`, and `Quot.sound`. The leaf is wired into
`RHTower.lean`; generated API, gaps, overview, and lexical index were
refreshed. All 24 exports are catalogued, with no missing or extra entries.
The `index` command already refreshes the lexical index; a separate final
`search-index` check reported zero changed and zero removed files. Future
unchanged checkpoints do not need both refresh commands.

The operator-indexed spectral subtype makes a direct operator rewrite under
its scalar coercion ill-typed. The certified bridge uses `congrArg` on
`fun T => maxGenEigenspace T.toLinearMap (mu : ℂ)`. Idempotence reduces to
an equality, so the conversion to linear-map idempotence uses the explicit
`ContinuousLinearMap.IsIdempotentElem.toLinearMap` name. Range membership
proofs use `change` to the continuous application before rewriting its
quotient action.

Authoritative formal lint exits 1 on twenty unrelated unreachable RHTower
leaves: `CCMApertureChainProfile`, `CCMApertureTranslationChains`,
`CCMExponentialRampPrimeMoment`, `CCMExponentialRampSourceDissipation`,
`CCMExponentialRampTerminalEntropy`, `CCMRetainedChainKernelLower`,
`DeBruijnTopZeroVelocity`, `MoebiusMollifiedCriticalMoment`,
`MoebiusMollifiedErrorThreeLines`, `RiemannAutocorrFourier`,
`ThetaMovingShellFirstOrderPhase`, `WeilDeviationBumps`,
`WeilDeviationDecomposition`, `WeilDeviationFejerTest`,
`WeilDeviationPacketLimit`, `WeilDeviationSpectralPairing`,
`WeilDeviationTranslationBound`, `WeilFullConeNearNullPositiveDefinite`,
`XiRealZeroFejerSum`, and `ZetaZeroDensityPowerSaving`. All diagnostics
were inspected; none belongs to the new owned leaf. Baseline large-file
warnings remain. Global lint is not green.

The exhaustive current inventory contains 99 Stage 2 Markdown files:
nine support files and 90 theorem cards. Every current path is queued.
New `11-rh-zero-divisor-geometry/weil-cone-zero-free-window-rigidity.md`
and `li-clock-damped-endpoint-sum-rule.md` are queued for exact audit.
The finite eta-deflation and off-line negative-response cards moved
externally to Stage 3; their complete certificate audits remain pending.
This checkpoint does not promote a partial card or complete the recursive goal.

Next missing clause has existing candidate infrastructure. Both direct
prior-research searches were inspected across all twenty candidate lemmas
and all twenty source arguments. The first search was non-partial but mostly
unrelated. A Hedenmalm-filtered search returned useful source hits but was
partial because semantic retrieval timed out within its budget. Inventory
coverage is complete; compiler statuses remain source-only/not-checked,
refresh is incomplete, and semantic coverage is unmeasured. The available
hits, rather than an inferred completeness claim, guide the next audit.

`HedenmalmShiftedCokernel.lean` already defines
`HedenmalmClosedWeightedDerivative.thetaCokernelFunctional` as the bounded
inner-product functional of the actual weighted conormal. Its source vector
is admitted for every complex parameter using all exponential moments; the
literal inner-product/integral bridge is at lines 149–181, the functional
at 307, its source-forcing identity at 314, and surjectivity at 349.
`HedenmalmQuantileRootMode.lean:90` defines the exact character `exp(i z x)`.
`HedenmalmShiftedClosedWeightedDerivative.lean:38` defines the bounded
shifted map as `subtype + z • thetaCenteredSourceInverse`, and
`HedenmalmClosedWeightedDerivative.lean:76` defines that inverse as the
restriction of the actual compact inverse. At a Xi zero, the forcing
identity should kill the source-density component, allowing the centered
annihilation identity to extend to the whole space. These are audited source
candidates, not yet current-toolchain certificates for the card's missing
left-functional clause. Verify their names and exact instances in scratch
before new Lean code; do not import a source-only claim as proven coverage.

Checkpoint cleanup removed twelve explicit owned scratch paths and verified
each absent. All owned foreground commands have terminal exit results;
no owned Lean/build or search/lint job remains running. External jobs and
their files were left untouched. The full recursive goal remains active.

### Literal bounded left Fourier functional work plan

- [x] Check current cokernel and all-shift infrastructure in this toolchain.
- [x] Identify the bounded functional with the literal source Fourier
  integral for every complex parameter and every actual source vector;
  certify the admitted test vector's exact value `M`.
- [x] Derive the full centered-primitive Fourier identity and every actual
  derivative transform; annihilate the complete closed history at Xi zeros.
- [x] Descend the nonzero functional to the literal quotient and certify
  its exact reciprocal left eigenvalue law.
- [x] Build only needed leaves; directly audit final source, all exports
  and axioms; wire and index, inspect formal lint, preserve full queue,
  record exact coverage, and clean owned scratch.

The construction reuses the actual bounded conormal functional, not a new
functional premise. Its weighted inner-product formula identifies the
ordinary Lebesgue Fourier integral. The canonical conormal at conjugate
parameter gives `k exp(-izx)` and has exact Fourier value `M`. The old
shifted-range kernel identity first supplies the left-action law on
centered inputs; separating the actual source-density vector supplies the
full mass correction. Applying this identity to the certified zero-Jordan
chain gives every derivative transform, after which closed-kernel minimality
annihilates history and the literal quotient lift gives the left eigenfunctional.
All source candidates require the current native/API checks before they
count as a certificate. The unfinished card remains Stage 2.

The current direct `thetaCokernelFunctional` prior-research query returned
two declarations, two candidate lemmas and two source arguments; all were
inspected. Inventory coverage is complete and `partial` is false, but
compiler freshness is mixed/pending/stale/source-only and semantic coverage
is unmeasured. Both needed native infrastructure leaves,
`HedenmalmShiftedCokernel` and `HedenmalmShiftedSourceEquation`, now build in
this toolchain. A 44-name scratch API witness passes. The existing exact
source-equation bridge identifies the actual compact inverse's pulled-back
output with the literal centered primitive for every full-space input.
The new Fourier leaf's native build and final direct source audit pass
without warnings. Its exhaustive 35-export witness also passes. The
complete axiom, generated-index, formal-lint and checkpoint results are
recorded below.

### Literal Fourier functional checkpoint

`HedenmalmThetaDerivativeHistoryFourier.lean` closes the exact bounded-left-
functional clause with 35 public declarations. Its source-space continuous
linear map is the existing actual theta conormal functional transported
by the actual quantile unitary. The weighted inner-product formula gives
the ordinary Fourier integral for every complex parameter and every source
vector. The admitted conjugate-parameter conormal is exactly
`k(x) exp(-izx)` almost everywhere, and its Fourier value is exactly the
positive mass `M`.

The complete shifted-range/kernel identity proves
`L_z(f) + z L_z(Bf) = 0` on the centered Hilbert hyperplane. Subtracting
the actual source-density vector, whose compact inverse is zero, proves
the full mass correction for arbitrary inputs. The existing exact
source-equation bridge then proves the literal physical integral identity
for `sourceInverse`, including the reciprocal formula at every `z ≠ 0`.
All source inputs, primitive outputs, and ordinary derivatives are
integrable under every complex Fourier tilt. Applying the centered law
to the actual zero-Jordan chain proves every transform
`L_z(k^(n)) = (-iz)^n XiC(z)`. At actual Xi zeros, closed-kernel minimality
kills the entire history. Its literal quotient lift has the same exact
mass test, is surjective and nonzero, and satisfies the full left
eigenvalue law `L̄_z(B̄f) = -z⁻¹ L̄_z(f)` on every quotient vector.
No source-admission, density, analytic continuation, zero-location or RH
premise was added.

The two necessary old infrastructure native targets and the new native
leaf target pass. Final `lake env lean FILE` source audit passes without
warnings. The 44-name infrastructure and 19-name remaining mathlib scratch
witnesses pass, as does the exhaustive 35-export witness. All 35 exports
and seven existing analytic capstones give 42 complete axiom reports
containing only `propext`, `Classical.choice`, and `Quot.sound`. The leaf
is wired into `RHTower.lean` exactly once. The single generated `index`
refresh passes, including its lexical refresh; all 35 owned declarations
are present in `formal/LEAN_API.md`. No full or umbrella build was run.

Authoritative final lint exits 1 on 25 other unreachable RHTower modules:
`CCMApertureChainProfile`, `CCMApertureTranslationChains`,
`CCMExponentialRampPrimeMoment`, `CCMExponentialRampSourceDissipation`,
`CCMExponentialRampTerminalEntropy`, `CCMRetainedChainKernelLower`,
`DeBruijnBarrierZerosSimple`, `DeBruijnHeatLocalModel`,
`LiEvenCrossActualClockDampedResolvent`, `MoebiusMollifiedCriticalMoment`,
`MoebiusMollifiedErrorThreeLines`, `RiemannAutocorrFourier`,
`ThetaMovingShellFirstOrderPhase`, `WeilDeviationBumps`,
`WeilDeviationDecomposition`, `WeilDeviationDeficitMeanVanishes`,
`WeilDeviationFejerTest`, `WeilDeviationPacketDecomposition`,
`WeilDeviationPacketEstimates`, `WeilDeviationPacketLimit`,
`WeilDeviationSpectralPairing`, `WeilDeviationTranslationBound`,
`WeilFullConeNearNullPositiveDefinite`, `XiRealZeroFejerSum`, and
`ZetaZeroDensityPowerSaving`. All errors were inspected; no lint diagnostic
names the owned Fourier leaf. Global lint is not green. The 170 baseline
large-file warnings remain outside this leaf's scope.

Final exhaustive inventory still contains 99 Stage 2 Markdown files:
nine support files and 90 theorem cards. Every current path is queued.
The theta history card remains Stage 2: sharp translation boundary and
local-translation history, full positive-weight properness and unweighted
endpoint collapse, tempered annihilator classification with multiplicity
jets, and rapid normalized quotient eigenmode decay still require complete
exact certificates. The recursive goal remains active; no partial card
was promoted.

Checkpoint cleanup removed nineteen explicit owned scratch paths and
verified every path absent. New leaf whitespace and scoped diff checks
pass. Every owned foreground command has a terminal exit result; no owned
Lean/build, index, lint or scratch job remains running. External jobs and
files were left untouched. Cross-session memory records exact coverage,
toolchain details, the complete recursive queue, and remaining obligations.

### Sharp real translation boundary and complete history orbit work plan

- [x] Check prior research, actual tail/weighted-family infrastructure,
  and every required current-toolchain API.
- [x] Prove literal real and complex `L²(k^(-q) dx)` shift admission iff
  `q < 2 exp(-2|a|)` for every positive `q`, with equality excluded.
- [x] Prove every admitted real shift, including negative shifts, belongs
  to the actual weighted derivative history.
- [x] Prove every actual derivative lies in the closed span of admitted
  real shifts, then exact equality of both closed histories for
  every `0 < q < 2`; record the literal `log(2/q)/2` boundary and `q=1` case.
- [x] Certify the paper's full open connected complex domain and the
  literal Hilbert-holomorphic translation map on that domain.
- [x] Check needed leaves, final sources, all exports and axioms; wire,
  index, inspect authoritative lint, preserve the full recursive queue,
  update paper/memory and clean owned scratch.

The direct prior-research query returned six candidate lemmas and six
source arguments; all were inspected. Inventory coverage is complete,
`partial` is false, semantic coverage is unmeasured, compiler freshness
is mixed/pending/stale/source-only, and refresh remains incomplete.
Useful source candidates are the existing explicit Gaussian envelope,
all-parameter real tail ratio, local holomorphic weighted family and
its exact derivative jets. The old history membership theorem covers
nonnegative real shifts only. Strict complex rectangles centered at zero
cover either sign directly. On the dangerous cusp, the literal energy
has positive limiting ratio to the exact envelope, which stays bounded
below at and above the boundary. The reverse closed-span inclusion
uses bounded duals: a functional zero on all admitted real shifts is
zero near the complex origin by analytic isolated-zero uniqueness,
so all its actual derivative jets vanish. Current-toolchain verification
and the exact original-carrier transport are now complete below.
The full history card remains Stage 2. Its separate inter-weight bounded
translation/operator-norm classification, graded finite prime/Euler words,
positive-weight properness/unweighted collapse, tempered annihilator jets
and rapid quotient decay remain exact obligations.

`ThetaRealShiftHistory.lean` now has a successful warning-free native
leaf build and final direct source audit. Its exact boundary and both
closed-span inclusions are proved for the literal full source; negative
shifts and equality failure are included. A 61-name infrastructure/mathlib
scratch witness passes. Complete export/axiom/index/lint gates remain,
alongside the full complex-domain holomorphy construction recorded above.

`ThetaWeightedTranslationDomain.lean` now builds without warnings in its
19-declaration final form. The full Gaussian-slack domain is open and
star-convex, hence path connected when `q < 2`. Every point has a strict
enclosing rectangle with one genuine weighted `L²` majorant. The actual
full-domain translation family is Hilbert-holomorphic, has the actual
ordinary theta derivatives as origin jets, and lies in derivative history
throughout the connected domain. The `q=1` measure is proved equal to the
literal Hedenmalm source measure; the sharp source-carrier membership
theorem is stated explicitly. A 22-name domain API witness and 12-name
additional witness pass. Final direct source and exhaustive certificate
gates follow.

Before counting the original quantile-history identity as complete,
transport both literal weighted origin jets and admitted real translation
classes through the actual quantile unitary. Construct the canonical
measure-equality isometry, verify its representatives, then prove both
closed-span inclusions using the already certified bounded-dual criterion.
This is a required identification, not a new history premise.

The fresh recursive census finds two new Stage 2 cards. Both join the
unbounded exact-certificate queue; their paper status is not a Lean audit.

| Stage 2 path | Audit status |
|---|---|
| `li-clock-first-prefix-gamma-exact-sign.md` | moved externally to Stage 3; complete exact certificate audit pending |
| `li-clock-positive-gamma-dyadic-completion.md` | moved externally to Stage 3; complete exact certificate audit pending |
| `li-clock-completion-arithmetic-cancellation-boundary.md` | moved externally to Stage 3; complete exact certificate audit pending |
| `li-clock-contiguous-comparison-window.md` | moved externally to Stage 3; complete exact certificate audit pending |
| `li-clock-finite-partition-volterra-positive-area.md` | moved externally to Stage 3; complete exact certificate audit pending |
| `li-clock-joint-arithmetic-cancellation-window.md` | moved externally to Stage 3; complete exact certificate audit pending |
| `li-clock-partition-density-ratio-endpoint-boundary.md` | moved externally to Stage 3; complete exact certificate audit pending |
| `li-clock-positive-borel-ratio-transfer.md` | moved externally to Stage 3; complete exact certificate audit pending |
| `11-rh-zero-divisor-geometry/weil-cone-finitely-generated-support-rigidity.md` | newly added; complete exact certificate audit pending |
| `11-rh-zero-divisor-geometry/weil-cone-first-zero-window-lacunary-rigidity.md` | moved externally to Stage 3; complete exact certificate audit pending |
| `li-clock-infinite-partition-density-tail-boundary.md` | newly added; complete exact certificate audit pending |
| `li-clock-partition-relative-volterra-forcing.md` | newly added; complete exact certificate audit pending |

The original-carrier bridge is certified in
`ThetaQuantileTranslationHistory.lean` (23 public declarations). The canonical source translation
class is the proved measure-congruence transport of the actual weighted
class; its separate literal `toLp` identity discharges source admission.
Derivative classes and both vector families have exact physical and
quantile identifications. Closure transport is factored through abstract
isometry preimages and direct `Lp` measure-congruence lemmas. An isolated
kernel timeout exposed expensive transport of the whole isometry structure.
The isometry now casts the vector directly and proves linearity and norm
preservation separately. Both concrete theta `toLp` specialization tests
pass, and all six generic measure-congruence declarations build. No
heartbeat or depth limits were changed. Both original physical and
quantile closed-span inclusions are exact; the actual quotient kills
every admitted local translate. Prime-word
exclusion includes arbitrary complex coefficients by real/imaginary
components, with zero coefficients removed before the terminal-prime audit.

The final named bridge build `lake build --old
GaloisForLFunctions.RHTower.ThetaQuantileTranslationHistory` passes in
12 seconds without leaf warnings. A prior default build was stopped after
it began unrelated dependency refreshes; its completed generic cast leaf
built successfully. All four final direct source audits pass with empty
logs. The exhaustive export witness checks all 69 declarations across
the four leaves (6/21/19/23); all 69 and eight existing analytic/transport
capstones have 77 complete axiom reports containing exactly the standard
three axioms. The five earlier infrastructure witnesses plus the explicit
cast prototype cover 145 API entries. Every public export is present in
`formal/LEAN_API.md`, every leaf has exactly one umbrella import, and
`scripts/formal_tools.py index` refreshes the generated catalogue and
lexical index. No umbrella build or numerical experiment ran.

Authoritative `scripts/formal_tools.py lint` reports 170 existing large-file
warnings and these 15 other unreachable modules; none concerns the four
new leaves:

```text
GaloisForLFunctions.RHTower.CCMApertureChainProfile
GaloisForLFunctions.RHTower.CCMApertureTranslationChains
GaloisForLFunctions.RHTower.CCMExponentialRampPrimeMoment
GaloisForLFunctions.RHTower.CCMExponentialRampSourceDissipation
GaloisForLFunctions.RHTower.CCMExponentialRampTerminalEntropy
GaloisForLFunctions.RHTower.CCMRetainedChainKernelLower
GaloisForLFunctions.RHTower.LiClockPairedEtaCompletionAsymptotic
GaloisForLFunctions.RHTower.MoebiusMollifiedCriticalMoment
GaloisForLFunctions.RHTower.MoebiusMollifiedErrorThreeLines
GaloisForLFunctions.RHTower.Sieve.BarbanVehovGcdFormSharp
GaloisForLFunctions.RHTower.ThetaMovingShellFirstOrderPhase
GaloisForLFunctions.RHTower.XiLaguerreShadowDensity
GaloisForLFunctions.RHTower.ZetaGateProductAFESharpHighBlock
GaloisForLFunctions.RHTower.ZetaOffLineMomentExplicit
GaloisForLFunctions.RHTower.ZetaZeroDensityPowerSaving
```

Global lint remains non-green. All 15 diagnostics were inspected and
recorded; no unrelated module was edited to clear this gate. The original
history card retains every remaining exact obligation and stays Stage 2.

The fresh census has 100 current Stage 2 Markdown files: nine support files
and 91 theorem cards, all queued. The historical queue also retains ten
externally moved Stage 3 candidates whose complete exact-certificate audits
remain pending, alongside the five owned whole-card certifications. The
newly moved zero-free-window rigidity, damped endpoint sum-rule, first-prefix
gamma sign, and positive-gamma dyadic completion cards are marked explicitly;
external promotion is not counted as certification.

Scoped whitespace checks pass. The card and cross-session memory record
the exact completed clauses and every remaining obligation. All 49
explicitly owned translation-checkpoint scratch files were removed by a
finite guarded manifest, with absence verified. No owned Lean job remains.

### Graded finite arithmetic/Euler history work plan

- [x] Check prior research and literal finite arithmetic/Euler sources.
- [x] Construct one positive weight admitting the whole finite word.
- [x] Identify its literal `toLp` class and prove membership in actual
  weighted derivative history, then zero class in that history quotient.
- [x] Discharge the finite prime/Euler specializations without an added
  source-admission premise.
- [x] Run targeted native/direct/export/axiom/index/lint gates; update the
  exact coverage map, queue and memory, then clean owned scratch.

Paper closure for this clause: for a finite arithmetic alphabet `D`, set
`q_D = exp(-2 * Σ_(d∈D) |log d|)`. Each summand is nonnegative, so
`0 < q_D ≤ 1 < 2`; each individual absolute log is at most the sum, hence
`q_D ≤ exp(-2|log d|) < 2 exp(-2|log d|)`. Every literal shift is therefore
admitted at this single weight. Finite complex linear combinations are
admitted and belong to the actual closed derivative submodule, because
their `toLp` classes are the corresponding finite sums of actual shift
classes. The submodule quotient kills each such sum. Apply the same
construction to all squarefree words of the actual finite Euler deletion;
its previously certified Möbius expansion gives the literal Euler source,
including the empty prime alphabet. A singleton prime word is in that
squarefree alphabet, so this weight admits every individual prime letter
and the entire Euler word simultaneously. No nonzero-coefficient or
source-admission premise is needed.

Prior research: the hybrid query's 20 candidate lemmas and 20 source
arguments were inspected; inventory is complete, `partial=false`, semantic
coverage unmeasured and compiler freshness mixed/source-only. The lexical
OR follow-up returns the exact existing finite arithmetic/Euler history
lemmas. Both current source proofs were read; their weight-margin premise
is now discharged explicitly. The 40-entry API witness passes. The new
`ThetaGradedFiniteHistory.lean` leaf has 20 public declarations and passes
its native named build in 19 seconds without leaf warnings, exact final
direct source check, and exhaustive 20-export witness. All 20 declarations
and six prior analytic/transport capstones have 26 complete axiom reports
containing exactly `propext`, `Classical.choice`, and `Quot.sound`. The
explicit literal `toLp` classes equal their actual finite translation sums;
one coefficient-independent weight handles arbitrary complex coefficients,
empty support and cancellation. The actual Euler source and every prime
letter share a single carrier and have zero history quotient class.
No admission, nonzero terminal coefficient, density or RH premise was added.
The leaf has exactly one umbrella import and all 20 exports appear in the
regenerated catalogue. Index refresh includes the lexical index.

Authoritative lint now has 170 large-file warnings and these 14 other
unreachable modules, with no finding on this leaf or the four earlier
translation leaves:

```text
GaloisForLFunctions.RHTower.CCMApertureChainProfile
GaloisForLFunctions.RHTower.CCMApertureTranslationChains
GaloisForLFunctions.RHTower.CCMExponentialRampPrimeMoment
GaloisForLFunctions.RHTower.CCMExponentialRampSourceDissipation
GaloisForLFunctions.RHTower.CCMExponentialRampTerminalEntropy
GaloisForLFunctions.RHTower.CCMRetainedChainKernelLower
GaloisForLFunctions.RHTower.LiClockPairedEtaFinitePartitionVolterra
GaloisForLFunctions.RHTower.MoebiusMollifiedCriticalMoment
GaloisForLFunctions.RHTower.MoebiusMollifiedErrorThreeLines
GaloisForLFunctions.RHTower.ThetaMovingShellFirstOrderPhase
GaloisForLFunctions.RHTower.WeilDeviationLineRepresentation
GaloisForLFunctions.RHTower.WeilRegularDeviationRigidity
GaloisForLFunctions.RHTower.ZetaFixedSigmaDensity
GaloisForLFunctions.RHTower.ZetaZeroDensityPowerSaving
```

Every diagnostic was inspected. Global lint remains non-green; no unrelated
source was edited to clear it. The latest recursive census has 99
Stage 2 Markdown files, nine support and 90 theorem cards, all queued.
The newly added joint arithmetic cancellation-window card is queued;
the previous completion/arithmetic cancellation-boundary and finite-partition
Volterra area cards moved externally to Stage 3 and remain exact-audit pending. Seventeen historical
queue cards have unique Stage 3 matches: five owned whole-card certificates
and twelve external promotions still awaiting full exact audits.
The whole history card stays Stage 2 with (5), (7), (8) and rapid normalized
quotient decay still open. These five new leaves supply 89 fully audited
public declarations across the two completed construction blocks.

Card and memory coverage are updated; scoped whitespace passes. All 21
explicitly owned finite-history scratch files were removed through a finite
guarded manifest, with absence verified. No owned Lean job remains.

### Positive-weight properness and unweighted endpoint work plan

- [x] Check prior research, existing ordinary theta `L²` cyclicity,
  literal density unitaries and actual real Xi-zero certificates.
- [x] Construct the literal bounded real Fourier evaluation for
  `0 < q < 2`; discharge its integrability from the complementary
  exponent `2-q`, rather than add an admission premise.
- [x] Identify every actual derivative's transform, annihilate its
  closed history at a real Xi zero, and prove that history is proper.
- [x] Identify the actual `q=0` measure, derivative representatives and
  holomorphic translation orbit, then prove dense endpoint history.
- [x] Run the complete exact certificate gates, preserve the recursive
  queue, update card/memory and clean owned scratch.

### Exact weighted properness and endpoint certificate checkpoint

`ThetaWeightedHistoryProperness.lean` contains 17 public declarations.
The complementary exponent `2-q` proves the literal positive moment and
phase-source admission. Actual density unitaries cancel their square-root
weights, so the continuous functional equals `∫f exp(itx)`. Its source test
has value `M>0`; every actual derivative has transform `(-it)^n XiC(t)`.
Hardy's actual real zero proves properness for all `0<q<2`.

`ThetaUnweightedDerivativeHistory.lean` contains 18 public declarations.
The literal endpoint measure equals Lebesgue measure; its canonical
isometry preserves representatives. The strengthened Gaussian rectangle
majorant includes `q=0`, with the old strict-positive signature preserved.
Actual dominated sections give Hilbert holomorphy throughout the full
connected strip. Their jets equal actual ordinary derivative generators,
so their closed span includes every real translate. Exact `2π` dilation
transfers the existing normalized cyclicity certificate to the literal
unscaled orbit. The actual endpoint history is therefore top. Capstone
`thetaDerivativeHistory_endpoint_dichotomy` proves both halves of (7).

All 36 new public declarations (17+18+one majorant strengthening) pass the
exhaustive export witness. Named native leaf builds pass; endpoint build
also rebuilt the final properness leaf. Three final literal `lake env lean
FILE` checks pass with empty logs. All 36 exports plus ten prior capstones
have 46 complete axiom reports, each containing exactly `propext`,
`Classical.choice`, `Quot.sound`. The final 63-entry API witness passes.
Both new leaves occur exactly once in `RHTower.lean`; all 36 exports occur
in the regenerated catalogue with their exact owner modules. Catalogue
names are unqualified, so verification matches name and module together.
Index refresh includes the lexical index (five changed sources, no removals).
Scoped whitespace and both new untracked-source whitespace checks pass.

The full history card stays Stage 2. Remaining exact clauses: inter-weight
translation boundedness and operator norm (5), full tempered annihilator
classification with multiplicity jets (8), and rapid normalized quotient
eigenmode decay. No partial-card promotion, additional analytic/source
admission premise, RH premise, computational certificate, heartbeat hack,
subagent, full/umbrella build or commit is used.

Authoritative final lint exits 1: all 170 warnings are baseline large-file
warnings; ten other leaves remain unreachable, with no owned-leaf finding:

- `GaloisForLFunctions.RHTower.CCMApertureChainProfile`
- `GaloisForLFunctions.RHTower.CCMApertureTranslationChains`
- `GaloisForLFunctions.RHTower.CCMExponentialRampPrimeMoment`
- `GaloisForLFunctions.RHTower.CCMExponentialRampSourceDissipation`
- `GaloisForLFunctions.RHTower.CCMExponentialRampTerminalEntropy`
- `GaloisForLFunctions.RHTower.CCMRetainedChainKernelLower`
- `GaloisForLFunctions.RHTower.MoebiusMollifiedCriticalMoment`
- `GaloisForLFunctions.RHTower.MoebiusMollifiedErrorThreeLines`
- `GaloisForLFunctions.RHTower.ThetaMovingShellFirstOrderPhase`
- `GaloisForLFunctions.RHTower.ZetaZeroDensityPowerSaving`

Global lint is non-green. Recursive census: 99 Stage 2 Markdown files,
nine support files and 90 theorem cards; zero unqueued paths. Two new LI
ratio/endpoint cards are queued. Contiguous-comparison and joint-arithmetic
window cards moved externally and remain complete-audit pending. The
historical queue has 19 unique Stage 3 matches: five owned whole-card
certifications and fourteen external promotions requiring exact audits.

### Sharp inter-weight translation work plan

- [x] Check prior research, literal two-tail envelopes and existing
  bounded-multiplier/source-metric infrastructure in this toolchain.
- [x] Prove the actual density-ratio two-tail law and strict threshold,
  including dangerous-tail equality failure and the zero-shift boundary.
- [x] Construct the actual bounded translation between weighted carriers
  and prove necessity without an added admission/operator premise.
- [x] Identify its squared operator norm with the literal density-ratio
  essential supremum; discharge every paper specialization.
- [x] Run exact native/direct/export/axiom/index/lint gates, update the
  complete coverage ledger and clean owned scratch.

Initial Theta-filtered hybrid search inspected all 20 candidate lemmas and
20 source arguments. It was nonpartial with complete inventory; sources
were source-only/not-checked and the background refresh was incomplete.
Useful material includes actual density unitaries, bounded multipliers,
and the old fixed-carrier theta shift obstruction. These are ingredients,
not a complete sharp transport certificate. The broader recursive goal
remains active and unbounded.

`ThetaTranslationDensityRatio.lean` passes the literal direct Lean check.
Its 20 public declarations prove the actual first-atom relative limit,
both strict-margin tail limits, dangerous-tail blow-up beyond the boundary
and at equality, and the exact bounded-ratio classification for every
shift. Positive output exponent is the sole exponent premise in the
nonzero-shift classification; the zero-shift classification holds for all
real exponents. Native/export/axiom/index gates remain open for this leaf.
This scalar classification alone does not discharge paper clause (5).

The second, multiplier-filtered deep search inspected all 20 candidate
lemmas, all 20 source arguments and its one ingredient set; it returned
no proof ideas. Coverage was complete/nonpartial, with unchecked source
status and incomplete background refresh. Existing multipliers supply
construction and upper bounds, but not the required necessity or exact
essential-supremum norm. The next proof uses actual finite-interval
indicators in ordinary complex Lebesgue L², then conjugates with the
already verified theta density unitaries.

### Exact inter-weight translation certificate checkpoint

The actual sharp translation law (5) is now certified. Three new leaves
contain 52 public declarations: `LpContinuousMultiplierNorm.lean` has
four theorems, `ThetaTranslationDensityRatio.lean` has 20 declarations,
and `ThetaInterWeightTranslation.lean` has 28 declarations. Total: six
definitions and 46 theorems.

The scalar leaf proves the actual two-cusp envelope law, strict-margin
decay and dangerous-tail divergence, including the zero Gaussian
coefficient at equality. The generic norm leaf tests the actual operator
on positive-volume finite-interval indicators and identifies the exact
essential supremum. The operator leaf constructs literal translations
with the already verified density unitaries. Conversely every bounded
operator satisfying the actual representative law forces a bound on the
literal density ratio. The existence iff statements therefore add no
admission or operator-existence premise to the paper theorem.

The exact certificate includes all shifts, the zero-shift boundary,
unique actual operators, the squared essential-supremum norm as both
extended-nonnegative and real equalities, failure at dangerous-tail
equality, absence of nonzero fixed-weight translations, and the exact
prime inequality `q'<q/p²`. Positive output exponent alone suffices for
the nonzero-shift theorem, so it covers the paper's positive input and
output exponents without weakening the result.

Named native builds of all three leaves pass. The operator leaf's final
native build took 8.4 seconds. Three final literal `lake env lean FILE`
checks pass with empty logs. All 52 declarations pass the exhaustive
export witness; all 52 plus eight prior capstones give 60 complete axiom
reports, each containing exactly `propext`, `Classical.choice`, and
`Quot.sound`. The 105-entry API witness passes. Scoped tracked whitespace
and each new untracked-source whitespace check pass.

All 52 exact name/module pairs occur in `formal/LEAN_API.md`. Each leaf
has exactly one import in its own theorem-area umbrella. Initial lint
found a missing HTGeometry registration for the generic norm leaf;
that owned defect was fixed and the authoritative lint rerun confirms
zero owned-leaf findings. Final catalogue and lexical-index refresh
reports three changed sources and no removals.

Authoritative final lint exits 1: 170 baseline large-file warnings and
13 other unreachable leaves remain:

- `GaloisForLFunctions.RHTower.CCMApertureChainProfile`
- `GaloisForLFunctions.RHTower.CCMApertureTranslationChains`
- `GaloisForLFunctions.RHTower.CCMExponentialRampPrimeMoment`
- `GaloisForLFunctions.RHTower.CCMExponentialRampSourceDissipation`
- `GaloisForLFunctions.RHTower.CCMExponentialRampTerminalEntropy`
- `GaloisForLFunctions.RHTower.CCMRetainedChainKernelLower`
- `GaloisForLFunctions.RHTower.MoebiusMollifiedCriticalMoment`
- `GaloisForLFunctions.RHTower.MoebiusMollifiedErrorThreeLines`
- `GaloisForLFunctions.RHTower.RiemannKernelModulatedWindowTests`
- `GaloisForLFunctions.RHTower.ThetaMovingShellFirstOrderPhase`
- `GaloisForLFunctions.RHTower.ZetaNotchDualCarrier`
- `GaloisForLFunctions.RHTower.ZetaNotchDualContour`
- `GaloisForLFunctions.RHTower.ZetaZeroDensityPowerSaving`

Global lint remains non-green. The exhaustive recursive census contains
100 Stage 2 Markdown files: nine support files and 91 theorem cards, with
zero unqueued paths after adding both new Weil support/window cards.
The positive Borel ratio card moved externally and remains complete-audit
pending. Historical queue matches 20 unique Stage 3 cards: five owned
whole-card certifications and 15 external promotions needing exact audits.

The history card stays Stage 2. Exact remaining obligations are the full
tempered annihilator classification with multiplicity jets (8) and rapid
normalized quotient eigenmode decay. Whole recursive goal remains active
and unbounded. No subagent, computational certificate, heartbeat/depth
hack, full/umbrella build or commit was used. The prior endpoint work's
23 owned scratch files have been removed and their absence verified.

All 26 owned transport scratch files were removed through the exact
finite manifest after checking regular-file/non-symlink ownership.
The transport namespace's absence is verified; all owned processes exited.

### Full tempered annihilator work plan

- [ ] Check prior research and this toolchain's actual Schwartz/distribution
  infrastructure against every assertion in paper clause (8).
- [ ] Construct the actual theta translation curve in the Schwartz space,
  with every seminorm bound required for smoothness and analytic uniqueness.
- [ ] Prove annihilation of all literal theta derivatives iff the actual
  Fourier-transformed tempered distribution is killed by multiplication
  with XiC, without a replacement multiplier/admission premise.
- [ ] Classify the full kernel: local real-zero jets below exact
  multiplicity, compatible globally tempered sums, and exclusion of
  off-real evaluations from tempered functionals.
- [ ] Run exact native/direct/export/axiom/index/lint gates, retain the full
  recursive queue and separately preserve rapid quotient eigenmode decay.

The first deep search inspected all 20 candidates, all 20 source
arguments and its one ingredient set (zero proof ideas). It was
nonpartial, with complete 63,247-file inventory and no errors; retrieved
certificates were source-only/unchecked and background refresh remained
incomplete. A Theta-filtered OR/deep search also inspected all 20
candidates, all 20 arguments and its one ingredient set. That result
was partial, with text/source retrieval reported interrupted; the
63,250-file inventory was complete and background refresh incomplete.
Available hits are used as ingredients, not asserted as compiler-verified
or a complete solution to (8).

The actual `xiCSchwartz` restriction and normalized theta Fourier identity
already exist. The positive-form tempered-null theorems require momentum
symmetry and positivity and cannot replace (8) for arbitrary tempered
functionals. Existing scalar Schwartz coordinate division is a local
classification ingredient. Existing remote positive even packets prove
off-real Laplace discontinuity and are being lifted to the literal
complex Schwartz dual. Physical Fourier normalization must be retained:
the unscaled source transforms at `t/(2π)` to XiC(t), whereas the existing
normalized source has the direct mathlib-frequency transform XiC(t).
No source scaling is being silently substituted in (8).

The off-real scratch lift already passes: actual complex tempered
functionals cannot agree with the literal exponential evaluator even on
the embedded real Schwartz functions with entire Laplace transforms.
The negative boundary will be paired with the exact positive survivor:
for every real frequency the Fourier transform of the actual Dirac at
`-t/(2π)` gives that evaluator on every complex Schwartz function. The
full real/off-real existence iff is being checked; this subclause alone
does not certify the complete annihilator or multiplicity classification.

For the full curve, preserve the genuine Fréchet topology. Schwartz space
is controlled by all its seminorms; do not impose a norm or import a
Hilbert-analytic premise. One available bridge is the existing concrete
Schwartz Sobolev estimate: a tempered functional has a finite-seminorm
bound, and polynomial-weighted derivative seminorms can be controlled by
finitely many weighted L² derivatives. Actual dominated analytic theta
sections can then be tested through that derived Sobolev observer. The
source construction, observer extension and exact derivative identities
must be proved, not assumed.

### Exact tempered evaluation boundary certificate checkpoint

`ThetaTemperedEvaluationBoundary.lean` contains 11 public declarations:
four definitions and seven theorems. They exclude every literal off-real
Fourier–Laplace evaluator from the actual complex tempered dual, even
when agreement is required only on the complexification of real Schwartz
sources with entire Laplace transform. The stronger complex-domain
exclusion follows without any extra zero-location premise.

The positive survivor is proved exactly: for every real frequency `t`,
the actual Fourier transform of the Dirac distribution at `-t/(2π)`
equals the physical evaluator `∫ exp(itx) f(x) dx` on every complex
Schwartz function. Existence of a tempered extension on the entire
exponential domain is therefore equivalent to `Im z = 0`. This closes
the real/off-real evaluation boundary inside (8), not the complete
annihilator or multiplicity classification.

The named native build passes in 2.3 seconds. Final literal direct Lean
check and the 20-entry API witness pass with empty logs. Every one of the
11 public declarations passes the exhaustive export witness. All 11
exports plus four prior capstones have 15 complete axiom reports, each
containing exactly `propext`, `Classical.choice`, and `Quot.sound`.
All 11 exact name/module pairs occur in `formal/LEAN_API.md`; the leaf
is imported exactly once by its area umbrella. Scoped tracked and new
source whitespace checks pass. Final catalogue and lexical-index refresh
reports six changed sources and no removals.

Authoritative lint exits 1, with zero findings for this leaf. Global
diagnostics are 170 baseline large-file warnings and 18 unrelated
unreachable modules:

- `GaloisForLFunctions.RHTower.CCMApertureChainProfile`
- `GaloisForLFunctions.RHTower.CCMApertureTranslationChains`
- `GaloisForLFunctions.RHTower.CCMExponentialRampPrimeMoment`
- `GaloisForLFunctions.RHTower.CCMExponentialRampSourceDissipation`
- `GaloisForLFunctions.RHTower.CCMExponentialRampTerminalEntropy`
- `GaloisForLFunctions.RHTower.CCMRetainedChainKernelLower`
- `GaloisForLFunctions.RHTower.MoebiusMollifiedCriticalMoment`
- `GaloisForLFunctions.RHTower.MoebiusMollifiedErrorThreeLines`
- `GaloisForLFunctions.RHTower.ThetaMovingShellFirstOrderPhase`
- `GaloisForLFunctions.RHTower.XiSliceSaddleStrip`
- `GaloisForLFunctions.RHTower.ZetaNotchDiagonalSum`
- `GaloisForLFunctions.RHTower.ZetaNotchDualCarrier`
- `GaloisForLFunctions.RHTower.ZetaNotchDualContour`
- `GaloisForLFunctions.RHTower.ZetaNotchDualJets`
- `GaloisForLFunctions.RHTower.ZetaNotchDualOscillation`
- `GaloisForLFunctions.RHTower.ZetaNotchDualOscillationBound`
- `GaloisForLFunctions.RHTower.ZetaNotchDualWeightBounds`
- `GaloisForLFunctions.RHTower.ZetaZeroDensityPowerSaving`

The exhaustive current census has 100 Stage 2 Markdown files: nine
support files and 91 theorem cards. Both new infinite-partition/relative
Volterra cards are now queued, leaving zero unqueued paths. Two additional
external promotions are marked audit-pending. Historical queue matches
22 unique Stage 3 cards: five owned whole-card certifications and 17
external promotions requiring complete exact audits. No whole-card
promotion is claimed for this boundary certificate. The recursive goal
remains active and unbounded; (8) and rapid normalized quotient decay
remain explicit obligations.

All 13 owned tempered-boundary scratch files were removed through their
exact finite manifest after checking regular-file/non-symlink ownership.
Their namespace is absent; all owned processes have exited. The final
census after queue edits again confirms zero unqueued Stage 2 paths.

### Rapid normalized quotient eigenmode decay work plan

- [x] Audit prior research and actual canonical mode, normalization,
  derivative history and two-ended weighted tail bounds.
- [x] Prove repeated integration by parts for the literal theta
  derivative primitives, including their zero total integral at each
  actual Xi zero.
- [x] Derive a uniform actual `L²(k⁻¹dx)` remainder bound throughout
  `|Im z|≤1/2`, without replacing it by an admission/bound hypothesis.
- [x] Kill the finite derivative sum with the actual quotient map and
  prove, for every integer `A≥0`, `‖π f_z‖≤C_A(1+|z|)^(-A)` for
  actual Xi zeros with sufficiently large `|Re z|`.
- [x] Run exact leaf/export/axiom/catalogue/lint gates, record coverage
  and preserve the still-open full tempered annihilator classification.

The exact paper statement permits a sufficiently-large-real-part
threshold. The canonical mode is the existing literal `sourceModeF`,
whose integral is already proved equal to the source mass; no free
rescaling of eigenvectors is allowed. The actual source/quantile unitary
and history quotient must transport this mode and its derivative
remainder without silently changing the quotient norm.

The first rapid-decay deep search inspected all 20 candidate lemmas,
all 20 source arguments and its one ingredient set (zero proof ideas).
It was nonpartial, with complete 63,261-file inventory and no errors;
hits were source-only/unchecked and background refresh incomplete.
Generic eigenbasis/norm conservation results do not prove this bound.
The HedenmalmTheta-filtered OR/deep follow-up inspected all 20 candidates,
all 20 arguments and one ingredient set. It was partial with interrupted
text/source retrieval, complete 63,262-file inventory and incomplete
background refresh. Its useful exact ingredients are the actual
derivative Fourier integrals, derivative vectors, quantile unitary and
history quotient; none is a rapid-decay certificate by itself.

Existing source derivative ratios are moderate in the literal first-atom
scale. Combined with the complete theta tail envelope, this bounds every
derivative by an exponential times the same double-exponential source
envelope. At actual Xi zeros, every derivative's full modulated integral
vanishes, allowing the primitive to use the nearer tail. Those actual
bounds will supply the uniform weighted remainder, independent of the
real frequency. No numerical tail computation is involved.

The literal derivative-primitive scratch proof now passes with an empty
log. `HedenmalmThetaDerivativeOscillatoryPrimitive.lean` contains the
exact all-order finite source-mode expansion and actual oscillatory
remainder. Its named native build passes (23 seconds). Every actual Xi
zero kills the full modulated integral of every derivative, so either
tail represents the same primitive. Uniform weighted remainder bounds,
quotient decay and final exhaustive gates remain open.

The complete derivative-primitive bound scratch proof passes with an
empty log. `HedenmalmThetaDerivativePrimitiveBounds.lean` constructs one
actual nearest absolute-tail majorant for every derivative, continuous
and nonnegative, and proves its literal reciprocal-density L² energy
finite. Its norm bounds the actual oscillatory primitive's `toLp` class
uniformly for all real frequencies and all actual Xi zeros in
`|Im z|≤1/2`. The constant is the actual majorant norm, not a new bound
hypothesis. This closes the analytic remainder estimate; quotient
recurrence, rapid-decay capstone and final gates remain open.


### Exact canonical rapid quotient decay certificate (49 exports)

The rapid-decay block is now certified in three actual source leaves:

| Module | Public exports | Exact role |
| --- | ---: | --- |
| `HedenmalmThetaDerivativeOscillatoryPrimitive` | 12 | Literal oscillatory integrals, their all-order Fourier totals, zero-total right tails, exact primitive recurrence and finite source-mode expansion. |
| `HedenmalmThetaDerivativePrimitiveBounds` | 18 | Actual strip-uniform majorant, finite literal weighted energy, source-space admission and a constructed uniform norm constant. |
| `HedenmalmThetaQuotientEigenmodeDecay` | 19 | Literal source quotient, exact quotient remainder, canonical mean normalization, nonzero quotient mode and all-order rapid decay. |

Write `P_n(z,x)=exp(-izx)∫_{-∞}^x k^(n)(y)exp(izy)dy`.
The exact recurrence is `P_(n+1)=k^(n)-izP_n`. At an actual Xi
zero its integral representation can use either end. Throughout
`|Im z|≤1/2` it obeys the constructed pointwise bound
`|P_n(z,x)|≤B_n(x)`, where
`B_n(x)=exp(|x|/2)∫_{|x|}^∞ exp(|y|/2)|k^(n)(y)|dy`.
The actual full-source derivative ratios and double-exponential theta
bounds prove `∫ B_n²/k < ∞`, with no bound or admission premise.

The quotient is literally `H_s/(U⁻¹R)`. Its projection kills every
actual source derivative. Consequently the existing canonical source
mode, whose literal integral is `M`, satisfies exactly
`πf_z=-(-iz)^(-A)πP_(A+1)` for every natural `A`. The norm constant
is the actual norm of `B_(A+1)` in `L²(k⁻¹dx)`. Thus the paper's rapid
decay holds with explicit `C_A=2^A‖B_(A+1)‖` and threshold
`|Re z|≥1`, stronger than a merely sufficiently-large threshold.
The same actual quotient mode is nonzero. No rescaling, RH premise,
or assumed remainder bound appears.

All three named native builds pass, followed by final literal
`lake env lean FILE` checks with empty logs for each project leaf.
All 49 public exports have exact scratch witnesses and 49 matching
`#print axioms` reports, each exactly
`{propext, Classical.choice, Quot.sound}`. The fresh native `.ilean`
references supply 266 pinned API witnesses: 201 Mathlib names and
65 actual project dependencies; all compile with an empty log.
The generated catalogue contains exactly all 49 export/module pairs,
with no missing or extra pair. Each umbrella import appears once;
source whitespace and scoped `git diff --check` pass. Final index
refresh succeeds (1 changed, 0 removed).

Authoritative global lint exits 1: 170 existing large-file warnings,
29 unrelated unreachable modules, and one unrelated active proof-debt
finding. There are no diagnostics in the three owned leaves.
Unreachable modules: `CCMApertureChainProfile`, `CCMApertureTranslationChains`, `CCMExponentialRampPrimeMoment`, `CCMExponentialRampSourceDissipation`, `CCMExponentialRampTerminalEntropy`, `CCMRetainedChainKernelLower`, `MoebiusMollifiedCriticalMoment`, `MoebiusMollifiedErrorThreeLines`, `SmoothNumberLogSeries`, `ThetaMovingShellFirstOrderPhase`, `WeilNullPotentialSpectralPairing`, `XiSliceLogLogOrderDensity`, `XiSliceLogLogOrderPositivity`, `ZetaNotchBohrLift`, `ZetaNotchCriticalAFE`, `ZetaNotchCrudeTail`, `ZetaNotchDiagonalSum`, `ZetaNotchDualCarrier`, `ZetaNotchDualContour`, `ZetaNotchDualJets`, `ZetaNotchDualOscillation`, `ZetaNotchDualOscillationBound`, `ZetaNotchDualWeightBounds`, `ZetaNotchPairingInequality`, `ZetaNotchResonanceCount`, `ZetaNotchSmoothTest`, `ZetaNotchTwistedDiagonal`, `ZetaNotchTwistedOffDiagonal`, `ZetaZeroDensityPowerSaving`.
The proof-debt finding is exactly
`formal/GaloisForLFunctions/RHTower/XiSliceLogLogOrderDensity.lean:402`,
`sorry` in `eventually_volume_xiSliceCoeff_nonpos_loglog_le`.
Global lint is not claimed green; unrelated work is left untouched.

Fresh exhaustive recursive census: 100 Stage 2 Markdown files,
9 support files, 91 theorem cards, zero unqueued cards. Historical
Stage 3 matches remain 22 unique paths: 5 owned whole-card certificates
and 17 externally promoted cards still pending exact-proof audit;
no ambiguous basename match. No whole card is promoted here.
The history card remains Stage 2. Its remaining exact mathematical
obligation is the full tempered annihilator/multiplicity classification
(8); the real/off-real boundary is already certified.

Rapid-block scratch cleanup verified: all 27 explicitly owned files
removed after every owned process exited. The rapid scratch namespace
is absent. Evidence above is persisted before deletion. The unbounded
recursive objective continues with exact tempered clause (8).


### Actual tempered multiplicity-jet subplan

- [x] Run documented prior-research search and inspect all 20 candidate
  lemmas, all 20 source arguments, zero standalone proof ideas and the
  proposed ingredient set. Search is nonpartial with complete inventory
  of 63,283 files and no errors; candidates are source-only/not-checked
  and background index refresh is incomplete. Existing literal theta
  Schwartz/Fourier source and internal physical Xi jets are useful;
  no retrieved statement gives the required Dirac-jet classification.
- [x] Pin actual Schwartz/tempered derivative APIs and prove exact
  signed Dirac-jet pairing, including real/complex Xi derivative bridge.
- [x] Construct the actual real Xi multiplier from its literal Schwartz
  Fourier representative, and prove all Dirac jets strictly below the
  actual analytic multiplicity lie in its kernel.
- [x] Prove sharp first excluded jet using the actual nonzero Xi jet and
  a literal positive theta Schwartz test; audit finite-jet classification.
- [x] Transport these actual spectral jets to the unscaled source with
  explicit Fourier normalization; no silent replacement by scaled theta.
- [x] Run exact native/direct/export/axiom/API/catalogue/lint gates,
  persist exact partial coverage and retain full (8) as open until the
  actual analytic translation curve and full local/global converse pass.

Pinned Mathlib has `TemperedDistribution.derivCLM`, whose pairing is
negative Schwartz differentiation, and `SchwartzMap.derivCLM`.
Official documentation was searched and opened; actual local toolchain
names will be witnessed in scratch before use. The multiplicity used
here must be `(analyticOrderAt XiC (t:ℂ)).toNat`, with its finiteness
and vanishing/nonvanishing jets proved from actual entire Xi. No
assumed finite-jet vanishing interface may replace that actual order.

Actual tempered-jet scratch now passes with an empty log: literal real
Xi symbol has an actual Schwartz Fourier representative and temperate
growth; real and complex Xi derivatives agree on the real axis; actual
analytic order is finite with exact lower vanishing/terminal nonvanishing.
The signed pairing of iterated actual Dirac derivatives is proved. Every
jet below actual multiplicity is killed by the literal Xi multiplier,
and its first excluded jet is nonzero, witnessed by the actual positive
theta Schwartz source. Finite-jet independence/classification and final
project gates remain open. No full-clause certificate is claimed.

### Newly added recursive audit rows, 2026-09-30

All three newly discovered cards were read in full. Their paper claims
enter the exact audit queue; external partial plans are not certificates.

| Stage 2 path | Audit status |
|---|---|
| `11-rh-zero-divisor-geometry/weil-cone-common-ratio-unions-bohr-nonvanishing.md` | exact audit pending; both Bohr-restricted zeta nonvanishing and finite common-ratio union rigidity require unconditional certificates |
| `11-rh-zero-divisor-geometry/weil-cone-log-summable-deviation-rigidity.md` | exact audit pending; log-summable positive-definite rigidity and every stated Weil-cone corollary require unconditional certificates |
| `li-clock-infinite-partition-quarter-window.md` | exact audit pending; both explicit weighted complex bounds, vanishing error, all qualified real limits and uniform negative gap require complete certificates |

### Exact finite-Dirac-jet Xi kernel certificate

`ThetaTemperedMultiplicityJets.lean` supplies 38 public exports in 457
lines. The multiplier is the literal real Xi function, with its actual
Schwartz Fourier representative and proved temperate growth. Its order
is the finite actual analytic order `m(t)` of entire Xi at `(t:ℂ)`.
Actual tempered derivatives of Dirac have pairing
`δ_t^(r)(φ)=(-1)^r φ^(r)(t)`. Real and complex Xi derivatives agree.

At every real point, each jet of order below `m(t)` is killed; the first
excluded jet survives. Explicit polynomial-times-positive-theta Schwartz
probes prove independence of every finite jet prefix. A triangular
probe argument proves that a finite jet sum is killed exactly when all
coefficients of order at least `m(t)` vanish. Consequently
`ker(Xi·) ∩ span{δ_t^(r): r∈ℕ} = span{δ_t^(r): r<m(t)}`,
and this kernel has dimension exactly `m(t)`. This is the full exact
classification inside the algebraic finite-jet span, with no assumed
vanishing interface or multiplier-admission premise.

The named native build passes (5.2 seconds, 9,108 jobs). Final literal
`lake env lean GaloisForLFunctions/RHTower/ThetaTemperedMultiplicityJets.lean`
passes with an empty log. Every public export has an exact scratch
witness and a matching axiom report: all 38 reports contain exactly
`propext`, `Classical.choice`, `Quot.sound`. The fresh native `.ilean`
references supply 111 successful pinned API witnesses (103 Mathlib,
8 project dependencies), with an empty final log. All 38 expected
export/module catalogue pairs appear, with no extra pair; the umbrella
import appears once. Source whitespace passes. The final index refresh
passes (0 changed, 0 removed).

Authoritative global lint exits 1: 171 large-file warnings and eleven
unrelated unreachable modules; no active proof-debt finding and no
diagnostic in this owned leaf. The unreachable modules are
`CCMApertureChainProfile`, `CCMApertureTranslationChains`,
`CCMExponentialRampPrimeMoment`, `CCMExponentialRampSourceDissipation`,
`CCMExponentialRampTerminalEntropy`, `CCMRetainedChainKernelLower`,
`MoebiusMollifiedCriticalMoment`, `MoebiusMollifiedErrorThreeLines`,
`ThetaMovingShellFirstOrderPhase`, `WeilLogSummableRigidity`, and
`ZetaZeroDensityPowerSaving`. Global lint is not claimed green.

The fresh recursive census has 102 Stage 2 Markdown files: nine support
files and 93 theorem cards, zero unqueued paths. Historical Stage 3
matches are 29 unique paths: five owned whole-card certificates and
24 external promotions still requiring complete exact audits. There
are no ambiguous basename matches. No whole card is promoted here.

Full clause (8) remains open: explicit transport to the unscaled physical
source, its genuine Schwartz-valued holomorphic translation curve, every
point-supported distribution's finite-jet representation, and the full
local/global tempered converse are not consequences claimed by this
finite-span certificate. The history card stays Stage 2 and the recursive
objective continues.

All 23 explicitly owned finite-jet scratch files were removed after every
owned process exited; their namespace is absent. Certificate evidence was
persisted before deletion. Scoped `git diff --check` passes. Work continues
with the documented physical source-jet transport search.

### Exact unscaled physical source-jet transport work plan

- [x] Audit all 20 candidate statements, all 20 source arguments and
  available methods, zero proof ideas and the proposed ingredient set.
  Deep search is nonpartial, inventory 63,307/63,307 complete, errors
  empty; compiler candidates are source-only/not-checked, coverage
  snapshot older than current generation, semantic coverage unmeasured,
  background refresh incomplete. The actual unscaled source derivative
  integral and scaled Schwartz Fourier identity apply. The proposed
  arithmetic log-dilation ingredient does not apply to Schwartz dilation.
- [x] Pin Fourier, linear-equivalence, precomposition and actual source
  derivative APIs in this toolchain before writing the candidate proof.
- [x] Construct the actual invertible Schwartz map
  `F_phys φ(t)=F_mathlib φ(-t/(2π))` and its continuous tempered pullback.
- [x] Represent every ordinary unscaled theta derivative as an actual
  Schwartz function, and prove its physical transform is
  `(-it)^n XiC(t)` with every normalization explicit.
- [x] Transport every lower real Dirac jet to a nonzero independent
  source annihilator and prove the first excluded jet survives on the
  actual unscaled source. Retain full supported-distribution converse
  and Schwartz-valued analytic-curve construction as separate obligations.
- [x] Run exact native/direct/export/axiom/API/catalogue/index/lint
  gates; persist complete partial coverage and clean owned scratch.

Paper mechanism: pull back `δ_t^(r)` through the literal physical
Fourier map. Its value is `(-1)^r` times the `r`th real derivative of
the transformed Schwartz test. The actual unscaled source derivative
transforms to a polynomial times actual Xi. Leibniz then kills every
order below the actual Xi multiplicity. At the first excluded order,
the original unscaled source exposes the nonzero terminal Xi jet.
Invertibility transports finite-prefix independence. These positive
source statements do not supply the full annihilator identity (8).

### Actual Schwartz-valued complex translation curve work plan

- [x] Audit all 20 new candidate statements, all 20 source arguments and
  available methods, zero standalone proof ideas and the ingredient set.
  Search is nonpartial with complete 63,316-file inventory and no errors;
  compiler results remain source-only/not-checked, semantic coverage is
  unmeasured and background refresh incomplete. Existing Sobolev bounds
  are potentially reusable; the suggested radial-weight derivative chain
  does not prove the literal translated theta source's holomorphy.
- [x] Identify literal `thetaCuspStripSource`, its actual scalar analytic
  strip and two-sided closed-substrip exponential bound. Read actual
  fixed-radius Cauchy derivative estimate. This source-side bound avoids
  introducing a new gamma/Stirling dependency.
- [x] Pin Cauchy, scalar restriction, Schwartz seminorm and general TVS
  derivative APIs against this toolchain before new Lean implementation.
- [x] Prove uniform exponential decay of every actual complex source
  derivative on every closed substrip; construct every literal translated
  source as an actual Schwartz function, with its exact spatial jets.
- [x] Prove actual complex derivative in Schwartz topology through
  seminorm remainder bounds and `IsLittleOTVS`; identify its derivative
  with the actual spatial Schwartz derivative.
- [x] Compose every genuine tempered functional with that actual curve,
  prove scalar holomorphy and exact derivative/source-jet identification,
  then apply analytic uniqueness to the literal source annihilator.
- [x] Run exact leaf gates and retain the Fourier-correlation identity
  and full supported-distribution local/global converse as open until
  their separate exact proofs pass.

Paper mechanism: choose a fixed complex-disc radius within a closed
substrip. The actual bound `|k(z)|≤C exp(-|Re z|)` and Cauchy's estimate
give uniform exponential bounds for all complex spatial derivatives.
Their real restrictions give every actual Schwartz seminorm. On a
smaller disc, the second-derivative bound gives, for each seminorm,
`p(k_(a+h)-k_a-h k'_a)≤C_p |h|²`. This proves the genuine complex
derivative using the actual Schwartz seminorm topology and Mathlib's
general-TVS derivative definition. Scalar analytic uniqueness is applied
only after this literal construction, without an assumed holomorphy
interface for the source orbit.

### Exact unscaled physical source-jet certificate

`ThetaTemperedSourceJets.lean` supplies 29 public exports in 248 lines.
The actual continuous linear Schwartz equivalence is exactly
`F_phys φ(t)=F_mathlib φ(-t/(2π))`, with its actual continuous inverse.
Its actual continuous tempered pullback is injective. Every ordinary
derivative of the original unscaled theta source is constructed as an
actual Schwartz function, with literal pointwise representative
`((iteratedDeriv n thetaCuspFullSource x:ℝ):ℂ)` and exact physical
transform `(-it)^n XiC(t)`.

The pulled-back spectral Dirac jet has signed actual derivative pairing
on this physical Fourier transform. Its order-zero member equals the
previous literal real exponential evaluator. Every jet is nonzero;
every finite prefix is independent. Every order below the actual Xi
multiplicity annihilates every ordinary unscaled source derivative.
The first excluded jet survives on the original unscaled source itself.
The lower-jet span lies in the literal source derivative annihilator
and has dimension exactly the actual Xi multiplicity. No scaled source
is substituted for the original source.

Named native build passes (12 seconds, 13,580 jobs). Final literal
`lake env lean GaloisForLFunctions/RHTower/ThetaTemperedSourceJets.lean`
passes with an empty log. All 29 exact public export witnesses and
matching axiom reports pass, each with exactly `propext`,
`Classical.choice`, `Quot.sound`. The final 77 native-reference API
witnesses (58 Mathlib, 19 project dependencies) pass with an empty log.
All 29 exact generated-catalogue pairs appear, with no missing or
extra pair. Umbrella import appears once; source whitespace passes.
Final index refresh passes (1 changed, 0 removed).

Global lint exits 1: 172 large-file warnings and sixteen unrelated
unreachable modules, no other error and no owned diagnostic. Modules:
`CCMApertureChainProfile`, `CCMApertureTranslationChains`,
`CCMExponentialRampPrimeMoment`, `CCMExponentialRampSourceDissipation`,
`CCMExponentialRampTerminalEntropy`, `CCMRetainedChainKernelLower`,
`MoebiusMollifiedCriticalMoment`, `MoebiusMollifiedErrorThreeLines`,
`RectanglePoleWeightedLogDeriv`, `ThetaMovingShellFirstOrderPhase`,
`ZetaLogDerivSelbergExplicitFormula`, `ZetaNotchScaleMixture`,
`ZetaResidueUnitPoleWeightedRectangle`, `ZetaSelbergKernel`,
`ZetaSelbergRightEdge`, `ZetaZeroDensityPowerSaving`. Global lint
is not claimed green; unrelated work remains untouched.

Fresh exhaustive recursive census: 100 Stage 2 Markdown files,
nine support and 91 theorem cards, zero unqueued; 31 unique historical
Stage 3 matches comprise five owned whole-card certificates and
26 external promotions requiring complete exact audits. No ambiguity
and no owned whole-card promotion. Full clause (8) remains open:
actual Schwartz-valued analytic translation, Fourier-correlation
identity and full supported-distribution local/global converse are
separate outstanding proofs. The history card stays Stage 2.

Scoped `git diff --check` passes. All 23 explicit physical source-jet
scratch files were removed after every owned process exited, and their
namespace is absent. Certificate evidence was persisted before deletion.
The next Schwartz-curve API scratch is running in its separate namespace.

### Actual Schwartz translation construction checkpoint

`ThetaCuspSchwartzComplexTranslation.lean` constructs the literal
`x ↦ thetaCuspStripSource (↑x+a)` in the actual Schwartz space for
every `a` in the actual complex strip. Fixed-radius Cauchy estimates
prove uniform exponential decay of every complex source jet on every
closed substrip. The real spatial jets equal those actual complex jets.
The global curve's value at zero is the original `thetaCuspSchwartz`;
its restriction to real parameters is the literal unscaled translation.

The scratch literal compile passes with an empty log. Named native
build passes (8.8 seconds, 8,955 jobs). Initial 25 exact API witnesses
and three additional triangle/identity witnesses pass with empty logs.
Actual Schwartz-valued complex differentiation and scalar tempered
analytic continuation remain open; the next step proves quadratic
Taylor remainder bounds in every actual Schwartz seminorm. This is
a construction checkpoint, not a whole-card or clause (8) certificate.

The next owned leaf, `ThetaCuspStripTaylorRemainder.lean`, proves a
uniform quadratic remainder estimate for every actual complex theta
jet on every closed substrip. Two complex mean-value estimates on
nested discs preserve the exponential real-spatial decay. Its scratch
literal compile passes with an empty log. Named native build passes
(8,956 jobs; translate leaf 3.0 seconds, Taylor leaf 3.9 seconds).
Ten exact mean-value/filter API witnesses and fourteen further
scalar/Schwartz/TVS witnesses pass with empty logs. The translate leaf's
unused mean-value import was moved to the Taylor leaf. The actual
Schwartz seminorm derivative proof is the next outstanding step.

`ThetaCuspSchwartzTranslationCurve.lean` now proves the literal
quadratic remainder bound in every defining Schwartz seminorm,
normalized-remainder convergence in the actual Schwartz topology,
and the genuine complex `HasDerivAt` with derivative equal to the
actual spatial `SchwartzMap.derivCLM`. It also proves differentiation
after every genuine continuous complex-linear observer into any TVS,
and scalar analyticity for every actual tempered observer. Scratch
literal compile passes with an empty log. The eighteen further exact
basis API witnesses pass with an empty log. Release gates remain
pending; exact scalar higher jets and analytic uniqueness are next.

### Genuine Schwartz complex translation certificate

Three owned leaves contain 25 exact public exports:
`ThetaCuspSchwartzComplexTranslation.lean` (218 lines, 13 exports),
`ThetaCuspStripTaylorRemainder.lean` (156 lines, one export), and
`ThetaCuspSchwartzTranslationCurve.lean` (194 lines, 11 exports).
They construct the literal unscaled theta translate in actual Schwartz
space throughout the actual complex strip; identify every spatial jet;
prove closed-substrip Cauchy decay and quadratic Taylor bounds; prove
the quadratic remainder estimate in each defining Schwartz seminorm;
and obtain the genuine complex TVS derivative with the actual spatial
Schwartz derivative as its value. Every continuous complex-linear scalar
observer has an analytic orbit on the literal strip.

Named native gates pass: final translate/Taylor build has 8,956 jobs
(3.0/3.9 seconds), final Schwartz derivative build has 8,957 jobs
(8.3 seconds). All three final literal `lake env lean FILE` audits
ran sequentially and pass with empty logs. All 25 exact export witnesses
and matching axiom reports pass, each with exactly `propext`,
`Classical.choice`, `Quot.sound`. All 166 compiler-recorded API
witnesses (151 Mathlib, 15 project dependencies) pass with an empty log.
All 25 exact generated-catalogue pairs match, with no extra or missing
pair; all three umbrella imports occur once. Source whitespace and
scoped `git diff --check` pass. Final index refresh passes (one changed,
zero removed).

Global lint exits 1 with 172 large-file warnings and 17 unrelated
unreachable modules; no other diagnostic and no diagnostic in the
three new leaves. The complete error set was inspected:
`CCMApertureChainProfile`, `CCMApertureTranslationChains`,
`CCMExponentialRampPrimeMoment`, `CCMExponentialRampSourceDissipation`,
`CCMExponentialRampTerminalEntropy`, `CCMRetainedChainKernelLower`,
`ConvexLogModulusTransport`, `MoebiusMollifiedCriticalMoment`,
`MoebiusMollifiedErrorThreeLines`, `ThetaMovingShellFirstOrderPhase`,
`XiSliceLogDerivArcTail`, `ZetaLogDerivTypicalBox`,
`ZetaLogDerivTypicalBoxDensity`, `ZetaLogDerivTypicalScale`,
`ZetaLogDerivTypicalZeroSum`, `ZetaRightZeroWeightedCount`,
`ZetaZeroDensityPowerSaving`. Global lint is not claimed green.

Fresh exhaustive recursive census: 101 Stage 2 Markdown files,
nine support files and 92 theorem cards, zero unqueued. The two new
critical/supercritical partition cards were read completely, including
recovery of the first display's omitted ranges, and added pending every
exact paper target. Historical theorem matches: 26 unique Stage 3
matches, five owned whole-card certificates and 21 external promotions
pending complete audits. No ambiguity. A preliminary count included
six support rows; the census now excludes support filenames from both
current theorem counts and historical theorem matching.

This closes the genuine Schwartz complex derivative and scalar orbit
analyticity infrastructure. Exact scalar higher jets/ordinary-source
identification and analytic uniqueness remain open, followed by the
Fourier-correlation identity and complete supported-distribution
local/global converse. No owned whole-card promotion; full (8) and the
entire recursive Stage 2 objective remain open.

All 47 explicit owned Schwartz-curve scratch files were removed after
every owned process exited. The namespace is absent; certificate evidence
was persisted before deletion. Scoped `git diff --check` also passes
after the ledger/card certificate edits.

### Exact scalar source jets and analytic uniqueness work plan

- [x] Run the documented prior search for literal source jets and
  analytic uniqueness; audit all 20 candidate statements, all 20 source
  arguments and available methods, all ten prose hits and ten source
  passages. No standalone proof idea or ingredient set was returned.
  Deep search is partial: final filtering/judging returned malformed
  local-model JSON. Inventory is complete (63,371/63,371); retrieved
  compiler candidates remain source-only/not-checked, semantic coverage
  is unmeasured and background refresh incomplete. Actual real Schwartz
  translation is reusable; the L²-history result cannot act on every
  tempered functional. No corpus-wide absence claim is inferred.
- [x] Pin actual pointwise-tempered, real-to-complex derivative,
  iteration, analytic order and uniqueness APIs against this toolchain.
  All 24 exact basis witnesses pass; actual tempered data also compiles
  as a genuine scalar CLM and with the established scalar analytic orbit.
  Universe levels are explicitly pinned from this toolchain's output.
- [x] Prove the actual spatial jet CLM at zero is exactly
  `thetaUnscaledSchwartzDerivative n`, retaining the original real
  source and its complex postcomposition.
- [x] Prove every scalar observer's nth complex derivative throughout
  the strip equals its value on that actual nth spatial jet.
- [x] Prove the literal unscaled tempered derivative annihilator equals
  annihilation of every literal real/complex-strip translate, using
  scalar analytic uniqueness on the actual connected strip.
- [x] Complete every leaf gate, recursive census and explicit cleanup;
  retain Fourier-correlation and full local/global classification open.

Paper mechanism: real-to-complex postcomposition commutes with the
actual spatial Schwartz derivative. Induction identifies the exact
unscaled source representatives. For scalar higher derivatives, use
the established genuine continuous-linear observer derivative and
local equality of germs on the open strip; the nth spatial-jet CLM is
continuous and linear. If all original source derivatives are killed,
all scalar complex jets at zero vanish. A finite analytic order would
force a nonzero terminal derivative, so analytic order is infinite and
the scalar germ is zero. The identity principle propagates zero across
the actual preconnected strip, including every real translate. The
reverse direction uses exact higher derivatives of the real scalar
restriction: vanishing on every real translate makes that restriction
identically zero, and its derivatives at zero are the literal ordinary
source jets. Thus real vanishing supplies every original annihilator
condition without assuming an open complex germ from real vanishing.

The exact 169-line candidate compiles with an empty log, retaining every
original real source derivative and the actual Schwartz translation CLM.
`ThetaTemperedTranslationAnnihilator.lean` is installed and registered;
the release certificate below supersedes this construction checkpoint.
No whole-card or full-clause (8) certificate is inferred.

### Exact scalar source jets and translation-annihilator certificate

`ThetaTemperedTranslationAnnihilator.lean` contains 13 public theorems
in 169 lines. Complex postcomposition commutes with the actual spatial
Schwartz derivative; all spatial jets at zero are exactly the original
`thetaUnscaledSchwartzDerivative n`. Every scalar orbit derivative on
the strip, and every higher derivative of its real restriction, equals
the observer applied to the actual spatial jet. No scalar normalization
or substitute source is introduced.

For every actual tempered distribution, killing every ordinary unscaled
source derivative is equivalent to killing every literal strip translate,
every literal real translate, and every actual
`MellinL2.schwartzTranslate a thetaCuspSchwartz`. The forward proof uses
infinite analytic order and scalar uniqueness on the actual preconnected
strip. The reverse proof differentiates the identically zero real scalar
restriction. The genuine tempered functional's data supplies continuity;
no assumed holomorphy or extra functional interface is used.

Named native build passes (13,584 jobs, 30 seconds). Final literal
`lake env lean GaloisForLFunctions/RHTower/ThetaTemperedTranslationAnnihilator.lean`
passes with an empty log. All 13 export witnesses and all 43 native-reference
API witnesses (28 Mathlib, 15 project) pass with empty logs; all 56 exact
preflight checks pass. Every one of the 13 axiom reports contains exactly
`propext`, `Classical.choice`, `Quot.sound`. All 13 exact catalogue/module
pairs match, with no extra or missing pair, and the umbrella import occurs
once. Source whitespace and unchanged-source equality with the compiled
scratch candidate pass. Index refresh passes (three changed, zero removed).

Global lint exits 1 with 172 large-file warnings and 12 unrelated
unreachable modules, no other diagnostic and none in the new leaf.
The entire error set was inspected: `CCMApertureChainProfile`,
`CCMApertureTranslationChains`, `CCMExponentialRampPrimeMoment`,
`CCMExponentialRampSourceDissipation`, `CCMExponentialRampTerminalEntropy`,
`CCMRetainedChainKernelLower`, `JitteredUnitCellIntegrals`,
`JitteredUnitCellVariance`, `MoebiusMollifiedCriticalMoment`,
`MoebiusMollifiedErrorThreeLines`, `ThetaMovingShellFirstOrderPhase`,
`ZetaZeroDensityPowerSaving`. Global lint is not claimed green.

Fresh exhaustive recursive census: 102 Stage 2 Markdown files, nine
support files and 93 theorem cards, zero unqueued paths. Both newly added
cards were read completely (121-line random Weil granularity threshold,
451-line supercritical partition ratio) and queued for every exact target.
Historical theorem matches: 27 unique Stage 3 paths, comprising five
owned whole-card certificates and 22 external promotions pending complete
audits. No ambiguity. The supercritical-window card moved externally;
its complete certificate remains pending in this ledger.

Exact scalar source identification and analytic translation uniqueness
are closed. Fourier-correlation and full supported-distribution local/global
classification remain open. The history card stays Stage 2; no owned
whole-card promotion. All owned compiler/build/index/lint jobs have exited.
Explicit scratch cleanup and final scoped whitespace check are next;
this durable evidence precedes deletion.

Scoped `git diff --check` passes. All 25 explicitly owned scalar-germ
scratch files were removed by the finite guarded cleanup (exit 0), after
every owned compiler/build/index/lint job exited and evidence was saved.
Their namespace is absent. Source SHA256:
`9d6746a2369ebfbd2cf9dde3a3f93a394314f780412c78da0e9b2de45f85b8ee`.

### Actual tempered Fourier-correlation work plan

- [x] Run documented prior research for actual Schwartz/tempered
  Fourier-correlation; read all 20 candidate statements, all 20 source
  arguments and available methods, ten prose hits, ten source passages
  and the proposed ingredient set (zero proof ideas). Search is
  nonpartial, errors/unfinished empty, inventory complete (63,397 files).
  Index/coverage generation 1,159,668 is older than current 1,159,670;
  semantic coverage unmeasured, background refresh incomplete. Retrieved
  compiler records remain source-only/not-checked. Actual scalar inversion,
  Schwartz seminorm bounds, existing convolution and the literal Xi
  multiplier are useful. The proposed correlation-decay/regular-L²
  compatibility chain does not supply arbitrary-tempered interchange.
  No corpus-absence or novelty conclusion is inferred.
- [ ] Pin the actual physical Fourier translation phase, scalar
  inversion, literal Xi multiplier, tempered pullback inverse and
  continuity/seminorm/integration APIs against this toolchain.
- [ ] Prove the actual physical transform of a real unscaled translate
  is the negative phase `exp(-i*a*t)` times the literal actual Xi source.
- [ ] Prove genuine tempered interchange with scalar Fourier inversion,
  deriving finite-seminorm control from the actual continuous functional.
  If a Banach factor is required, construct its actual seminorm quotient
  and completion; never replace the original Schwartz topology by a norm
  or assume a functional/interchange interface.
- [ ] Prove both exact directions between all literal translation
  annihilation and the actual Xi tempered multiplier kernel, including
  any cutoff approximation needed for non-Schwartz plane waves.
- [ ] Construct and verify the actual continuous tempered pullback
  inverse; identify the entire original unscaled source annihilator
  with the physical pullback of that actual multiplier kernel.
- [ ] Complete every leaf gate, recursive census and explicit cleanup;
  retain full supported-distribution local/global classification open.

Planned paper mechanism: physical positive-phase Fourier inversion has
coefficient `1/(2*pi)` and negative inversion phase. For a Schwartz
spectral source `psi`, the desired scalar pairing identity is
`Q(psi*phi)=(1/(2*pi))*integral F_phys(phi)(a)*Q(exp(-i*a*t)*psi(t)) da`.
This is an obligation, not an assumed interchange. The actual source
Fourier identity and real translation phase then match the established
literal annihilator equivalence. Conversely, a zero Xi multiplier must
annihilate its Xi-weighted plane-wave probes through proved Schwartz
cutoff approximation; the bare plane wave itself is not a Schwartz test.
Only after both directions and the actual invertible pullback are proved
is the full source/multiplier identity certified. Global locally finite
real-zero jet representation is a separate remaining proof.

### Concrete finite-jet Banach observer component

- [x] Pin actual bounded-continuous-function, finite-product,
  seminorm-bound, quotient/range and complex Hahn–Banach APIs.
- [x] Construct the genuine continuous weighted-jet maps
  `phi ↦ (x ↦ x^k*iteratedDeriv n phi x)` into bounded continuous
  functions and prove their norms equal the defining Schwartz seminorms.
- [x] Construct their finite product as an actual Banach target and
  derive every actual tempered functional's norm bound from continuity.
- [x] Descend the actual functional through the weighted-jet map's
  algebraic kernel/range, prove boundedness there, and extend it to the
  Banach product by the actual complex Hahn–Banach theorem.
- [x] Certify the exact unconditional factorization for every tempered
  functional; run all leaf gates and preserve the still-open integral,
  cutoff, multiplier and global supported-distribution obligations.

Dependency-closed paper mechanism: for each `(k,n)`, the bounded function
is the actual polynomial multiplier after the actual spatial-jet CLM,
followed by the actual inclusion into bounded continuous functions.
Pointwise seminorm bounds and the defining supremum show its norm is
exactly `p_(k,n)(phi)`. For actual `T`, the continuous seminorm `‖T(phi)‖`
is bounded by `C*sup_(k,n in s) p_(k,n)(phi)` for a finite set `s`.
This supremum is controlled by the norm of the concrete finite product
`J_s(phi)`. Hence `ker J_s ⊆ ker T`; the algebraic first isomorphism
theorem descends `T` to `range J_s`. Its proved norm bound supplies a
genuine continuous linear map on this normed subspace. Complex
Hahn–Banach extends it to an actual scalar continuous linear observer
`L` on the complete bounded-function product, with
`L(J_s(phi))=T(phi)` for every original Schwartz test. No norm is
installed on the original Schwartz space. This classical infrastructure
component supplies actual observer data; it does not assume the desired
interchange or classify the Xi multiplier kernel.

### Concrete finite-jet Banach factorization certificate

`ThetaTemperedFiniteJetFactorization.lean` contains 11 public exports
(three data definitions and eight theorems) in 137 lines. The actual
weighted-jet CLM has literal value
`(x : Complex)^k * iteratedDeriv n phi x`; its bounded-function norm is
exactly `SchwartzMap.seminorm Complex k n phi`. The genuine finite
product is `s → (Real →ᵇ Complex)`, with its existing complete normed
space structure. Its norm controls the finite supremum of the original
defining Schwartz seminorms, including the empty-product case.

For every actual `T : S'(Real,Complex)`, continuity in the original
Schwartz topology derives a finite set and a positive nonnegative-real
bound. That bound proves `ker J_s ⊆ ker T`. The actual algebraic
quotient/range equivalence descends `T`; the proved bound makes the
descended map continuous on the concrete normed range. Actual complex
Hahn–Banach extends it to the finite Banach product. The unconditional
capstone `thetaTempered_exists_finiteJetFactorization` supplies actual
`s` and actual `L : thetaSchwartzFiniteJetBanach s →L[Complex] Complex`
such that `L(thetaSchwartzFiniteJetCLM s phi)=T phi` for every original
Schwartz test. No norm or replacement topology is installed on Schwartz
space; no assumed factorization or interchange interface is introduced.

The 41 dependency API witnesses, literal polynomial-growth witness and
concrete Banach instance pass. Named native build passes (8,958 jobs,
110 seconds), with only unrelated replayed informational suggestions.
Final literal `lake env lean GaloisForLFunctions/RHTower/ThetaTemperedFiniteJetFactorization.lean`
passes with an empty log. All 11 exact export witnesses and all 59
native-reference API witnesses (57 Mathlib, two project) pass with empty
logs. All 70 release preflight checks pass; the three printed aliases
`Complex → ℂ`, `Real → ℝ`, `MulZeroClass.mul_zero → mul_zero` are recorded
and their exact universe arities are pinned. Every axiom report contains
exactly `propext`, `Classical.choice`, `Quot.sound`. All 11 exact
catalogue/module pairs match; umbrella import occurs once. Source
equality with the compiled candidate and scoped whitespace checks pass.
Index refresh passes (two changed, zero removed).

Global lint exits 1 with 172 large-file warnings and 12 unrelated
unreachable modules: `CCMApertureChainProfile`,
`CCMApertureTranslationChains`, `CCMExponentialRampPrimeMoment`,
`CCMExponentialRampSourceDissipation`, `CCMExponentialRampTerminalEntropy`,
`CCMRetainedChainKernelLower`, `LogWindowPrimeNumberTheorem`,
`MoebiusMollifiedCriticalMoment`, `MoebiusMollifiedErrorThreeLines`,
`ThetaMovingShellFirstOrderPhase`, `ZetaLogDerivTypicalBoxScaledLength`,
`ZetaZeroDensityPowerSaving`. All errors were inspected. No other
diagnostic or new-leaf diagnostic; global lint is not claimed green.

Fresh exhaustive census: 101 Stage 2 Markdown files, nine support files,
92 theorem cards, zero unqueued paths. There are 28 unambiguous historical
theorem-card Stage 3 matches: five owned whole-card certificates and
23 external promotions pending complete audits. The random granularity
card's updated 131 lines were read completely. Its external endpoint
coverage at `kappa = 2^(−26)` and `kappa = 1` does not discharge the
original sharp threshold, all-height probability, actual producer and
sharp maximum-growth targets; its queue row retains every target.

The finite Banach observer component is closed. The actual Fourier
integral identity, negative physical phase, inverse tempered pullback,
cutoff approximation and full supported-distribution local/global
classification remain open. The history card stays Stage 2; no owned
whole-card promotion. All owned compiler/build/index/lint/metadata jobs
have exited. Durable source SHA256:
`7f25545f3e78aec93d530a922519edd458083b061e0612e8fe67eadd552374f4`.
Guarded static-manifest cleanup exited 0, removed exactly 23 owned
factorization scratch files and verified that namespace absent. The two
previously audited Fourier research files remain for the next proof
phase. Durable evidence preceded deletion; final scoped whitespace
check passes.

### Literal physical Fourier orbit and inverse bridge work plan

- [x] Pin exact actual translation, scalar inverse/Jacobian, original
  physical Fourier CLE, pointwise-dual precomposition and real-orbit
  continuity APIs against this toolchain.
- [x] Prove for every original Schwartz test the literal phase identity
  `F_phys(phi(.+a))(t)=exp(−i*a*t)*F_phys(phi)(t)`.
- [x] Construct actual inverse precomposition on tempered distributions
  and its two inverse laws, hence an actual continuous linear equivalence.
- [x] Construct the genuine Schwartz modulation CLM, prove its literal
  exponential value and actual real-parameter continuity.
- [x] Prove the exact physical inverse integral with `1/(2*pi)`
  normalization on every actual Schwartz test.
- [x] Run all named-leaf, literal, export, API, axiom, catalogue,
  index/lint, census and static-manifest cleanup gates. Keep full (8),
  arbitrary-functional correlation, cutoff and classification open.

Paper mechanism: translation changes variable `y=x+a` in the literal
positive-exponent Fourier integral. Its phase is `exp(−i*a*t)`.
Precomposition by the inverse of the original physical Fourier CLE
is the actual inverse tempered map. Conjugating actual Schwartz
translation by that original CLE gives a genuine modulation CLM;
the literal phase identity identifies it with exponential multiplication.
Existing strong continuity of actual Schwartz translation gives its
real-parameter continuity. Finally, the actual scalar Fourier inverse
of `psi(−2*pi*xi)` becomes
`(1/(2*pi))*integral(exp(−i*a*t)*psi(a),a)` by the genuine real linear
Jacobian formula. These are concrete inputs to the remaining Banach
integral proof, not assumptions of the desired interchange.

### Literal physical Fourier orbit and inverse bridge certificate

`ThetaTemperedFourierOrbit.lean` contains 16 public exports (three data
definitions and 13 theorems) in 170 lines. For every original Schwartz
test and every real translation, its original positive-exponent physical
Fourier transform has literal phase `exp(−i*a*t)`, using the already
defined `HTGeometry.modulation a t`. Actual precomposition by the original
Schwartz Fourier inverse gives a continuous inverse on the actual pointwise
tempered dual; both inverse laws, the actual tempered CLE and surjectivity
of the original pullback are proved. No regular-distribution restriction,
additional functional interface or substitute transform is introduced.

Conjugating actual Schwartz translation by the original physical CLE
constructs a genuine Schwartz modulation CLM. Its literal exponential
value, real-parameter continuity and equality with the actual temperate
multiplier CLM are proved. Every fixed real wave is proved to have
temperate growth from its actual derivative norms. The original physical
Schwartz inverse is exactly
`((2*pi)^(-1) : Complex) * integral(modulation a t * psi a,a)`;
the same formula reconstructs every original test from its own physical
transform. Genuine real change of variables supplies the normalization.

All 37 initial exact-universe API witnesses pass. Named native build
passes (13,590 jobs, 24 seconds); every replayed warning header was read,
all unrelated, no new-leaf diagnostic. Final literal
`lake env lean GaloisForLFunctions/RHTower/ThetaTemperedFourierOrbit.lean`
passes with an empty log. All 16 export witnesses and all 51 native-reference
API witnesses (41 Mathlib, ten project) pass with empty logs. All 67
release preflight checks pass; exact printed aliases `Complex → ℂ`,
`Real → ℝ`, `Inner.inner → inner`,
`MeasureTheory.MeasureSpace.volume → MeasureTheory.volume` are recorded
and universe arities pinned. Four opened-namespace aliases in the initial
37-check probe were also resolved explicitly. Every one of the 16 axiom
reports contains exactly `propext`, `Classical.choice`, `Quot.sound`.
All 16 exact catalogue/module pairs, unique umbrella import, unchanged
source equality and scoped whitespace checks pass. Index refresh passes
(one changed, zero removed).

Global lint exits 1 with 172 large-file warnings and 12 unrelated
unreachable modules: `CCMApertureChainProfile`,
`CCMApertureTranslationChains`, `CCMExponentialRampPrimeMoment`,
`CCMExponentialRampSourceDissipation`, `CCMExponentialRampTerminalEntropy`,
`CCMRetainedChainKernelLower`, `MoebiusMollifiedCriticalMoment`,
`MoebiusMollifiedErrorThreeLines`, `SelbergPrimeRangeCascade`,
`ThetaMovingShellFirstOrderPhase`, `ZetaLogDerivTypicalBoxPrimeCascade`,
`ZetaZeroDensityPowerSaving`. Every error was read; no other or owned-leaf
diagnostic. Global lint is not claimed green.

Fresh exhaustive census: 100 Stage 2 Markdown files, nine support files,
91 theorem cards, zero unqueued paths. There are 29 unambiguous historical
theorem-card matches: five owned whole-card certificates and 24 external
promotions pending complete exact audits. The critical-transition card
was externally moved to Stage 3; all updated 589 lines were read in three
complete bounded ranges. All original five target groups, all 17 paper
equations and all 64 externally claimed public declarations remain in
the full audit queue. External metadata is not an owned whole-card
certificate. No owned card was promoted.

Physical phase, actual inverse tempered pullback, Schwartz modulation
continuity and normalized scalar inversion are closed. Arbitrary-functional
Fourier correlation, cutoff approximation and full supported-distribution
local/global classification remain open; full (8) is not certified.
All owned compiler/build/index/lint/metadata jobs have exited. Source SHA256:
`4cd09f7ad7c11a3400273bee83e96e3d517309a0f1883efbf6adaed693234ee6`.
Guarded static-manifest cleanup exited 0, removed exactly 23 owned orbit
scratch files and verified that namespace absent. The two audited Fourier
research files remain. Durable evidence preceded deletion.

### Actual Banach Fourier-correlation proof work plan

- [x] Pin generic physical spatial-jet transform, complete Leibniz,
  Schwartz polynomial integrability, finite Banach norm, coordinate
  evaluation and genuine Banach integral APIs. The initial 35 jet, 30 bound
  and 12 integral API packets compile as exact universe-zero witnesses;
  the final leaf's complete 95 native API packet also passes.
- [x] Prove the exact physical transform of every spatial jet of every
  original Schwartz test, with multiplier `(−i*a)^n`. Scratch candidate
  `10003` exited zero with an entirely empty log; its exact scalar jet
  inverse and actual moment integrability also compiled. Release pending.
- [x] Prove exact modulated spatial jets and a finite-product polynomial
  norm bound, derived from the original seminorms. Scratch candidate
  `82274` exited zero with an entirely empty log; release pending.
- [x] Prove genuine Banach integrability of
  `a ↦ F_phys(phi)(a) • J_s(modulation_a(psi))`. The same scratch
  candidate proves an explicit finite polynomial norm majorant and its
  actual Schwartz-weighted integrability, including empty `s`. A direct
  real-source second-countability witness resolves typeclass search;
  no search-limit changes or Banach structure on Schwartz are used.
- [x] Prove the Banach integral's exact weighted-jet value by coordinate
  evaluation, full Leibniz and the actual scalar inverse formula. Complete
  scratch `69965` exited zero with an entirely empty log.
- [x] Apply the already-unconditional actual factorization of every
  tempered functional and the genuine Banach integral commutation theorem
  to obtain the full arbitrary-functional scalar correlation identity.
  The same scratch proves the full identity and actual scalar integrability.
- [x] Run all leaf gates with complete lint disposition; static cleanup is
  the final release step below. Retain cutoff approximation,
  both directions of the original Xi-kernel identity, and complete
  supported-distribution local/global classification as separate obligations.

Dependency-closed paper mechanism: for fixed Schwartz `psi`, the exact
Leibniz expansion of a modulated `n`th jet is a finite sum with wave
coefficients `(−i*a)^j`, `j≤n`, times original `psi` jets. Weighted
pointwise bounds give seminorm bounds. For finite `s`, put `K` equal to
the largest derivative order in `s`; sum the nonnegative finite Leibniz
seminorm constants to obtain `C_s`. Then
`norm(J_s(modulation_a(psi))) ≤ C_s*(1+a^2)^K`, since
`|a|^j ≤ (1+a^2)^K` for `j≤K`. The empty-product case gives zero.
The implementation now targets the sharper explicit finite-sum majorant
`sum_(k,n)∈s sum_j≤n choose(n,j)*|a|^j*p_(k,n−j)(psi)` directly.
After multiplication by `norm(F_phys(phi)(a))`, every summand is integrable
by the installed actual Schwartz polynomial-norm integrability theorem;
finite summation proves the full majorant integrable. This removes the
auxiliary smooth polynomial and maximum-degree estimate without adding an
assumption. Actual modulation continuity gives strong measurability.
Coordinate evaluation commutes with this genuine Banach
integral. The scalar inverse formula applied to every actual spatial
jet of `phi` identifies its moments; full Leibniz identifies their finite
sum with `J_s(psi*phi)`. Thus the exact Banach integral is
`2*pi • J_s(psi*phi)`. For actual arbitrary `Q`, the already-derived
factorization `Q=L∘J_s` allows genuine Banach integral commutation and
gives `Q(psi*phi)=(1/(2*pi))*integral(F_phys(phi)(a)*Q(modulation_a(psi)),a)`.
No Bochner integral on the original non-normed Schwartz space and no
assumed functional interchange is used. Bare waves are not Schwartz;
the remaining kernel-to-wave direction still needs an actual proved
cutoff approximation.

### Fourier-correlation release work plan

- [x] Install the exact complete correlation leaf and register every public
  export, with unique actual `RHTower.lean` umbrella import.
- [x] Named native build `91622`: exit zero, 13,595 jobs, owned leaf 80 seconds.
  All 128 replayed warning headers from 53 external modules read; no owned
  diagnostic and no build error. Final literal leaf `14346`: exit zero,
  completely empty log.
- [x] Check all 14 complete export headers and all 95 native referenced APIs.
  All 109 headers `28309` exit zero, no error or warning.
- [x] Compile explicit universe-zero witnesses for all 14 exports and 95 APIs.
  Exports `9858` and APIs `87962` exit zero with entirely empty logs.
- [x] Print and inspect every export's axioms; verify exact source/catalogue
  pairs, unchanged hash, candidate equality and unique umbrella registration.
  All 14 reports `94019` exit zero and use exactly the three standard axioms.
- [x] Refresh index and run authoritative global lint; classify every finding.
  Index `51614` exits zero, 0 changed and 0 removed (background refresh
  had already indexed the leaf). Post-index exact catalogue checks pass.
  Lint `37590` exits one: all 183 lines read; 172 existing size warnings
  plus the 11 unrelated unreachable modules listed below, no other finding.
- [x] Persist the complete release certificate and recursive census, then
  perform only the audited static scratch cleanup and confirm absence.
  All 42 audited regular scratch files removed; complete owned namespace
  absence verified after all handles were terminal and evidence persisted.

The current recursive census is 99 Stage-2 Markdown files: 9 support files
and 90 theorem cards, with zero unqueued theorem cards. There are 30 unique,
unambiguous historical theorem-card matches in Stage 3: five owned exact whole
certificates and 25 external promotions pending this ledger's whole audit.
The newly moved supercritical ratio card has been read completely through all
569 updated lines; its claimed 37 declarations and all 23 source-pure paper
equations remain in the queue. Historical metadata is not an owned certificate.

### Unconditional physical Fourier-correlation certificate

Actual leaf: `formal/GaloisForLFunctions/RHTower/ThetaTemperedFourierCorrelation.lean`; 337 lines, 14 public exports (one definition,
13 theorems). Frozen SHA256 `f94ad6ad208a6663bd5b9cca57d12c1d36d353fba0637e7fa143d150dc353660`. The full actual arbitrary
tempered-functional identity and scalar integrability are unconditional;
every integral interchange occurs in the existing complete finite Banach
observer. Original Schwartz tests retain their installed seminorm topology.

Complete scratch 69965: exit zero, empty log. Named native 91622: exit zero,
13,595 jobs, owned leaf 80 seconds; all 128 replayed warning
headers from 53 external modules read, no owned diagnostic.
Final literal project 14346, all 14 export witnesses 9858, and all 95 native
API witnesses 87962: each exits zero with entirely empty logs. All 109 complete
headers 28309: exit zero, no error or warning. Every one of the 14 axiom
reports 94019 uses exactly `propext`, `Classical.choice`, `Quot.sound`.
All 14 exact public name/module catalogue pairs, candidate/source equality,
unchanged SHA256, unique actual `RHTower.lean` registration and whitespace
checks pass, including post-index verification. Observed printer aliases are
`Complex→ℂ`, `ENat→ℕ∞`, `Inner.inner→inner`,
`MeasureTheory.MeasureSpace.volume→MeasureTheory.volume`, `Real→ℝ`;
every witness uses the exact requested native constant and explicit zero universes.

Index 51614 exits zero: 0 changed, 0 removed; managed background refresh had
already indexed this source. Authoritative lint 37590 exits one; all 183
lines read. Exactly 172 existing size warnings plus these 11 unrelated
unreachable modules, no other or owned leaf finding:

- `GaloisForLFunctions.RHTower.CCMApertureChainProfile`
- `GaloisForLFunctions.RHTower.CCMApertureTranslationChains`
- `GaloisForLFunctions.RHTower.CCMExponentialRampPrimeMoment`
- `GaloisForLFunctions.RHTower.CCMExponentialRampSourceDissipation`
- `GaloisForLFunctions.RHTower.CCMExponentialRampTerminalEntropy`
- `GaloisForLFunctions.RHTower.CCMRetainedChainKernelLower`
- `GaloisForLFunctions.RHTower.MoebiusMollifiedCriticalMoment`
- `GaloisForLFunctions.RHTower.MoebiusMollifiedErrorThreeLines`
- `GaloisForLFunctions.RHTower.ThetaMovingShellFirstOrderPhase`
- `GaloisForLFunctions.RHTower.ZetaNotchTruncatedDiagonal`
- `GaloisForLFunctions.RHTower.ZetaZeroDensityPowerSaving`

Global lint is not green. The whole theta card remains Stage 2: actual cutoff
approximation, both directions of its original Xi-kernel identity and complete
local/global supported-distribution classification remain open. No partial
support theorem or externally asserted promotion is a whole-card certificate.

Complete public export inventory:

- `RHTower.thetaPhysicalFourierCLE_derivCLM_apply` (theorem, source line 29)
- `RHTower.thetaPhysicalFourierCLE_spatialJet_apply` (theorem, source line 51)
- `RHTower.thetaPhysicalFourierCLE_spatialJet_inverse_integral` (theorem, source line 62)
- `RHTower.thetaPhysicalFourierCLE_spatialJet_moment_integrable` (theorem, source line 77)
- `RHTower.thetaPhysicalModulationCLM_iteratedDeriv_apply` (theorem, source line 92)
- `RHTower.thetaPhysicalModulationCLM_seminorm_le` (theorem, source line 115)
- `RHTower.thetaModulationFiniteJetMajorant` (def, source line 147)
- `RHTower.thetaPhysicalModulationCLM_finiteJet_norm_le` (theorem, source line 154)
- `RHTower.thetaModulationFiniteJetMajorant_fourier_integrable` (theorem, source line 170)
- `RHTower.thetaPhysicalFourierCLE_modulation_finiteJet_integrable` (theorem, source line 196)
- `RHTower.thetaPhysicalFourierCLE_modulation_jet_inverse` (theorem, source line 215)
- `RHTower.thetaPhysicalFourierCLE_modulation_finiteJet_inverse` (theorem, source line 260)
- `RHTower.thetaTempered_physicalFourier_correlation` (theorem, source line 312)
- `RHTower.thetaTempered_physicalFourier_correlation_integrable` (theorem, source line 328)

Complete native API inventory: 76 Mathlib and 19 project references. Every
one has an explicit universe-zero witness compiled in the all-95 API gate.

`GaloisForLFunctions.HTGeometry.FlowTemperedGrowth`:

- `GaloisForLFunctions.HTGeometry.cexpLin`
- `GaloisForLFunctions.HTGeometry.contDiff_cexpLin`
- `GaloisForLFunctions.HTGeometry.iteratedDeriv_cexpLin`
- `GaloisForLFunctions.HTGeometry.modulation`
- `GaloisForLFunctions.HTGeometry.norm_modulation`
- `GaloisForLFunctions.HTGeometry.norm_neg_I_mul`

`GaloisForLFunctions.RHTower.ThetaCuspSchwartzTranslationCurve`:

- `RHTower.thetaSchwartzSpatialJetCLM`
- `RHTower.thetaSchwartzSpatialJetCLM_apply`

`GaloisForLFunctions.RHTower.ThetaTemperedFiniteJetFactorization`:

- `RHTower.thetaSchwartzFiniteJetBanach`
- `RHTower.thetaSchwartzFiniteJetCLM`
- `RHTower.thetaSchwartzFiniteJetCLM_apply_apply`
- `RHTower.thetaSchwartzFiniteJetCLM_component_norm`
- `RHTower.thetaTempered_exists_finiteJetFactorization`

`GaloisForLFunctions.RHTower.ThetaTemperedFourierOrbit`:

- `RHTower.thetaPhysicalFourierCLE_inversion`
- `RHTower.thetaPhysicalModulationCLM`
- `RHTower.thetaPhysicalModulationCLM_apply`
- `RHTower.thetaPhysicalModulationCLM_continuous`

`GaloisForLFunctions.RHTower.ThetaTemperedSourceJets`:

- `RHTower.thetaPhysicalFourierCLE`
- `RHTower.thetaPhysicalFourierCLE_apply`

`Mathlib.Algebra.BigOperators.Group.Finset.Basic`:

- `Finset.sum_congr`

`Mathlib.Algebra.BigOperators.Ring.Finset`:

- `Finset.mul_sum`

`Mathlib.Algebra.Group.Action.Defs`:

- `smul_eq_mul`

`Mathlib.Algebra.Group.Defs`:

- `mul_assoc`
- `mul_comm`
- `pow_succ`

`Mathlib.Algebra.Order.BigOperators.Group.Finset`:

- `Finset.single_le_sum`
- `Finset.sum_le_sum`

`Mathlib.Algebra.Order.GroupWithZero.Defs`:

- `mul_le_mul_of_nonneg_left`

`Mathlib.Analysis.Calculus.ContDiff.Defs`:

- `ContDiff.contDiffAt`
- `ContDiffAt`
- `ContDiffAt.of_le`

`Mathlib.Analysis.Calculus.Deriv.Basic`:

- `fderiv_apply_one_eq_deriv`

`Mathlib.Analysis.Calculus.IteratedDeriv.Defs`:

- `iteratedDeriv`

`Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas`:

- `iteratedDeriv_mul`

`Mathlib.Analysis.Complex.Norm`:

- `Complex.norm_natCast`

`Mathlib.Analysis.Distribution.DerivNotation`:

- `LineDeriv.lineDerivOp`

`Mathlib.Analysis.Distribution.SchwartzSpace.Basic`:

- `SchwartzMap.contDiffAt`
- `SchwartzMap.continuous`
- `SchwartzMap.hasTemperateGrowth`
- `SchwartzMap.integrable`
- `SchwartzMap.integrable_pow_mul`
- `SchwartzMap.le_seminorm'`
- `SchwartzMap.seminorm`
- `SchwartzMap.seminorm_le_bound'`
- `SchwartzMap.smulLeftCLM`
- `SchwartzMap.smulLeftCLM_apply_apply`

`Mathlib.Analysis.Distribution.SchwartzSpace.Deriv`:

- `SchwartzMap.derivCLM`
- `SchwartzMap.lineDerivOp_apply_eq_fderiv`

`Mathlib.Analysis.Distribution.SchwartzSpace.Fourier`:

- `SchwartzMap.fourier_lineDerivOp_eq`

`Mathlib.Analysis.Distribution.TemperateGrowth`:

- `Function.hasTemperateGrowth_inner_left`

`Mathlib.Analysis.InnerProductSpace.Basic`:

- `RCLike.inner_apply`

`Mathlib.Analysis.InnerProductSpace.Defs`:

- `Inner.inner`

`Mathlib.Analysis.Normed.Group.Basic`:

- `norm_nonneg`
- `norm_sum_le`

`Mathlib.Analysis.Normed.Group.Constructions`:

- `pi_norm_le_iff_of_nonneg`

`Mathlib.Analysis.Normed.Group.Real`:

- `Real.norm_eq_abs`

`Mathlib.Analysis.Normed.MulAction`:

- `norm_smul`

`Mathlib.Analysis.Normed.Ring.Basic`:

- `norm_mul`
- `norm_pow`

`Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`:

- `Real.pi`
- `Real.pi_ne_zero`

`Mathlib.Data.Complex.Basic`:

- `Complex`
- `Complex.I`
- `Complex.real_smul`

`Mathlib.Data.ENat.Defs`:

- `ENat`

`Mathlib.Data.Finset.Defs`:

- `Finset`

`Mathlib.Data.Finset.Range`:

- `Finset.range`

`Mathlib.Data.Fintype.Defs`:

- `Finset.mem_univ`
- `Finset.univ`

`Mathlib.Data.Nat.Choose.Basic`:

- `Nat.choose`

`Mathlib.Data.Real.Basic`:

- `Real`

`Mathlib.MeasureTheory.Constructions.BorelSpace.Basic`:

- `SecondCountableTopologyEither`

`Mathlib.MeasureTheory.Function.L1Space.Integrable`:

- `ContinuousLinearMap.integrable_comp`
- `MeasureTheory.Integrable`
- `MeasureTheory.Integrable.const_mul`
- `MeasureTheory.Integrable.mono'`
- `MeasureTheory.Integrable.mul_const`
- `MeasureTheory.integrable_finsetSum`

`Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable`:

- `Continuous.aestronglyMeasurable`

`Mathlib.MeasureTheory.Integral.Bochner.Basic`:

- `MeasureTheory.integral_congr_ae`
- `MeasureTheory.integral_const_mul`
- `MeasureTheory.integral_finsetSum`

`Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap`:

- `ContinuousLinearMap.integral_comp_comm`

`Mathlib.MeasureTheory.Measure.MeasureSpaceDef`:

- `MeasureTheory.MeasureSpace.volume`

`Mathlib.Order.Basic`:

- `LE.le.trans`

`Mathlib.Order.BoundedOrder.Basic`:

- `le_top`

`Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic`:

- `ContinuousLinearMap.comp`
- `ContinuousLinearMap.continuous`
- `ContinuousLinearMap.map_smul`

`Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd`:

- `ContinuousLinearMap.proj`

`Mathlib.Topology.Algebra.MulAction`:

- `Continuous.smul`

`Mathlib.Topology.Continuous`:

- `Continuous.comp`

`Mathlib.Topology.ContinuousMap.Bounded.Basic`:

- `BoundedContinuousFunction.evalCLM`
- `BoundedContinuousFunction.ext`

`Mathlib.Topology.Defs.Basic`:

- `Continuous`

Recursive census: 99 Stage-2 Markdown files = 9 support + 90 theorem cards; zero unqueued theorem cards. Historical 30 unique unambiguous theorem-card
Stage-3 matches = five owned whole-card certificates + 25 external pending.

42-file static cleanup manifest (prefix `/tmp/hgt_stage2_theta_fourier_correlation_`;
each literal suffix below specifies exactly one file, with no wildcard deletion):

- `research.json`
- `research_audit.py`
- `jets_preflight.lean`
- `jets_preflight.log`
- `jets_gate.py`
- `jets_basis.lean`
- `jets_basis.log`
- `jets_candidate.lean`
- `jets_candidate.log`
- `jets_cast.lean`
- `jets_cast.log`
- `bounds_preflight.lean`
- `bounds_preflight.log`
- `bounds_gate.py`
- `bounds_basis.lean`
- `bounds_basis.log`
- `bounds_candidate.lean`
- `bounds_candidate.log`
- `integral_preflight.lean`
- `integral_preflight.log`
- `integral_gate.py`
- `integral_basis.lean`
- `integral_basis.log`
- `integral_candidate.lean`
- `integral_candidate.log`
- `integral_extension.lean`
- `release_audit.py`
- `release_native.log`
- `release_native_diagnostics.json`
- `release_literal.log`
- `release_metadata.json`
- `release_checks.lean`
- `release_checks.log`
- `release_exports.lean`
- `release_exports.log`
- `release_api.lean`
- `release_api.log`
- `release_axioms.lean`
- `release_axioms.log`
- `release_census.json`
- `release_index.log`
- `release_lint.log`

All owned compiler, build, index and lint handles are terminal. Full evidence
is persisted here and in the theta card and Serena before cleanup. The audited
manifest equals the whole owned namespace; all 42 entries are regular, non-symlink
files. Actual deletion result and absence verification will be recorded next.

Static cleanup completed: guarded runner exits zero; exactly the 42 literal
manifest entries removed. Complete owned namespace absence verified. Scoped
whitespace validation remains the final bookkeeping check before the next
original-theorem obligation.

### Actual expanding Schwartz cutoff and full Xi-kernel work plan

- [ ] Run the documented prior-research search and inspect every returned
  record, coverage and freshness before new cutoff code.
- [ ] Pin the installed scaled cutoff's actual values, complete derivative
  formula, compact support and uniform derivative bounds; pin the original
  Schwartz seminorm convergence criterion and every needed API.
- [ ] Prove every original weighted seminorm of
  `psi-cutoffSchwartz R psi` is bounded by an explicit constant divided by
  `R≥1`, without a seminorm assumption or replacement topology.
- [ ] Prove actual compact Schwartz cutoffs converge to every original test
  in its installed topology and supply genuine compactly supported wave tests.
- [ ] Combine actual compact wave approximation with the completed arbitrary
  functional correlation theorem to prove the full modulation-orbit/multiplier
  kernel equivalence for every actual tempered functional.
- [ ] Specialize the whole physical Fourier equivalence to the original
  theta derivative annihilator and actual Xi multiplier, preserving both
  directions and every original source test.
- [ ] Run complete leaf gates and audited static cleanup; keep the complete
  actual local/global supported-distribution classification as the next
  separate obligation of original (8).

Paper mechanism to audit: the installed `cutoffScaled R` is one on
`|x|≤R`, supported in `|x|≤2R`, and has `j`th derivative bounded by
`B_j/R^j`, with `B_j` a proved bound on the fixed smooth compact profile.
Full Leibniz expands the actual difference. Its `j=0` term vanishes on
`|x|<R`; outside, the extra original spatial weight gives
`|x|^k*norm(psi^(n)(x))≤p_(k+1,n)(psi)/R`. For each `j≥1`, `R≥1`
gives `R^(-j)≤R^(-1)` and the original `p_(k,n−j)(psi)` controls
the remaining weighted derivative. The finite binomial sum is therefore
`C_(k,n,psi)/R`. Every original seminorm tends to zero for `R=N+1`,
so the actual installed Schwartz topology gives convergence. A compact
wave test times actual `psi` is exactly the cutoff of its actual modulation.
The multiplier-kernel premise annihilates every such product; continuity
and actual Schwartz convergence give all real modulation probes. Conversely,
the now-proved full correlation formula gives the entire actual product
kernel from those probes. Actual physical Fourier transport and the already
proved original theta derivative/translation annihilator equivalence give
the full Xi-kernel identity. No bare wave is inserted into Schwartz, and no
assumed approximation, inverse-integral interchange or artificial norm is used.
