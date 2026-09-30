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
| `theta/theta-compact-inverse-zero-jordan-history.md` | actual Jordan chains, centered obstruction, proper quasinilpotent history, full nonzero quotient root spaces, literal Riesz/Fourier descent, sharp translation admission, original closed-history equality and graded finite arithmetic/Euler quotient vanishing certified; bounded scale transport and full properness/endpoint/dual/decay audit pending |
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
| `li-clock-contiguous-comparison-window.md` | newly added; complete exact certificate audit pending |
| `li-clock-finite-partition-volterra-positive-area.md` | moved externally to Stage 3; complete exact certificate audit pending |
| `li-clock-joint-arithmetic-cancellation-window.md` | newly added; complete exact certificate audit pending |

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
- [ ] Identify the actual `q=0` measure, derivative representatives and
  holomorphic translation orbit, then prove dense endpoint history.
- [ ] Run the complete exact certificate gates, preserve the recursive
  queue, update card/memory and clean owned scratch.

The complementary-weight construction now passes a native named leaf build
and a direct source check in `ThetaWeightedHistoryProperness.lean`. Its
literal density-unitary cancellation identifies the bounded functional with
`∫f exp(itx)`, the source test with mass `M>0`, and the actual derivative
transform with `(-it)^n XiC(t)`. Hardy's real zero proves properness throughout
`0<q<2`. Exhaustive final export/axiom/index/lint gates remain pending for
this work block; no whole card is promoted.

Endpoint source audit found that the existing rectangle-majorant proof
never uses its strict-positive exponent argument. Its new nonnegative
form includes `q=0`, while the original public signature is preserved by
a wrapper. The exact endpoint paper construction is: use the same literal
Gaussian majorants on compact rectangles throughout `|Im z|<π/4`; apply
the existing dominated Hilbert-holomorphy and jet theorem; identify all
origin jets with actual ordinary derivatives; use analytic uniqueness to
include every real translate in their closed span. The actual normalized
translation orbit is then `sqrt(2π)` times the `2π` dilation of those
literal translates, so the existing unconditional normalized cyclicity
certificate proves endpoint density. This passage still requires its own
Lean certificate. The broader recursive formalization goal remains active
and unbounded.
