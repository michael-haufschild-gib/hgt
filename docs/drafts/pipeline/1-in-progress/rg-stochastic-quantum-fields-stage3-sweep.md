# RG, stochastic, and quantum fields Stage-3 sweep

- **ID:** `rg-stochastic-quantum-fields-stage3-sweep`
- **Stage:** 1-in-progress
- **Type:** FORMALIZATION SWEEP
- **Source:** `../2-fully-proven/not_new_scientific_knowledge/04-rg-stochastic-quantum-fields`
- **Statement:** Formalize every dependency-closed theorem proved on all 23 source cards as exact,
  unconditional Lean theorems, wire each leaf module, audit axioms and lint, then move each completed
  card to Stage 3.

## Goal

No source-card theorem may be replaced by a finite shadow, conditional interface, encoded lookup
table, weakened conclusion, or theorem with new premises. Existing partial formalizations count only
for exact claims they prove.

## Global constraints

- Search local corpus with `scripts/formal_tools.py research` before new Lean.
- Verify every new Mathlib name in `/tmp` with `lake env lean /tmp/x.lean`.
- Check each leaf with `lake env lean <file>`; use `lake build <module>` only for final leaf audit.
- Never run a full build or umbrella build. One foreground Lean process only.
- Run formal lint and `#print axioms` before promotion; no `sorry`, `admit`, `axiom`, `opaque`, or
  `unsafe` declarations.
- Wire completed leaves into `HTGeometry.lean` or `RHTower.lean` without building umbrellas.

## Requirement ledger

| # | Source card | Current exact Lean evidence | Remaining promotion obligation |
|---:|---|---|---|
| 1 | `balanced-causal-fracture-torsor-classification` | `ColorGram*`, `PrimitivePairInteriorDimension`, `BalancedActualityCapacity` prove the `3x2` orbit, primitive-pair dimension test, and finite balance arithmetic | General AIII Gram-fibre torsor equivalence, smooth product equivalence, arbitrary-boundary strict-convexity iff rank two, genuine Cartan-family corollary |
| 2 | `bbm-pullback-completion-purely-continuous-law` | `BBMMetricObstruction` proves the Mellin state is never in the pullback metric | Pullback completion unitary, self-adjoint restriction reducing, dilation spectral type, BBM no-point-spectrum conclusion, compact/trace-class consequences |
| 3 | `coherence-graph-volume-recurrence-exponent-law` | `FiniteQuantumObserverCoherenceLaw` and `FiniteQuantumObserverGraphRecurrenceBound` prove graph rank and universal upper recurrence | Exact Haar-volume bounds, minimax lower exponent, almost-every fixed-spectrum exponent, rank-zero boundary |
| 4 | `common-profile-boolean-anchor-curvature` | Existing Boolean/signed-tensor laws plus new `SquarefreeShearKernelSpectrum`, `SquarefreeShearKernelFourier`, `SquarefreeShearKernelHilbert`, and `SquarefreeShearKernelArithmetic`: exact rank/inertia/eigenvalues/norms, actual root-density `(SG5)`, literal coprime-packet `(SG6)`, sharp `(SG7)`--`(SG8a)`, and canonical `ZMod`/spectral reindexing; `(SG10)` is existing `quadraticCongruenceNormalizedRootSum_mul_alias` | Build/axiom/lint/wiring audit after exact physical `(SG9)`; no corpus implementation of its `W_h/δ_h` BV layer found |
| 5 | `de-sitter-ultrametric-detailed-balance-hypertranscendence` | `FiniteKMSDetailedBalance`, `UltrametricThermalMahler`, `UltrametricThermalTruncation` prove finite KMS algebra, formal Mahler constraint, finite residual | Infinite detector trace, DA inverse time-change and HT transfer, exact Hubble equation/nonselection, source spectrum and physical analytic dependencies |
| 6 | `erosion-threshold` | Stage-3 `critical-line-abscissa-of-convergence` exists; related cocycle and finite-free infrastructure require audit | Exact backbone, sharp `L2` coboundary iff threshold, imported statistical theorem surface, zero/singularity identity, terminal conjunction |
| 7 | `exact-rational-rg-generation-dichotomy` | Differential-algebra infrastructure exists but no exact analytic Poincare/Ritt theorem | Analytic Poincare construction, local inversion, Ritt equivalence, cocycle equivalence, DA-scheme theorem |
| 8 | `exact-rg-clock-hypertranscendence-equivalence` | Differential-algebra infrastructure exists but no analytic germ/logarithm package for statement | Poincare/inverse/beta/clock equivalence, multiplicative clocks, DA-scheme invariance |
| 9 | `gadc-tree-population-rg-clock-hypertranscendence` | `GADCTreePopulationRG` proves exact channel/population rational algebra; parent RG modules require exact audit | Interior CPTP channel and interval dynamics, all three HT regimes, endpoint classification, exact clock/scheme conclusion |
| 10 | `infinite-half-turn-frequency-source-admissibility-split` | Finite repaired-packet obstructions and a Stage-3 local-infinity card exist; exact declaration audit pending | Curvature gate, sigma-finite universality, finite-mass passport, compact-target impossibility, forced local infinity and all stated corollaries |
| 11 | `noisy-binary-tree-channel-rg-clock-hypertranscendence` | `BetheHolographicIsingRG` proves BSC/BP rational algebra; parent RG modules require exact audit | All-noise HT theorem, noiseless DA endpoint, collapsed endpoint, threshold separation, DA-scheme invariance |
| 12 | `q-geometric-generalized-free-field-hypertranscendence` | Stage-3 `geometric-kallen-lehmann-self-similar-spectrum` proves finite algebraic/positivity shadows | Infinite positive measure, generalized free Wightman field, exact response, difference-Galois HT, propagator HT |
| 13 | `reciprocal-q-ladder-kallen-lehmann-field` | Related geometric Kallen--Lehmann and Mahler infrastructure exists | Infinite-soliton source, reciprocal pushforward/local finiteness/growth, Wightman reconstruction, response HT, de Sitter clock |
| 14 | `reservoir-density-complete-monotonicity-markov-equivalence` | No exact card module found | Bernstein theorem infrastructure, finite Laplace/support equivalence, complete-monotonicity shift criterion, pushforward inverses |
| 15 | `rg-tower-differential-incoherence-obstruction` | Differential-algebra infrastructure exists; no Boshernitzan--Rubel analytic-family theorem found | Analytic germ category, DA inversion and beta equivalence, common autonomous ADE closure, scheme invariance |
| 16 | `schwarzian-projective-erosion-tower` | Differential-independence/order infrastructure and `SchwarzianHypertranscendence` exist | Differential rational Schwarzian, exact order addition, independence, strict tower, depth law, trivial intersection, translation covariance |
| 17 | `thermodynamic-divisor-charge-finite-ancestor-or-boundary-index` | `PrimeQuasiLocalCharge.nonzero_winding_has_finiteAncestor` | Operator K-theory, six-term exact sequence, nonzero boundary iff nonliftability, AF continuity statement |
| 18 | `ultrametric-one-loop-resolvent-hypertranscendence` | `UltrametricResolventSusceptibility` proves exact formal coefficients, constraint, uniqueness | Analytic meromorphic resolvent, pole/nonrational proof, difference-Galois HT, determinant and de Sitter Hessian interpretation |
| 19 | `ultrametric-thermal-mahler-hypertranscendence` | `UltrametricThermalMahler` proves coefficient spectrum, constraint, uniqueness; truncation formalized | Analytic heat trace, nonrational gap theorem, Mahler difference-Galois HT, spectral-zeta DA split, QFT realization |
| 20 | `universal-typed-event-network-fixed-carrier-no-go` | `EventNetworkFixedCarrier` proves algebraic network; `TraceClassQuantumCorner` proves abstract certified corner composition | Literal Hilbert direct-sum inclusion/compression, complete positivity, trace nonincrease, normality, exact CP history theorem |
| 21 | `zero-frequency-repaired-source-dx-over-x-law` | No exact card module found | Determinate representing measure, exact density comparison for every nonnegative Borel weight, measure-class corollary |
| 22 | `zero-frequency-repaired-source-mellin-threshold` | No exact card module found | Determinacy/representation, all positive real Mellin exponents finite, zero and negative exponents infinite |
| 23 | `zero-frequency-reservoir-density-laplace-equivalence` | No exact card module found | Radon--Nikodym density, logarithmic asymptotic, Laplace uniqueness and target recovery |

## Active lane

- **Card:** `common-profile-boolean-anchor-curvature`
- **Exact claim:** complete the currently started finite signed-shear tensor package before opening
  analytic arithmetic obligations.
- **Status:** `[PAPER-PROVED]`, partial Lean only.
- **Open core:** exact tensor rank/inertia/eigenvalue and sharp norm laws `(SG2)`--`(SG8a)` on the
  actual finite local kernels, then protected-anchor alias `(SG10)`.
- **Reason for first lane:** existing modules already prove `(CG1)`--`(CG7)` at the correct abstract
  level and sign-surjectivity; remaining finite-dimensional linear algebra is dependency-closed and
  reusable by later coherence work.

## Gates

- [x] All 23 source cards read and initial exact-obligation inventory recorded.
- [x] First local-corpus research query completed.
- [ ] Every exact proved claim represented by unconditional Lean.
- [ ] Every leaf checked and final targeted build passed.
- [ ] Every promoted declaration passes axiom and formal-lint gates.
- [ ] All 23 cards moved to Stage 3 with exact certificates.

## Log

- 2026-08-26 — sweep opened; read all source cards, project scientific method, frontier map matches,
  endpoints matches, and existing Stage-3/Lean surfaces. Serena symbol operations do not support
  Lean in this project (`Active languages: ['python']`), so Lean symbol inventory uses `rg`.
- 2026-08-26 — card 4 finite algebra completed in passing leaf checks. Corpus-first reuse includes
  `commonGramBooleanAnchorCurvature`, `productDifferenceKernel_signedBranchExpansion`,
  `DistinctPrimeFamily`, `quadraticCongruenceRootCountTotal_*`, canonical CRT, additive-character
  Parseval infrastructure, tensor inertia/norm infrastructure,
  `totient_prod_of_pairwise_coprime`, and `quadraticCongruenceNormalizedRootSum_mul_alias`.
  Remaining `(SG9)` requires the literal physical window/BV response, absent from current corpus;
  no conditional interface will be introduced.
