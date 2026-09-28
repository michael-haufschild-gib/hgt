# Six-folder stage-2 → stage-3 Lean goal (started 2026-09-28)

Goal: unconditional Lean for every proven theorem of every card in `2-fully-proven/{chronological,
01-bottcher-complex-dynamics, 02-analytic-da-entire-functions, 03-ht-translation-projective-geometry,
04-rg-stochastic-quantum-fields, 11-rh-zero-divisor-geometry}`; then move each card to stage 3.
Per-folder detail stays in the folder ledgers (`_STAGE3-LEDGER.md`, `_SWEEP-LEDGER.md`,
`chronological-stage3-sweep-working-log.md`, `formal/GaloisForLFunctions/Bottcher/STATUS.md`).

| Folder | Card | Open core | Status |
|---|---|---|---|
| 02 | first-order-autonomous-algebraic-ap-periodicity | — | **DONE → stage 3** (4 HTGeometry modules) |
| 02 | smooth-stein-order-two-autonomous-ade-frequency-rank | Taubes replaceable: Reeb field preserves Webster metric ⇒ flow closure is a torus ⇒ β closed | TODO |
| 02 | entire-heat-multiplicative-da-order-three-floor | global Strelitz component argument | TODO |
| 02 | asymptotically-exponential-algebraic-cascade-unit-cost | — | **DONE → stage 3** (6 HTGeometry modules; entire Briot–Bouquet) |
| 02 | entire-composition-hypertranscendence-or-law | Steinmetz reduction (HT∘HT) | TODO |
| 03 | combination-mode-reducibility-baker-bridge | polynomial effective Baker (Matveev) | TODO |
| 03 | hypertranscendental-maximal-finite-horizon-galois-law | parent full-symmetric monodromy, brick D | TODO |
| 03 | projective-horizon-hankel-secant-stratification | normality r≥2, rational singularities | TODO |
| 04 | gadc / noisy-binary-tree / exact-rational-rg | Ritt implication, weighted-homogeneous residual | TODO |
| 01 | six Böttcher cards | Brolin/cylinder monodromy; E–vS; q62 hole-free tip gap | TODO |
| chrono | finite-tail-obstruction | — | **DONE → stage 3** (12 RHTower modules + quantitative weighted boundary) |
| chrono | growing-moment-source | — | **DONE → stage 3** (8 RHTower modules) |
| chrono | recovery-exponential-rate | DONE 2026-09-28 → `3-formalized/`; HTGeometry/ChronologicalTensor CubicRecovery* + ArcsineLogIntegral + GaussianFrullaniLogKernel | DONE |
| chrono | recovery-uniform-spectrum | DONE 2026-09-28 → `3-formalized/`; `CubicRecoveryUniformGrowth`, `CubicRecoverySpectralDisc` | DONE |
| 11 | verified-height-one-zero-turing-extension | needs 10^13-zero certified computation | BLOCKED (rules) |

## AP-periodicity route (no Schwartz, no normalization)
1. Minimal-Y-degree relation Q ⇒ Q_Y(f,f') ≢ 0; real z0 with f'(z0)≠0, Q_Y(f(z0),f'(z0))≠0.
2. Local uniqueness: strict derivative of Q at (a0,b0) ⇒ |v'−w'| ≤ K|v−w| ⇒ Grönwall ⇒ v=w.
3. ε-almost period τ ⇒ c small (open mapping) with f(·+τ)=f(·+c) ⇒ period ω=τ−c.
4. Im ω=0 ⇒ real period. Else Im ω_n→0, heights kβ_n dense ⇒ |f| ≤ sup_ℝ|f| on a substrip ⇒
   Bochner compactness + maximum modulus ⇒ f constant. Contradiction.
5. Period ⇒ Bohr spectrum ⊆ (2π/p)ℤ ⇒ Γ(f) cyclic, rank 1.

## Log
- 2026-09-28: survey of all 22 cards; ledger created.
- 2026-09-28: AP-periodicity card promoted (FirstOrderRelationLocalUniqueness, ImStripTranslateCompactness,
  FirstOrderAlgebraicStripPeriodicity, FirstOrderAlgebraicStripFrequencyGroup).
- 2026-09-28: cascade card promoted; entire Briot–Bouquet proved (CasoratiWeierstrassAtInfinity,
  FirstOrderRepeatedRegularValue, AutonomousFirstOrderEntirePeriod/Classification, LaurentExpGrowth,
  AutonomousFirstOrderCascadeUnitCost).
- 2026-09-28: finite-tail card promoted. Chain: TailInjectivity, TailRiemann, TailProjectionPerturbation,
  TailSampleSpace, TailKernelLipschitz, TailHeatVectors, TailNormals, WeightedSourceFloor, TailObservation,
  TailWeight, FiniteTailObstruction, LeastNormMomentRepair; WeightedBoundary gained the quantitative
  bound |M(w)(ρ)| ≤ M|ζ'(ρ)|, which gives main theorem and survivor in one route.
- 2026-09-28: growing-moment-source card promoted. Modules: ZeroChargeTailBounds, BoseKernelJets,
  HalfTailGram, MobiusHalfPrefixMoments, GrowingMomentSource, BoseCothRemainder, BoseCothLocalBounds,
  GrowingSignedProjection (29 audited capstones). Reused HTGeometry `bernoulli_two_mul_ne_zero`,
  `iteratedDeriv_cexp`, `cosh_sub_one_le`, corpus Lambert regrouping and PNT little-o.
- 2026-09-28: `chronological-recovery-exponential-rate` formalized (rate, E_{2m}, consequences, equilibrium measure with energy minimality + uniqueness, S_m/m → A) and moved to `3-formalized/`.
- 2026-09-28: `chronological-recovery-uniform-spectrum` formalized (growth inequality, uniform limit, ‖U^d‖, spectrum = closed disc, complexification) and moved to `3-formalized/`. Chronological folder complete.
