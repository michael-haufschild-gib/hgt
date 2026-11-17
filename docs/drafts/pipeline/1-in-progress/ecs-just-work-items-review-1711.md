# ECS just-work items of review 1711 (E-J10–E-J15)

- **ID:** ecs-just-work-1711
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper → Lean), one module per item
- **Source:** docs/reports/review-1711/route-ecs.md §4
- **Statement:** the six just-work items of the ECS route report, each as unconditional Lean theorems.

## Goal
Close the assembly-level gaps of the ECS route listed in §4 of the report: the ladder in Pick form, the Ω± sign law at the rate of the zeros, mean squares at the exact rate, the trace inequality of the ladder, the pointwise edge law at the wall, and the prime-side rows of stage 2. None of them is RH.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven (per item)
- [ ] 2 → 3  formalized (per item)

## Items (easiest first)

| Item | Module (ECS/) | Status |
|---|---|---|
| E-J15 prime-side rows of stage 2 | Index/StageTwoHasPrimeSideRows.lean | formalized: `stageTwo_primeSide_tfae` (B13 ⇔ finite layer ⇒ real-amplitude positivity above X ⇔ bounded confined index ⇒ no critical state ⇔ finite wave law ⇒ empty wave ⇔ finite wave law ⇒ positivity above X); `confinedIndexBounded_iff_exists_finiteWaveLaw`; `no_criticalState_iff_jasRealPositiveAbove_of_finiteOffLine`; `riemannHypothesis_iff_exists_finiteWaveLaw_empty` |
| E-J11 sign law at the rate of the zeros | Decay/TheSignLawHoldsAtTheRateOfTheZeros.lean | formalized: Landau against an exponential (`integrable_exp_of_tail_le_exp`); (a) `criticalState_re_le_of_tail_le_exp`, `criticalState_not_tail_le_exp`, Θ-form `criticalState_omega_pm` (both signs exceed e^{cu} for c > 17/2 − Θ, square moments finite for b < 17 − 2Θ); (b) `criticalState_unseen_of_beyondWall_le_exp`, `criticalState_beyondWall_not_tail_le_exp` (any seen zero, c < ½ − Re ρ), `criticalState_beyondWall_omega_pm`; dichotomy `riemannHypothesis_or_criticalState_omega_pm` |
| E-J12 mean squares at the exact rate | Modes/TheAveragedStateHasAMeanSquareAtTheExactRate.lean, Modes/TheHeatedProfileBeyondTheWallHasAMeanSquareAtTheExactRate.lean | formalized: T⁻¹∫_0^T (e^{(17/2−Θ)t}Ā)² → extremal pair sum (`criticalState_tendsto_meanSquare_ratedAveragedState`), positive iff Θ attained (`extremalModeMass_pos_iff`, `criticalState_meanSquare_attained_dichotomy`); beyond the wall: the heated zero series is real (`heatedZeroSeries_im`), T⁻¹∫(e^{−κT}a(F⁺_ε − (e^{−8u}F)_ε))² → mirror pair sum (`criticalState_tendsto_meanSquare_ratedHeatedBeyondWall`), positive iff a zero on Re z = −κ is seen (`mirrorModeMass_pos_iff`) |
| E-J13 trace inequality of the ladder | Index/TheLadderSatisfiesATraceInequality.lean | formalized: Bessel against the zero exponentials (`sum_norm_sq_laplace_div_le`), one rung (`IsConfinedNullVector.criticalAliasCoefficient_mul_le_offLine`), trace inequality `IsCriticalLadder.sum_criticalAliasCoefficient_le` (Σ_j a(R_j) ≤ Σ offLineWeight, finite layer), `succ_mul_criticalAliasCoefficient_le`, linear growth `succ_mul_div_le_ratio`, counting form `sqrt_sixtyThree_mul_sum_le` |
| E-J10 ladder in Pick form | Index/WindowTestsCarryTheNegativeSpacesOfTheConfinedForm.lean, Pick/TheConfinedPickMatricesComputeEveryRungOfTheLadder.lean | formalized: lower semicontinuity of Q_R along window tests (`fullEnergy_le_of_tendsto_sq`), window recoveries with convergent energies (`exists_isWindowRecovery`), polarization (`IsWindowRecovery.tendsto_mixedEnergy`), window tests carry negative spaces (`exists_window_family_of_negative`); probe sums carry a negative window family (`exists_pick_family_of_window`); index ≤ j up to R_j (`IsCriticalLadder.hermNegIndex_confinedProbeGram_le`), ≥ j+1 beyond (`IsCriticalLadder.exists_le_hermNegIndex`); every rung in Pick form (`IsCriticalLadder.isGreatest_confinedPick`), ratios independent of the ladder (`IsCriticalLadder.ratio_eq`) |
| E-J14 pointwise edge law at the wall | | not started |

## Paper proofs

### E-J15
(a) B13 ⇒ row: FiniteOffLine ⇒ RH ⇒ real-amplitude positivity above some X (exists_jasRealPositiveAbove_one_of_riemannHypothesis). Row ⇒ B13: FiniteOffLine and positivity above X give RH (riemannHypothesis_iff_finiteOffLine_and_jasRealPositiveAbove). Under a finite layer: no critical state ⇔ RH (beyond-the-wall prime continuation) ⇔ positivity above some X.
(b) ConfinedIndexBounded ⇔ FiniteOffLine (confinedIndexBounded_tfae) ⇔ {Re ≠ ½} finite (Im of the spectral point is ½ − Re ρ) ⇔ finite wave law (finite_offLine_iff_exists_offLineWave). The empty wave law is RH (von Koch both ways). So B13 ⇔ (finite wave law ⇒ empty wave law) ⇔ (finite wave law ⇒ positivity above some X).

### E-J10 (plan)
Fix a ladder Φ_0..Φ_k, ratios R_0 ≤ … ≤ R_k. (1) R ≤ R_k: Q_R is block diagonal against the rungs (null vectors pair through W₈ only) and ≥ 0 on their W₈-complement (floor), so Q_R(X) ≥ −Σ_{R_i<R}(a(R_i)−a(R))W₈(Φ_i,X)²/W₈(Φ_i): every Pick matrix is PSD plus a rank-≤k correction, index ≤ k. (2) R > R_k: Q_R is negative definite on span Φ. Window recovery (exists_window_energy_recovery) gives window tests H_i^n → Φ_i in L² with W₈ bounded and limsup Q_R(H_i^n) ≤ Q_R(Φ_i); lower semicontinuity under L² convergence with bounded W₈ (exists_domain_limit_of_smooth_energy_limit) applied to H_i^n ± H_j^n plus the parallelogram law gives convergence of every Gram entry, so the window Gram is eventually negative definite; window tests → probe sums (zero coordinates in ℓ², |G − P| ≤ εe^{6u}) transfers it to an integer Pick matrix with k+1 negative squares.

## Conjecture ledger

## Log
- 2026-11-17 — created in 1-in-progress
