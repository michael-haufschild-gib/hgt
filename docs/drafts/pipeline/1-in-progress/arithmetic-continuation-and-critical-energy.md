# Arithmetic Continuation and Critical Energy (ACCE)

- **ID:** acce
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) — programme
- **Source:** docs/reports/review-2110/astra.md § "New field - research programme"
- **Statement:** Which exact arithmetic relations prevent a complete signed critical energy from
  escaping under continuation in damping, cutoff or aperture?

## Goal
A Lean programme (`formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy`) supplying
the continuation and compensation theorems the RH work lacks: transport of an *endpoint* budget
backwards through a damping interval, the exact signed-work identity of the damped Möbius energy,
the countermodels that fix which uniformity is indispensable, and the discrete envelope tools for
sector compensation.

Non-circularity: every criterion names its arithmetic input (a horizon-uniform bound on one signed
pairing) and nothing about zeros. The continuation machinery itself is unconditional real analysis.

## Gates
- [x] 0 → 1  in-progress: objects fixed (energy family, admission, continuation, compensation)
- [ ] 1 → 2  fully-proven: paper proofs of the pillars
- [ ] 2 → 3  formalized: Lean modules + umbrella wiring
- [ ] 3 → 4  n/a (no stage 4)

## Approach
1. **Admission language.** `EnergyFamily := ℝ → ℕ → ℝ`; `Admits E ε := ∃ B, ∀ T, E ε T ≤ B`.
2. **Osgood/Grönwall backward continuation.** `Ψ` a primitive of `1/Φ`, `β` a primitive of the
   continuation budget: `-ψ(E_T) · E_T' ≤ β'` on `[a,c]` forces `Ψ(E_T(a)) ≤ Ψ(E_T(c)) + β(c) - β(a)`;
   coercive `Ψ` turns a budget at `c` into a budget at `a`, uniformly in the horizon.
3. **Signed work identity.** `∂_ε E_T(ε) = 2 Σ_{n≤T} A_ε(n) E_ε(n)/(n(n+1))` for the centred damped
   divisor prefix, from the owned tangent law.
4. **Criterion.** A horizon-uniform integrable bound on the *negative part* of the signed work on
   every `[a,1/2]` gives cofinal admission, hence RH.
5. **Selectivity.** (i) the tangent-norm receiver implies the signed-work criterion (so the new
   demand is formally weaker); (ii) a two-coordinate rotation has zero signed work and arbitrarily
   large tangent norm (so it is strictly weaker); (iii) `T^{2(1/2-ε)}-1` satisfies a per-horizon
   continuation bound with endpoint budget and still escapes (so horizon uniformity is the theorem).
6. **Compensation.** Complete signed three-term decomposition; affine recurrence envelope for (R);
   recovery-is-not-control countermodel.

## Log
- 2026-10-22 — created in 1-in-progress; programme initiated from astra.md.

## Lean assets (programme folder `formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy`)
- `CriticalEnergyFamilies` — `Admits`, `CofinallyAdmits`, `UniformlyAdmitsOn`.
- `BackwardContinuationCalculus` — `scaledEnergy_add_budget_le` (master monotonicity),
  `one_add_le_mul_exp_of_linear_work` (Grönwall), `bddAbove_of_tendsto_atTop` (coercive recovery),
  `monotoneOn_of_hasDerivAt_nonneg_Ici`.
- `ContinuationTransportsAdmission` — `LinearContinuation`, `OsgoodContinuation`,
  `Admits.of_linearContinuation`, `Admits.of_osgoodContinuation`,
  `cofinallyAdmits_of_linearContinuation`, `cofinallyAdmits_of_osgoodContinuation`.
- `HorizonUniformityIsTheTheorem` — `escapeEnergy`, `hasDerivAt_escapeEnergy`,
  `not_admits_escapeEnergy`, `not_linearContinuation_escapeEnergy`.
- `AffineRecurrenceEnvelope` — `affineEnvelope`, `le_affineEnvelope`, `affineEnvelope_eq`,
  `affineEnvelope_le_of_contraction`, `affineEnvelope_one_one`.
- `GroundFloorNoCrossing` — `floor_le_of_relative_decay`, `floor_le_of_relative_decay_Ico`.
- `TheDampedMobiusCriticalEnergy` — `dampedMobiusEnergy`, `mem_receiverDampings_iff_admits`,
  `riemannHypothesis_iff_cofinallyAdmits`.
- `SignedDampingWorkOfTheMobiusEnergy` — `signedDampingWork`, `hasDerivAt_dampedMobiusEnergy`
  (`∂_ε E_T = 2W_T`), `two_mul_signedDampingWork_eq_markov` (bridge to the owned Markov flux form),
  `neg_two_mul_signedDampingWork_le_of_tangentNorm_le`.
- `TheDampingContinuationCriterion` — `riemannHypothesis_of_dampingContinuation_endpoint`,
  `riemannHypothesis_of_dampingContinuation_above_half_abscissa`,
  `zetaZeroAbscissa_le_half_add_of_partial_dampingContinuation`,
  `dampingContinuation_of_tangentNorm_le`,
  `arithmeticDampingTotalJumpEnergy_le_of_continuation_bound`.
- `TheSignedWorkDemandIsStrictlyWeaker` — `exists_vanishing_signed_work_with_large_tangent`.
- `SuperlinearOsgoodScale` — `riemannHypothesis_of_superlinear_dampingContinuation`.
- `CompensationNeedsItsCrossTerms` — `pronicNorm_add_sq`, `exists_sector_count_complete_energy_gt`,
  `exists_ratio_tendsto_zero_and_complete_unbounded`.

Foundational README: `formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/README.md`
(shared-target section synchronised across the now eight programme READMEs; new programme added to
the shared section as the continuation layer with mechanism 6).

## Log
- 2026-10-22 — programme folder, umbrella `GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy`
  wired into `MainTheorems`, foundational README written.

## Related cards (not duplicates)
- `astra-whole-report-programme.md` — audit of all three astra opportunities; extends this programme.
- `astra-opportunity1-signed-damping-continuation.md` — the conjecture (C) itself, the open
  arithmetic input consumed by `riemannHypothesis_of_dampingContinuation_endpoint`.

This card is the programme card: folder, umbrella, README and the continuation calculus.

## Log
- 2026-10-22 — programme co-developed with a second agent in the same folder: the covariance half of
  (C) is the open demand (scalar half paid, renormalisation neutral), cutoff transport added as the
  second parameter, and the depth-sampling bridge moved to `SquareRootThreshold`. All 16 modules in
  the folder carry fresh oleans; umbrella matches the folder and is wired into `MainTheorems`.
  `scripts/formal_tools.py` `ALLOWED_ROOT_LEAN` extended with the programme umbrella.

## Log
- 2026-10-22 — continuation layer deepened by four modules (all compiled, all wired into the
  umbrella):
  - `TheDampingAverageOfTheRelativeLossSuffices` — the relative loss `−E'_T/(1+E_T)`; a horizon-free
    bound on its *damping average* transports admission (`Admits.of_averagedContinuation`);
    `integral_relativeLoss_eq` identifies the average with `log` of the shifted-energy ratio;
    `AveragedContinuation.of_linearContinuation` (no integrability of `β'` needed, via the one-sided
    FTC); the thinning-spike family separates averaged from pointwise
    (`exists_averagedContinuation_not_linearContinuation`); the arithmetic relative loss is
    unconditionally interval integrable; `riemannHypothesis_of_averaged_tangentNorm` replaces the
    pointwise integrable majorant of `‖E_ε‖_T` by its damping average.
  - `TheSignedWorkIsTheTangentAutocorrelation` — `signedDampingWork_eq_pairing_add_integral`:
    `W_T(ε) = ⟪A_δ, E_ε⟫_T + ∫_δ^ε K_T(η, ε) dη` with `K_T` the pronic Gram kernel of the tangent
    family; the diagonal is `‖E_ε‖_T²`, so the obstruction is off-diagonal anti-correlation;
    `riemannHypothesis_of_nonneg_tangentCorrelation` (a sign, budget = the paid scalar constant) and
    `riemannHypothesis_of_bounded_anticorrelationTotal`.
  - `TheAveragedBudgetIsExactlyAdmission` — `averagedContinuation_iff_admits` and
    `riemannHypothesis_iff_cofinal_averagedDampingContinuation`: the averaged budget is calibrated
    exactly to the conclusion. `exists_admits_everywhere_not_linearContinuation`: a family admitted
    at *every* parameter with no pointwise budget on any interval, so the pointwise form of (C) is
    not implied by RH — (C) should be stated in averaged form.
  - `TheMaxKernelFormOfTheDampingAutocorrelation` — `pronicPairing_prefix_eq_maxKernel`:
    `Σ_{n≤T}(Σ_{j≤n}a_j)(Σ_{k≤n}b_k)/(n(n+1)) = Σ_{j,k≤T} a_j b_k/max(j,k) − (Σa)(Σb)/(T+1)`;
    `maxKernel_quadForm_eq` (Nyman–Beurling kernel psd with an exact formula);
    `tangentCorrelation_eq_maxKernel` puts the continuation obstruction in prime-pair coordinates;
    `riemannHypothesis_of_maxKernelForm_ge_boundary`.
- 2026-10-22 (cont.) — eight further modules, all compiled and wired:
  - `ThePolarCalibrationOfTheMaxKernelForm` — closed forms `Σ_{k≤T}1/max(j,k) = 1−1/j+Σ_{j≤m≤T}1/m`
    and `Σ_{j,k≤T}1/max(j,k) = 2T−Σ_{m≤T}1/m`; `maxKernelForm_increment_eq` separates the prime-pair
    form from two row-weighted prime sums and the explicit polar term, so the sign criterion needs
    cancellation to relative precision `1/T`.
  - `TheLevelCollapseOfTheMaxKernelForm` — `sum_sum_div_max_eq_level_sum`: the double kernel sum is a
    single scale sum `Σ_M (a_M B_M + A_M b_M − a_M b_M)/M`; `tangentCorrelation_eq_level_sum`;
    `pronicNorm_dampedChebyshevError_sq_eq_level_sum` (discrete `d(E²) = 2E dE − (dE)²`).
  - `RelativeStabilityOfTheTangentFamily` — polarisation: the autocorrelation's sign is an angle;
    `riemannHypothesis_of_relative_tangent_stability` (`‖E_η − E_ε‖_T ≤ ‖E_ε‖_T` ⟹ RH); a large
    tangent is never by itself an obstruction.
  - `TheEscapeIsAnInteriorBump` — `tendsto_dampedMobiusEnergy_nhdsGT_zero` (zero-damping limit is the
    pronic mass, ≤ 1, for every horizon): both ends of the damping range are paid, so the escape is
    interior; `riemannHypothesis_of_no_interior_bump`,
    `riemannHypothesis_of_convexOn_dampedMobiusEnergy`,
    `exists_unbounded_interior_bump_of_not_riemannHypothesis`.
  - `TheSignedWorkChangesSignOnce` — `riemannHypothesis_of_signedWork_single_sign_change` (shape, no
    constants), `riemannHypothesis_of_monotoneOn_signedWork`, `riemannHypothesis_of_nonneg_signedWork`.
  - `TheSecondDampingTangentAndConvexity` — the second damped von Mangoldt weight
    `Λ⁽²⁾_η(k) = Σ_{d∣k} μ(d)(log d)² d^{-η}`, the readout derivative from `ζ''`, the second tangent
    `F_η`, `hasDerivAt_signedDampingWork` (`W'_T = ‖E_ε‖_T² + ⟪A_ε,F_ε⟫_T`), and the constant-free
    criterion `riemannHypothesis_of_second_tangent_pairing_ge`.
  - `HorizonAveragesAndSparseHorizons` — monotonicity in the horizon: dyadic horizons suffice,
    Cesàro means suffice (`Admits.of_cesaro`, `admits_iff_cesaro`), with the two arithmetic criteria.
  - `TheApertureFloorTransportFromTheCertifiedEndpoint` — derivative-free multiplicative transport of
    a floor (`mul_prod_le_of_relative_step`, `one_sub_sum_le_prod_one_sub`,
    `half_le_of_relative_decay_steps`), instantiated on the aperture face from the certified endpoint
    `3/10` (`groundEnergy_ge_of_relative_step` keeps `μ ≥ 1/10000`;
    `riemannHypothesis_of_groundEnergy_relative_step`) — open problem 7's endpoint identified;
    `tendsto_prod_one_sub_harmonic_zero` shows summability is not a formality.
- 2026-10-22 (cont. 2) — six further modules (all compiled, all wired):
  - `TheTangentIsADilationAverageOfTheSource` — `sum_Icc_divisor_convolution_eq_dilation` (hyperbola),
    `dampedVonMangoldt_eq_dilation_convolution` (the tangent row is the source row dilated by prime
    powers), `dampedChebyshevError_eq_dilation` (integer-prefix dilation identity with its explicit
    correction), `signedDampingWork_eq_dilationForm_add_correction` (the work is the numerical range
    of the prime dilation operator at the literal source), `riemannHypothesis_of_nonneg_dilationForm_add_correction`.
  - `TheQuotientIncidenceKernelIsIndefinite` — the kernel `κ_ε(n,m) = Σ_{⌊n/j⌋=m} Λ(j)j^{-ε}`;
    `quotientIncidenceKernel_self = 0` (zero diagonal, since `Λ(1)=0`), `κ_ε(2,1) = log 2 · 2^{-ε}`,
    `exists_row_rowDilationForm_neg`: form positivity is impossible, the sign must use the source.
  - `TheDilationInversionLawOfTheSource` — `dampedTwist` is a ring homomorphism of the Dirichlet ring
    (`dampedTwist_mul`, `dampedTwist_one`); `sum_rpow_mul_rawPrefix_eq` (`Σ_{j≤n} j^{-ε}A^raw(⌊n/j⌋) = n`)
    and `sum_rpow_mul_centeredPrefix_eq`; `exists_centeredPrefix_ge_of_dilation_law`.
  - `TheDilationCalculusOnIntegerPrefixes` — `prefixDilation_comp` (`D^f ∘ D^g = D^{f*g}` exactly,
    integer parts included), `sum_divisors_dampedPrime_mul_rpow` (`Λ_ε * ζ_ε = (log)_ε`),
    `prefixDilation_dampedLog_centeredPrefix` (the log-dilation law of the source).
  - `TheCutoffParameterCostsNothingBeyondAdmission` — open problem 6 closed:
    `ramanujanPhysicalShellEnergy_le_energy_add`, `sum_shellWindow_energy_eq`,
    `summable_shellErrorBudget`, and
    `exists_bound_sum_ramanujanPhysicalShellEnergy_of_admits`: given admission at a damping the
    accumulated physical shell cost is bounded there, so the cutoff parameter is free.
  - `TheSelfImprovingEnergyIdentity` — `dampedMobiusEnergy_eq_pairing_sub`:
    `E_T = ⟪A,ρ_ε⟫ − ⟪A, D^{ζ_ε,≥2}A⟫` with `ρ_ε(n) = n − m₀(ε)Φ_ε(n)` explicit (the unit level of
    the positive dilation kernel is the energy itself); `admits_of_sublinear_pairings` gives
    admission at a *single* damping from two `κ√E_T + κ'` bounds — no transport, no interval;
    `riemannHypothesis_of_cofinal_sublinear_pairings`.
- 2026-10-22 (cont. 3) — six further modules (all compiled, all wired):
  - `TheTangentObeysAnExplicitDilationLaw` — `prefixDilation_dampedUnit_dampedChebyshevError`: the
    damped unit dilation of the tangent is Möbius-free (von Mangoldt weights, floors, two densities).
  - `TheWorkIntegralIsTheEnergyDrop` — `integral_signedDampingWork_eq` (`∫_a^c 2W_T = E_T(c) − E_T(a)`),
    `admits_iff_bounded_neg_work_integral` (the additive dictionary),
    `exists_signedDampingWork_lt_of_not_admits` (escape is visible as deep negative work).
  - `TheDilationSelfSimilarityOfThePronicMeasure` — `sum_Icc_pronic_dilation_fibre`: a dilation fibre
    carries exactly `1/j` of the level's pronic mass, hence the sharp contraction
    `pronicNorm_rowDilate_le_sharp` (`1/√j`); `abs_pronicPairing_offDiagonalHead_le`: every finite
    head of the dilation scales is paid, so the obstruction is the tail.
  - `TheMajorantSourceIsNeverAdmitted` — the row `d ↦ d^{-ε}` dominates `|μ(d)d^{-ε}|` cell by cell
    (`abs_pmPowerDamped_le_majorant`), its centred prefix obeys
    `A^maj ≤ −2^{-(1+ε)} n^{1-ε}` (`majorantCenteredPrefix_le`, via `dyadic_block_le_zeta_tail`), and
    its pronic energy diverges for every `ε ≤ 1/2` (`not_admits_majorantEnergy`): the named,
    unconditional selectivity certificate — a sign-blind estimate proves a false statement.
- 2026-10-22 (cont. 4) — eleven further modules (all compiled, all wired):
  - `TheSecondTangentIsAnIteratedDilation` — `pmul_log_mul` (log is a derivation),
    `(μ log²) * 1 = Λ*Λ − Λ log`, and `dampedChebyshevSecond_eq_dilation`: the second tangent is the
    source dilated by the second-order prime kernel; the convexity criterion in dilation coordinates.
  - `TheFunctionFieldCalibration` — the `F_q[T]` model: `fqCenteredPrefix_eq` (the centred source is
    exactly `q^{-ε}`), `fqEnergy_le_one`, `fqUniformlyAdmitsOn` (budget zero), and
    `exists_fqPerturbedPrefix_gt`: a single extra degree destroys it. The calibration the README asks
    for: (C) is vacuous over `F_q[T]`, and the reason is the exact degree-wise Möbius vanishing.
  - `SecondTangentControlGivesTheAngle` — `pronicNorm_dampedChebyshevError_sub_le` (mean value in the
    pronic norm) and `riemannHypothesis_of_second_tangent_majorant`.
  - `TheWorkIsACorrelationWithWindowMeans` — the pronic adjoint of a dilation is a fibre average
    (`pronicPairing_rowDilate_eq`, `rowFibreAverage_const`), so the work is the correlation of the
    source with its own window means (`rowDilationForm_eq_fibreAverage_pairing`).
  - `ReadingsOfTheSignCriterion` — the Markov reading (`riemannHypothesis_of_flux_ge_jump_add_forcing`),
    the dyadic reading, and `dampedMobiusEnergy_pos` (the criterion is not vacuous).
  - `ThePositiveCoreOfTheDilationForm` — `rowDilationForm_one_pos` (the constant row has a positive
    core) and `rowDilationForm_split_at_one`/`signedDampingWork_split_at_one`: the complete
    decomposition at the constant source, cross terms kept.
  - `TheTangentFactorsThroughTheMoebiusDilation` — `Λ_ε = μ_ε * (log)_ε`, so
    `dampedChebyshevError_eq_moebiusDilation`: the tangent is the Möbius dilation of a Möbius-free row.
  - `AntiCorrelatedDampingsAreFew` — `card_le_of_pairwise_anticorrelated`: at most `1 + 1/δ` dampings
    can be pairwise `δ`-anti-correlated; the obstruction is finite in the damping parameter.
  - `TheEscapeIsAnOutAndBackExcursion` — `integral_pronicNorm_tangent_ge`: an interior excursion is
    paid twice, so failure forces `∫‖E_ε‖ ≥ 2√E_T(ε) − (two paid ends)`: the exact converse of the
    averaged tangent-norm criterion.
  - `TheApertureFloorUnderAbsoluteDecay` — the additive aperture transport and the window-positivity
    corollary in SRT's units.
  - `TheEscapeIsATailPhenomenon` — `abs_pmPowerDampedCenteredDivisorPrefix_sub_one_le`
    (`|A_ε(n) − 1| ≤ ε Σ_{d≤n}(log d)⌊n/d⌋ + n m₀(ε)`, from the classical `Σ μ(d)⌊n/d⌋ = 1`) and
    `exists_damping_head_energy_le`: the escape lives beyond every fixed horizon.
- 2026-10-22 (cont. 5) — five further modules (all compiled, all wired):
  - `TheCompleteAccountingOfTheWork` — `rowDilationPairing_right_one` (the right cross term is the
    pairing with the damped Chebyshev prefix), `rowDilationPairing_left_one` (the left one is the
    pairing with the prime-weighted window means), `abs_rowDilationForm_le` (the quadratic term is at
    most the prime-dilation series times the energy), and `signedDampingWork_accounting`.
  - `TheCoreDominanceCriterion` — `workCore`/`workLinearWindow`/`workLinearPrefix`/`workQuadratic`
    and `riemannHypothesis_of_core_dominance`: a comparison in explicit units, no unspecified
    constants; `workCore_pos`.
  - `TheQuadraticTermIsTheResidualEnergy` — `pronicNorm_deviationRow_sq` (the deviation's energy is
    the dual residual) and the quadratic term in the units of the residual and of the energy.
  - `TheCoreGrowsLikeTheInverseDamping` — `dampedPrimePrefix_ge_powersOfTwo` and
    `dampedPrimePrefix_ge_inv_damping`: the core is of order `1/ε`, but only beyond `2^{1/ε}`.
  - `TheAveragedCriterionOnSparseHorizons` — `energy_le_of_averaged_horizon` (per-horizon transport)
    and `riemannHypothesis_of_averaged_dyadic`: the averaged budget only has to be checked at dyadic
    horizons.
- 2026-10-22 (cont. 6) — the free anchor and the core debt (all compiled, all wired):
  - `TheFreeAnchorAtZeroDamping` — `dampedMobiusEnergy_le_pronicMass_add`,
    `admits_of_work_integral_bound` (budget `1 + B`), `work_integral_le_of_bddAbove`, and
    `riemannHypothesis_iff_cofinal_work_integral_bound`: RH is exactly a horizon-uniform bound on the
    signed work accumulated from zero damping — no endpoint admission, no zero-free band, since the
    undamped source is constant and the pronic mass is below one.
  - `TheIntegratedCoreIsAPrimeCount` — `integral_rpow_neg_eq`, `integral_dampedPrimePrefix_eq`,
    `integral_workCore_eq`, `integral_workCore_ge` (Chebyshev form), `workDeviation` and
    `integral_workDeviation_le_of_bddAbove`.
  - `TheCoreDebtIsThePrimeHarmonicSeries` — `sum_Icc_pronic_from`,
    `integral_workCore_eq_scaleSum` (the integrated core as one sum over scales with density
    `Λ(j)/log j`), `tendsto_primeHarmonic_atTop`, `integral_workCore_ge_primeHarmonic`,
    `exists_horizon_integral_workCore_ge` and `integral_workDeviation_le_primeHarmonic`.
    Consequence: the explicit positive core is a **debt** of size `Σ_{p ≤ T/2} 1/p`, and under any
    energy budget the integrated deviation must carry it. The continuation obstruction is the
    divergence of the prime harmonic series.
- 2026-10-24 — Open Problem 1 resolved (`SignedAveragedContinuationAndTheZeroWidthBand`):
  - Eight-way equivalence `signedAveragedContinuation_tfae` connecting `Admits dampedMobiusEnergy a`,
    `a ∈ receiverDampings`, `AveragedDampingContinuation a c`, dyadic relative-loss continuation,
    additive signed work continuation, dyadic additive work continuation, Cesàro additive work
    continuation, and `AveragedResidualContinuation a c`.
  - Unconditional signed continuation across `(Θ − ½, ∞)` (`averagedDampingContinuation_of_zetaZeroAbscissa_sub_half_lt`,
    `exists_neg_signedDampingWork_integral_le_of_zetaZeroAbscissa_sub_half_lt`), exact threshold
    `sInf_averagedContinuationThresholds_eq_zetaZeroAbscissa_sub_half`, and boundary shadow law
    `analyticOrderAt_le_of_averagedDampingContinuation_at_zeroWidth`.
  - Unconditional horizon-uniform continuation on the Vinogradov–Korobov band
    `exists_signedWorkIntegral_and_relativeLoss_le_on_vinogradovKorobovBand` and all-damping
    sub-power saving `eventually_signedWorkIntegral_and_relativeLoss_le_vk_saving`.
- 2026-10-24 (cont.) — Open Problem 2 resolved (`SourceAngleShapeHierarchyAndIntegratedAutocorrelation`):
  - First-horizon separation on the actual source: `tendsto_signedDampingWork_one`,
    `not_forall_signedDampingWork_nonneg`, `tangentCorrelation_one`, and
    `exists_damping_tangentCorrelation_one_pos_and_signedDampingWork_one_neg`.
  - Strict separations `exists_pos_pairing_not_relative_stability`,
    `exists_single_sign_change_not_monotoneOn`, and `uniformlyAdmitsOn_of_no_interior_bump`.
  - Exact double-integral identity `double_integral_tangentCorrelation_eq_pronicNorm_sub_sq`,
    unconditional positivity `double_integral_tangentCorrelation_nonneg`, equivalence with admission
    `admits_iff_bounded_double_integral_tangentCorrelation`, and unconditional bounds above `Θ − ½`
    and on the Vinogradov–Korobov band.
- 2026-10-24 (cont. 2) — Open Problem 3 resolved (`PrimePairLevelSumAndRelativePrecisionCancellation`):
  - Exact identity `polarCalibratedPrimePairForm_eq_levelSum`, diagonal positivity up to boundary
    `diagonal_polarCalibratedPrimePairForm_ge_boundary`, `diagonal_primePairMaxKernelForm_ge`, and
    level-sum forms of the energy and work (`dampedMobiusEnergy_eq_level_sum_sub_boundary`,
    `signedDampingWork_eq_level_sum_sub_boundary`).
  - Unconditional integrated nonnegativity up to boundary on `[a, c] × [a, c]`
    (`double_integral_polarCalibratedPrimePairForm_ge_boundary`,
    `double_integral_levelSum_ge_boundary`).
  - Equivalence with relative-precision `1/(T+1)` cancellation
    `admits_iff_relative_precision_inv_T_primePair`, and unconditional `O(1/T)` cancellation above
    `Θ − ½` (`exists_relative_precision_inv_T_primePair_above_zeroWidth`,
    `tendsto_relative_precision_primePair_zero_above_zeroWidth`) and on the Vinogradov–Korobov band
    (`exists_relative_precision_inv_T_primePair_on_vinogradovKorobovBand`).
