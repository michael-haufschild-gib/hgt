import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheAveragedBudgetIsExactlyAdmission
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheAveragedCriterionOnSparseHorizons
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheWorkIntegralIsTheEnergyDrop
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.RenormalizationPreservesDampingContinuation
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.AdmissionTranslatesZerosWithMultiplicityUpToTheBoundary
import GaloisForLFunctions.BezoutValuationIncidence.AllDampingVinogradovKorobovBandAndInteriorGrowth

/-!
# Signed Averaged Continuation, the Zero-Width Frontier, and the Vinogradov–Korobov Band

This module resolves Open Problem 1 and the first research topic of
`ArithmeticContinuationAndCriticalEnergy`:

1. **The Eight-Way Equivalence of Signed Continuation (`signedAveragedContinuation_tfae`)**:
   For any `0 < a ≤ c` with an admitted right endpoint `c`, the following are mutually equivalent:
   - admission `Admits dampedMobiusEnergy a` (`a ∈ receiverDampings`);
   - signed relative-loss averaged continuation `AveragedDampingContinuation a c`;
   - dyadic-horizon signed relative-loss averaged continuation
     `∃ C, ∀ k, ∫_a^c r_{2^k}(ε) dε ≤ C`;
   - additive signed work continuation `∃ C, ∀ T, ∫_a^c −2 W_T(ε) dε ≤ C`;
   - dyadic-horizon additive signed work continuation `∃ C, ∀ k, ∫_a^c −2 W_{2^k}(ε) dε ≤ C`;
   - Cesàro-averaged signed work continuation
     `∃ C, ∀ N, ∑_{T ≤ N} ∫_a^c −2 W_T(ε) dε ≤ C (N + 1)`;
   - residual signed relative-loss averaged continuation `AveragedResidualContinuation a c`;
   - residual additive signed work continuation `∃ C, ∀ T, ∫_a^c −2 W_T^{res}(ε) dε ≤ C`.

2. **Unconditional Continuation Across `(Θ − ½, ∞)` and the Exact Threshold `Δ = Θ − ½`**:
   - Every damping `ε > Θ − ½` is unconditionally admitted
     (`admits_dampedMobiusEnergy_of_zetaZeroAbscissa_sub_half_lt`), so all eight signed
     continuation budgets hold unconditionally on every compact interval `[a, c]` with
     `Θ − ½ < a ≤ c` (`averagedDampingContinuation_of_zetaZeroAbscissa_sub_half_lt`,
     `exists_neg_signedDampingWork_integral_le_of_zetaZeroAbscissa_sub_half_lt`).
   - Conversely, for any `0 ≤ a₀ < Θ − ½` and any admitted `c > a₀`, continuation fails at some
     `a ∈ (a₀, min c (Θ − ½))` (`exists_not_averagedDampingContinuation_below_zeroWidth`), and the
     infimum of the thresholds `a₀ ≥ 0` above which `AveragedDampingContinuation a (1/2)` holds on
     `(a₀, 1/2]` equals `Θ − ½` (`sInf_averagedDampingContinuation_threshold_eq`).
   - At the boundary `a = Θ − ½`, if `Θ > ½` is attained at a zero `ρ₀`, continuation down to
     `Θ − ½` forces a critical-line shadow `½ + i Im ρ₀` of at least the same multiplicity
     (`analyticOrderAt_le_of_averagedDampingContinuation_at_zeroWidth`), and without such a shadow
     the continuable left endpoints in `[Θ − ½, c]` are `(Θ − ½, c]`
     (`averagedDampingContinuation_inter_Ici_eq_Ioc`).

3. **Unconditional Vinogradov–Korobov Band Continuation and All-Damping Sub-Power Savings**:
   - Along the Vinogradov–Korobov band `a ≥ ½ − κ σ(T) / (480 log T)` above any floor `ε₀ > 0`,
     the additive signed work integral `∫_a^c −2 W_T`, the signed relative-loss integral
     `∫_a^c r_T`, and the residual work integral `∫_a^c −2 W_T^{res}` are all bounded uniformly in
     `T`, `a`, and `c` (`exists_signedWorkIntegral_and_relativeLoss_le_on_vinogradovKorobovBand`),
     whereas the Ramanujan-isometric parity twin grows as `c (log(T+1) − log 100)`.
   - At every fixed sub-half damping `0 < a < ½` and `a ≤ c`, the additive signed work integral
     and signed relative-loss integral obey the unconditional Vinogradov–Korobov saving
     `∫_a^c −2 W_T ≤ C T^{1−2a} exp(−κ σ(T)/270)` and
     `∫_a^c r_T ≤ log(1 + C T^{1−2a} exp(−κ σ(T)/270))`
     (`eventually_signedWorkIntegral_and_relativeLoss_le_vk_saving`).
-/

open Set Filter Topology Finset MeasureTheory RHTower RHTower.Sieve
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open GaloisForLFunctions.BiScaleUncertainty

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. Residual Averaged and Additive Work Continuation -/

/-- The damping derivative of the dual residual `pmPowerDampedDualResidual` as a family indexed by
the horizon. -/
def residualMobiusEnergyDeriv (T : ℕ) (ε : ℝ) : ℝ := 2 * residualDampingWork ε T

/-- **An averaged continuation budget for the Báez–Duarte dual residual on `[a, c]`.** -/
def AveragedResidualContinuation (a c : ℝ) : Prop :=
  AveragedContinuation pmPowerDampedDualResidual residualMobiusEnergyDeriv a c

theorem continuousOn_pmPowerDampedDualResidual (T : ℕ) :
    ContinuousOn (fun ε => pmPowerDampedDualResidual ε T) (Ioi 0) :=
  fun _ hε => (hasDerivAt_pmPowerDampedDualResidual (mem_Ioi.mp hε) T).continuousAt.continuousWithinAt

theorem continuousOn_residualDampingWork' (T : ℕ) :
    ContinuousOn (fun ε => residualDampingWork ε T) (Ioi 0) := by
  unfold residualDampingWork
  refine continuousOn_finsetSum _ fun n _ ε hε => ?_
  have hε0 : (0 : ℝ) < ε := mem_Ioi.mp hε
  have h1 : ContinuousAt (fun x => pmPowerDampedCenteredDivisorPrefix x n - 1) ε :=
    ((hasDerivAt_pmPowerDampedCenteredDivisorPrefix hε0 n).continuousAt).sub continuousAt_const
  have h2 : ContinuousAt (fun x => dampedChebyshevError x n) ε :=
    (continuousOn_dampedChebyshevError n).continuousAt (isOpen_Ioi.mem_nhds hε)
  exact ((h1.mul h2).div_const _).continuousWithinAt

theorem intervalIntegrable_relativeLoss_residual {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) (T : ℕ) :
    IntervalIntegrable (relativeLoss pmPowerDampedDualResidual residualMobiusEnergyDeriv T)
      volume a c := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hac]
  intro ε hε
  have hε0 : (0 : ℝ) < ε := lt_of_lt_of_le ha hε.1
  have hmem : ε ∈ Ioi (0 : ℝ) := mem_Ioi.mpr hε0
  have hW : ContinuousAt (fun x => -(residualMobiusEnergyDeriv T x)) ε :=
    (((continuousOn_residualDampingWork' T).continuousAt
      (isOpen_Ioi.mem_nhds hmem)).const_mul 2).neg
  have hden : ContinuousAt (fun x => 1 + pmPowerDampedDualResidual x T) ε :=
    continuousAt_const.add ((continuousOn_pmPowerDampedDualResidual T).continuousAt
      (isOpen_Ioi.mem_nhds hmem))
  have hpos : 0 ≤ pmPowerDampedDualResidual ε T :=
    sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (by positivity)
  exact (hW.div hden (by positivity)).continuousWithinAt

theorem intervalIntegrable_residualDampingWork {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) (T : ℕ) :
    IntervalIntegrable (fun ε => 2 * residualDampingWork ε T) volume a c := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hac]
  exact continuousOn_const.mul ((continuousOn_residualDampingWork' T).mono
    fun x hx => mem_Ioi.mpr (lt_of_lt_of_le ha hx.1))

/-- **The residual work integral is the residual energy drop.** -/
theorem integral_residualDampingWork_eq {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) (T : ℕ) :
    (∫ ε in a..c, 2 * residualDampingWork ε T) =
      pmPowerDampedDualResidual c T - pmPowerDampedDualResidual a T := by
  have hderiv : ∀ ε ∈ uIcc a c,
      HasDerivAt (fun x => pmPowerDampedDualResidual x T) (2 * residualDampingWork ε T) ε := by
    rw [uIcc_of_le hac]
    exact fun ε hε => hasDerivAt_pmPowerDampedDualResidual (lt_of_lt_of_le ha hε.1) T
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_residualDampingWork ha hac T)

/-- **Uniform bound on the integrated difference between actual work and residual work.** -/
theorem exists_abs_integral_signedWork_sub_residualWork_le {a : ℝ} (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, a ≤ c → ∀ T : ℕ,
      |(∫ ε in a..c, 2 * signedDampingWork ε T) -
        (∫ ε in a..c, 2 * residualDampingWork ε T)| ≤ 2 * K * (c - a) := by
  obtain ⟨K, hK0, hK⟩ := exists_uniform_scalar_damping_work_bound ha
  refine ⟨K, hK0, fun c hac T => ?_⟩
  rw [← intervalIntegral.integral_sub (intervalIntegrable_signedDampingWork ha hac T)
    (intervalIntegrable_residualDampingWork ha hac T)]
  have hbound : ∀ ε ∈ Icc a c,
      ‖2 * signedDampingWork ε T - 2 * residualDampingWork ε T‖ ≤ 2 * K := by
    intro ε hε
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      signedDampingWork_sub_residualDampingWork]
    exact mul_le_mul_of_nonneg_left (hK ε hε.1 T) (by norm_num)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const' hac hbound
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hac)] at h
  exact h

/-- **Residual averaged continuation is equivalent to admission.** -/
theorem averagedResidualContinuation_iff_admits {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hc : Admits dampedMobiusEnergy c) :
    AveragedResidualContinuation a c ↔ Admits dampedMobiusEnergy a := by
  have hc_res : Admits pmPowerDampedDualResidual c := (admits_damped_residual_iff c).mpr hc
  have hpos : ∀ ε ∈ Icc a c, ∀ T, 0 ≤ pmPowerDampedDualResidual ε T :=
    fun _ _ _ => sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (by positivity)
  exact (averagedContinuation_iff_admits hac hpos
    (fun T _ hε => hasDerivAt_pmPowerDampedDualResidual (lt_of_lt_of_le ha hε.1) T)
    (fun T => intervalIntegrable_relativeLoss_residual ha hac T) hc_res).trans
    (admits_damped_residual_iff a)

/-- **Renormalization neutrality for averaged continuation.** Subtracting the constant source
preserves averaged continuation on every compact positive damping interval with an admitted right
endpoint. -/
theorem averagedResidualContinuation_iff_averagedDampingContinuation {a c : ℝ}
    (ha : 0 < a) (hac : a ≤ c) (hc : Admits dampedMobiusEnergy c) :
    AveragedResidualContinuation a c ↔ AveragedDampingContinuation a c :=
  (averagedResidualContinuation_iff_admits ha hac hc).trans
    (averagedDampingContinuation_iff_admits ha hac hc).symm

/-- **Admission is a horizon-free bound on the integrated negative residual work.** -/
theorem admits_iff_bounded_neg_residualWork_integral {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hc : Admits dampedMobiusEnergy c) :
    Admits dampedMobiusEnergy a ↔
      ∃ C : ℝ, ∀ T : ℕ, (∫ ε in a..c, -(2 * residualDampingWork ε T)) ≤ C := by
  rw [← admits_damped_residual_iff a]
  have hc_res : Admits pmPowerDampedDualResidual c := (admits_damped_residual_iff c).mpr hc
  have hint : ∀ T : ℕ, (∫ ε in a..c, -(2 * residualDampingWork ε T)) =
      pmPowerDampedDualResidual a T - pmPowerDampedDualResidual c T := by
    intro T
    rw [intervalIntegral.integral_neg, integral_residualDampingWork_eq ha hac T]
    ring
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨max B 0, fun T => ?_⟩
    rw [hint T]
    have h0 : 0 ≤ pmPowerDampedDualResidual c T :=
      sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (by positivity)
    linarith [(hB T).trans (le_max_left B 0)]
  · rintro ⟨C, hC⟩
    obtain ⟨B, hB⟩ := hc_res
    refine ⟨C + max B 0, fun T => ?_⟩
    have h := hC T
    rw [hint T] at h
    linarith [(hB T).trans (le_max_left B 0)]

/-! ## §2. Dyadic and Cesàro Equivalences and the Eight-Way TFAE -/

/-- **Dyadic averaged continuation is equivalent to full averaged continuation.** -/
theorem averagedDampingContinuation_iff_dyadic {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hc : Admits dampedMobiusEnergy c) :
    AveragedDampingContinuation a c ↔
      ∃ C : ℝ, ∀ k : ℕ,
        (∫ ε in a..c, relativeLoss dampedMobiusEnergy dampedMobiusEnergyDeriv (2 ^ k) ε) ≤ C := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun k => (hC (2 ^ k)).2⟩
  · rintro ⟨C, hC⟩
    rw [averagedDampingContinuation_iff_admits ha hac hc]
    obtain ⟨B, hB⟩ := hc
    refine Admits.of_dyadic_horizons (C := (1 + max B 0) * Real.exp C - 1)
      (dampedMobiusEnergy_mono a) fun k => ?_
    exact energy_le_of_averaged_horizon ha hac (2 ^ k) (hC k) (hB (2 ^ k))

/-- **Admission is equivalent to a dyadic-horizon bound on the additive signed work integral.** -/
theorem admits_iff_dyadic_neg_work_integral {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hc : Admits dampedMobiusEnergy c) :
    Admits dampedMobiusEnergy a ↔
      ∃ C : ℝ, ∀ k : ℕ, (∫ ε in a..c, -(2 * signedDampingWork ε (2 ^ k))) ≤ C := by
  rw [admits_iff_bounded_neg_work_integral ha hac hc]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun k => hC (2 ^ k)⟩
  · rintro ⟨C, hC⟩
    have ⟨B, hB⟩ := hc
    have hadm : Admits dampedMobiusEnergy a := by
      refine Admits.of_dyadic_horizons (C := C + max B 0) (dampedMobiusEnergy_mono a) fun k => ?_
      have hk := hC k
      rw [intervalIntegral.integral_neg, integral_signedDampingWork_eq ha hac (2 ^ k)] at hk
      linarith [(hB (2 ^ k)).trans (le_max_left B 0)]
    exact (admits_iff_bounded_neg_work_integral ha hac hc).mp hadm

/-- **Admission is equivalent to a Cesàro-averaged bound on the additive signed work integral.** -/
theorem admits_iff_cesaro_neg_work_integral {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hc : Admits dampedMobiusEnergy c) :
    Admits dampedMobiusEnergy a ↔
      ∃ C : ℝ, ∀ N : ℕ,
        (∑ T ∈ range (N + 1), ∫ ε in a..c, -(2 * signedDampingWork ε T)) ≤
          C * ((N : ℝ) + 1) := by
  rw [admits_iff_cesaro (dampedMobiusEnergy_mono a) (fun T => dampedMobiusEnergy_nonneg a T)]
  have hint : ∀ T : ℕ, (∫ ε in a..c, -(2 * signedDampingWork ε T)) =
      dampedMobiusEnergy a T - dampedMobiusEnergy c T := by
    intro T
    rw [intervalIntegral.integral_neg, integral_signedDampingWork_eq ha hac T]
    ring
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun N => ?_⟩
    calc (∑ T ∈ range (N + 1), ∫ ε in a..c, -(2 * signedDampingWork ε T))
        = ∑ T ∈ range (N + 1), (dampedMobiusEnergy a T - dampedMobiusEnergy c T) :=
          sum_congr rfl fun T _ => hint T
      _ ≤ ∑ T ∈ range (N + 1), dampedMobiusEnergy a T :=
          sum_le_sum fun T _ => by linarith [dampedMobiusEnergy_nonneg c T]
      _ ≤ C * ((N : ℝ) + 1) := hC N
  · rintro ⟨C, hC⟩
    obtain ⟨B, hB⟩ := hc
    refine ⟨C + max B 0, fun N => ?_⟩
    have hN := hC N
    have hsum : (∑ T ∈ range (N + 1), ∫ ε in a..c, -(2 * signedDampingWork ε T)) =
        (∑ T ∈ range (N + 1), dampedMobiusEnergy a T) -
          (∑ T ∈ range (N + 1), dampedMobiusEnergy c T) := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun T _ => hint T
    have hc_sum : (∑ T ∈ range (N + 1), dampedMobiusEnergy c T) ≤ max B 0 * ((N : ℝ) + 1) := by
      calc (∑ T ∈ range (N + 1), dampedMobiusEnergy c T)
          ≤ ∑ _T ∈ range (N + 1), max B 0 :=
            sum_le_sum fun T _ => (hB T).trans (le_max_left B 0)
        _ = max B 0 * ((N : ℝ) + 1) := by
            rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
    linarith

/-- **The Eight-Way Equivalence of Signed Averaged Continuation.**
For any `0 < a ≤ c` with `Admits dampedMobiusEnergy c`, admission at `a`, membership in
`receiverDampings`, relative-loss averaged continuation, dyadic relative-loss continuation,
additive signed work continuation, dyadic additive work continuation, Cesàro additive work
continuation, and residual averaged continuation are all equivalent. -/
theorem signedAveragedContinuation_tfae {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hc : Admits dampedMobiusEnergy c) :
    List.TFAE
      [ Admits dampedMobiusEnergy a,
        a ∈ receiverDampings,
        AveragedDampingContinuation a c,
        ∃ C : ℝ, ∀ k : ℕ,
          (∫ ε in a..c, relativeLoss dampedMobiusEnergy dampedMobiusEnergyDeriv (2 ^ k) ε) ≤ C,
        ∃ C : ℝ, ∀ T : ℕ, (∫ ε in a..c, -(2 * signedDampingWork ε T)) ≤ C,
        ∃ C : ℝ, ∀ k : ℕ, (∫ ε in a..c, -(2 * signedDampingWork ε (2 ^ k))) ≤ C,
        ∃ C : ℝ, ∀ N : ℕ,
          (∑ T ∈ range (N + 1), ∫ ε in a..c, -(2 * signedDampingWork ε T)) ≤
            C * ((N : ℝ) + 1),
        AveragedResidualContinuation a c ] := by
  tfae_have 1 ↔ 2 := (mem_receiverDampings_iff_admits ha).symm
  tfae_have 1 ↔ 3 := (averagedDampingContinuation_iff_admits ha hac hc).symm
  tfae_have 3 ↔ 4 := averagedDampingContinuation_iff_dyadic ha hac hc
  tfae_have 1 ↔ 5 := admits_iff_bounded_neg_work_integral ha hac hc
  tfae_have 1 ↔ 6 := admits_iff_dyadic_neg_work_integral ha hac hc
  tfae_have 1 ↔ 7 := admits_iff_cesaro_neg_work_integral ha hac hc
  tfae_have 1 ↔ 8 := (averagedResidualContinuation_iff_admits ha hac hc).symm
  tfae_finish

/-! ## §3. Unconditional Signed Continuation Across `(Θ − ½, ∞)` and the Exact Threshold Law -/

/-- **Unconditional admission above the zero width `Θ − ½`.** -/
theorem admits_dampedMobiusEnergy_of_zetaZeroAbscissa_sub_half_lt {ε : ℝ}
    (hε : zetaZeroAbscissa - 1 / 2 < ε) : Admits dampedMobiusEnergy ε := by
  have hε0 : 0 < ε := by linarith [half_le_zetaZeroAbscissa]
  exact (mem_receiverDampings_iff_admits hε0).mp
    (Ioi_zetaZeroAbscissa_sub_half_subset_receiverDampings hε)

/-- **Unconditional signed averaged continuation across the zero-width half-line.**
For every `a, c` with `Θ − ½ < a ≤ c`, `AveragedDampingContinuation a c` holds unconditionally. -/
theorem averagedDampingContinuation_of_zetaZeroAbscissa_sub_half_lt {a c : ℝ}
    (ha : zetaZeroAbscissa - 1 / 2 < a) (hac : a ≤ c) :
    AveragedDampingContinuation a c := by
  have ha0 : 0 < a := by linarith [half_le_zetaZeroAbscissa]
  have hc : Admits dampedMobiusEnergy c :=
    admits_dampedMobiusEnergy_of_zetaZeroAbscissa_sub_half_lt (ha.trans_le hac)
  exact (averagedDampingContinuation_iff_admits ha0 hac hc).mpr
    (admits_dampedMobiusEnergy_of_zetaZeroAbscissa_sub_half_lt ha)

/-- **Unconditional additive signed work continuation across the zero-width half-line.**
For every `a, c` with `Θ − ½ < a ≤ c`, `∫_a^c −2 W_T(ε) dε` is bounded uniformly in `T`. -/
theorem exists_neg_signedDampingWork_integral_le_of_zetaZeroAbscissa_sub_half_lt {a c : ℝ}
    (ha : zetaZeroAbscissa - 1 / 2 < a) (hac : a ≤ c) :
    ∃ C : ℝ, ∀ T : ℕ, (∫ ε in a..c, -(2 * signedDampingWork ε T)) ≤ C := by
  have ha0 : 0 < a := by linarith [half_le_zetaZeroAbscissa]
  have hc : Admits dampedMobiusEnergy c :=
    admits_dampedMobiusEnergy_of_zetaZeroAbscissa_sub_half_lt (ha.trans_le hac)
  exact (admits_iff_bounded_neg_work_integral ha0 hac hc).mp
    (admits_dampedMobiusEnergy_of_zetaZeroAbscissa_sub_half_lt ha)

/-- **Unconditional residual averaged continuation across the zero-width half-line.** -/
theorem averagedResidualContinuation_of_zetaZeroAbscissa_sub_half_lt {a c : ℝ}
    (ha : zetaZeroAbscissa - 1 / 2 < a) (hac : a ≤ c) :
    AveragedResidualContinuation a c := by
  have ha0 : 0 < a := by linarith [half_le_zetaZeroAbscissa]
  have hc : Admits dampedMobiusEnergy c :=
    admits_dampedMobiusEnergy_of_zetaZeroAbscissa_sub_half_lt (ha.trans_le hac)
  exact (averagedResidualContinuation_iff_admits ha0 hac hc).mpr
    (admits_dampedMobiusEnergy_of_zetaZeroAbscissa_sub_half_lt ha)

/-- **Sharpened endpoint criterion: the interval to cross is `(0, Θ − ½]`.**
Every damping `c > Θ − ½` is unconditionally admitted, so signed averaged continuation from any
`c > Θ − ½` down to `0` gives the Riemann Hypothesis (improving the `Θ / 2` endpoint of
`riemannHypothesis_of_dampingContinuation_above_half_abscissa` by `½ (1 − Θ)`). -/
theorem riemannHypothesis_of_averagedDampingContinuation_above_zeroWidth {c : ℝ}
    (hc : zetaZeroAbscissa - 1 / 2 < c)
    (h : ∀ a : ℝ, 0 < a → a ≤ c → AveragedDampingContinuation a c) :
    RiemannHypothesis :=
  riemannHypothesis_of_averagedDampingContinuation_endpoint
    (by linarith [half_le_zetaZeroAbscissa])
    (admits_dampedMobiusEnergy_of_zetaZeroAbscissa_sub_half_lt hc) h

/-- **No uniform continuation across the zero width.**
If `0 ≤ a₀ < Θ − ½` and `c > a₀` is admitted, then there exists `a ∈ (a₀, min c (Θ − ½)]` at
which `AveragedDampingContinuation a c` fails and the additive signed work integral
`∫_a^c −2 W_T` is unbounded in `T`. -/
theorem exists_not_averagedDampingContinuation_below_zeroWidth {a₀ c : ℝ}
    (ha₀ : 0 ≤ a₀) (hlt : a₀ < zetaZeroAbscissa - 1 / 2) (ha₀c : a₀ < c)
    (hc : Admits dampedMobiusEnergy c) :
    ∃ a : ℝ, a₀ < a ∧ a ≤ c ∧ a ≤ zetaZeroAbscissa - 1 / 2 ∧
      ¬ AveragedDampingContinuation a c ∧
      (∀ C : ℝ, ∃ T : ℕ, C < ∫ ε in a..c, -(2 * signedDampingWork ε T)) := by
  by_contra hcon
  push Not at hcon
  have hc_min : a₀ < min c (zetaZeroAbscissa - 1 / 2) := lt_min ha₀c hlt
  have hstrip : zetaZeroAbscissa ≤ 1 / 2 + a₀ := by
    refine zetaZeroAbscissa_le_half_add_of_partial_averagedDampingContinuation ha₀ ha₀c hc
      fun a ha1 ha2 => ?_
    rcases le_or_gt a (zetaZeroAbscissa - 1 / 2) with hle | hgt
    · by_contra hna
      obtain ⟨C, hC⟩ := hcon a ha1 ha2 hle hna
      have ha0 : 0 < a := lt_of_le_of_lt ha₀ ha1
      have hadm : Admits dampedMobiusEnergy a :=
        (admits_iff_bounded_neg_work_integral ha0 ha2 hc).mpr ⟨C, hC⟩
      exact hna ((averagedDampingContinuation_iff_admits ha0 ha2 hc).mpr hadm)
    · exact averagedDampingContinuation_of_zetaZeroAbscissa_sub_half_lt hgt ha2
  linarith

/-- The set of thresholds `a₀ ≥ 0` above which `AveragedDampingContinuation a (1/2)` holds on
`(a₀, 1/2]`. -/
def averagedContinuationThresholds : Set ℝ :=
  {a₀ : ℝ | 0 ≤ a₀ ∧ ∀ a : ℝ, a₀ < a → a ≤ 1 / 2 → AveragedDampingContinuation a (1 / 2)}

theorem zetaZeroAbscissa_sub_half_mem_averagedContinuationThresholds :
    zetaZeroAbscissa - 1 / 2 ∈ averagedContinuationThresholds :=
  ⟨by linarith [half_le_zetaZeroAbscissa],
    fun _ ha hac => averagedDampingContinuation_of_zetaZeroAbscissa_sub_half_lt ha hac⟩

theorem le_of_mem_averagedContinuationThresholds {a₀ : ℝ}
    (h : a₀ ∈ averagedContinuationThresholds) :
    zetaZeroAbscissa - 1 / 2 ≤ a₀ := by
  rcases lt_or_ge a₀ (1 / 2) with hlt | hge
  · have hstrip := zetaZeroAbscissa_le_half_add_of_partial_averagedDampingContinuation h.1 hlt
      (admits_dampedMobiusEnergy_of_half_le le_rfl) h.2
    linarith
  · linarith [zetaZeroAbscissa_le_one]

/-- **The exact threshold of signed averaged continuation is the zero width `Δ = Θ − ½`.** -/
theorem sInf_averagedContinuationThresholds_eq_zetaZeroAbscissa_sub_half :
    sInf averagedContinuationThresholds = zetaZeroAbscissa - 1 / 2 := by
  refine le_antisymm ?_ ?_
  · exact csInf_le ⟨0, fun _ hx => hx.1⟩
      zetaZeroAbscissa_sub_half_mem_averagedContinuationThresholds
  · exact le_csInf ⟨_, zetaZeroAbscissa_sub_half_mem_averagedContinuationThresholds⟩
      fun _ hx => le_of_mem_averagedContinuationThresholds hx

/-- **Boundary zero-shadow law at `a = Δ = Θ − ½`.**
If `Θ > ½` is attained at a zero `ρ₀` and `AveragedDampingContinuation (Θ − ½) c` holds from an
admitted `c ≥ Θ − ½`, then `½ + i Im ρ₀` is a critical-line zero of `ζ` of multiplicity at least
that of `ρ₀`. -/
theorem analyticOrderAt_le_of_averagedDampingContinuation_at_zeroWidth {ρ₀ : ℂ} {c : ℝ}
    (hz : riemannZeta ρ₀ = 0) (hmax : ρ₀.re = zetaZeroAbscissa) (hgt : 1 / 2 < ρ₀.re)
    (hc : zetaZeroAbscissa - 1 / 2 ≤ c) (hadm_c : Admits dampedMobiusEnergy c)
    (hcont : AveragedDampingContinuation (zetaZeroAbscissa - 1 / 2) c) :
    analyticOrderAt riemannZeta ρ₀ ≤ analyticOrderAt riemannZeta (1 / 2 + (ρ₀.im : ℂ) * Complex.I) := by
  have hpos : 0 < zetaZeroAbscissa - 1 / 2 := by linarith
  have hadm := (mem_receiverDampings_iff_averagedDampingContinuation hpos hc hadm_c).mpr hcont
  exact analyticOrderAt_le_of_zetaZeroAbscissa_mem_receiverDampings hz hmax hgt hadm

/-- **Unattained boundary when an extremal zero lacks a critical-line shadow.**
If `ρ₀` (`Re ρ₀ = Θ > ½`) has strictly larger multiplicity than `½ + i Im ρ₀`, then for any
admitted `c ≥ Θ − ½`, the dampings in `[Θ − ½, c]` that admit signed averaged continuation from
`c` are exactly the half-open interval `(Θ − ½, c]`. -/
theorem averagedDampingContinuation_inter_Ici_eq_Ioc {ρ₀ : ℂ} {c : ℝ}
    (hz : riemannZeta ρ₀ = 0) (hmax : ρ₀.re = zetaZeroAbscissa) (hgt : 1 / 2 < ρ₀.re)
    (hshadow : analyticOrderAt riemannZeta (1 / 2 + (ρ₀.im : ℂ) * Complex.I) <
      analyticOrderAt riemannZeta ρ₀)
    (hadm_c : Admits dampedMobiusEnergy c) :
    {a : ℝ | zetaZeroAbscissa - 1 / 2 ≤ a ∧ a ≤ c ∧ AveragedDampingContinuation a c} =
      Ioc (zetaZeroAbscissa - 1 / 2) c := by
  ext a
  simp only [mem_setOf_eq, Set.mem_Ioc]
  constructor
  · rintro ⟨ha1, ha2, hcont⟩
    rcases ha1.lt_or_eq with hlt | heq
    · exact ⟨hlt, ha2⟩
    · rw [← heq] at ha2 hcont
      exact absurd
        (analyticOrderAt_le_of_averagedDampingContinuation_at_zeroWidth hz hmax hgt ha2 hadm_c hcont)
        (not_le.mpr hshadow)
  · rintro ⟨ha1, ha2⟩
    exact ⟨ha1.le, ha2, averagedDampingContinuation_of_zetaZeroAbscissa_sub_half_lt ha1 ha2⟩

/-! ## §4. Unconditional Vinogradov–Korobov Band Continuation and All-Damping Sub-Power Savings -/

/-- **Unconditional Horizon-Uniform Signed Continuation on the Vinogradov–Korobov Band.**
For every damping floor `ε₀ > 0`, there exists `E ≥ 0` such that for every horizon `T : ℕ` and
every interval `[a, c] ⊆ [ε₀, 1/2]` inside the Vinogradov–Korobov band
`a ≥ 1/2 − κ σ(T) / (480 log T)`:
1. `(∫ ε in a..c, -(2 * signedDampingWork ε T)) ≤ E`;
2. `(∫ ε in a..c, relativeLoss dampedMobiusEnergy dampedMobiusEnergyDeriv T ε) ≤ Real.log (1 + E)`;
3. `(∫ ε in a..c, -(2 * residualDampingWork ε T)) ≤ 3 * E + 2`.
Meanwhile, the Ramanujan-isometric parity twin `parityTwinWeight a` satisfies
`E_T(c'_a) ≥ c_twin * (log(T+1) − log 100)`. -/
theorem exists_signedWorkIntegral_and_relativeLoss_le_on_vinogradovKorobovBand
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ E c_twin : ℝ, 0 ≤ E ∧ 0 < c_twin ∧
      ∀ (T : ℕ) (a c : ℝ), ε₀ ≤ a → a ≤ c → c ≤ 1 / 2 →
        1 / 2 - vkKappa * vkScale T / (480 * Real.log T) ≤ a →
          (∫ ε in a..c, -(2 * signedDampingWork ε T)) ≤ E ∧
          (∫ ε in a..c, relativeLoss dampedMobiusEnergy dampedMobiusEnergyDeriv T ε) ≤
            Real.log (1 + E) ∧
          (∫ ε in a..c, -(2 * residualDampingWork ε T)) ≤ 3 * E + 2 ∧
          c_twin * (Real.log ((T : ℝ) + 1) - Real.log 100) ≤
            weightPronicEnergy (parityTwinWeight a) (dampedDensity a) T := by
  obtain ⟨E, hE0, hE⟩ := exists_receiver_le_on_vinogradovKorobovBand_of_pos hε₀
  refine ⟨E, (twinDriftConstantAt ε₀ / 16) ^ 2 / 4, hE0,
    by have := twinDriftConstantAt_pos hε₀; positivity,
    fun T a c ha_ge hac hc2 hband => ?_⟩
  have ha0 : 0 < a := hε₀.trans_le ha_ge
  have ha2 : a ≤ 1 / 2 := hac.trans hc2
  have hEa : dampedMobiusEnergy a T ≤ E := hE T a ha_ge ha2 hband
  have hEc0 : 0 ≤ dampedMobiusEnergy c T := dampedMobiusEnergy_nonneg c T
  have h1 : (∫ ε in a..c, -(2 * signedDampingWork ε T)) ≤ E := by
    rw [intervalIntegral.integral_neg, integral_signedDampingWork_eq ha0 hac T]
    linarith
  have h2 : (∫ ε in a..c, relativeLoss dampedMobiusEnergy dampedMobiusEnergyDeriv T ε) ≤
      Real.log (1 + E) := by
    rw [integral_relativeLoss_eq hac (fun ε _ => dampedMobiusEnergy_nonneg ε T)
      (fun ε hε => hasDerivAt_dampedMobiusEnergy_deriv (lt_of_lt_of_le ha0 hε.1) T)
      (intervalIntegrable_relativeLoss_dampedMobiusEnergy ha0 hac T)]
    have hlogc : 0 ≤ Real.log (1 + dampedMobiusEnergy c T) := Real.log_nonneg (by linarith)
    have hloga : Real.log (1 + dampedMobiusEnergy a T) ≤ Real.log (1 + E) :=
      Real.log_le_log (by linarith [dampedMobiusEnergy_nonneg a T]) (by linarith)
    linarith
  have h3 : (∫ ε in a..c, -(2 * residualDampingWork ε T)) ≤ 3 * E + 2 := by
    rw [intervalIntegral.integral_neg, integral_residualDampingWork_eq ha0 hac T]
    have hcomp := (one_add_damped_energy_comparison a T).1
    have hrc0 : 0 ≤ pmPowerDampedDualResidual c T :=
      sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (by positivity)
    linarith
  exact ⟨h1, h2, h3, parityTwin_receiver_ge_of_pos hε₀ ha_ge ha2 T⟩

/-- **Unconditional All-Damping Sub-Power and Logarithmic Vinogradov–Korobov Saving for Signed
Continuation.**
For every fixed `0 < a < 1/2`, there exists `C ≥ 0` such that for all `c ≥ a` and all large `T : ℕ`,
the additive signed work integral and the signed relative-loss integral across `[a, c]` satisfy
`∫_a^c −2 W_T ≤ C T^{1−2a} exp(−κ σ(T)/270)` and
`∫_a^c r_T ≤ log(1 + C T^{1−2a} exp(−κ σ(T)/270))`. -/
theorem eventually_signedWorkIntegral_and_relativeLoss_le_vk_saving
    {a : ℝ} (ha0 : 0 < a) (ha2 : a < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℕ in atTop, ∀ c : ℝ, a ≤ c →
      (∫ ε in a..c, -(2 * signedDampingWork ε T)) ≤
        C * (T : ℝ) ^ (1 - 2 * a) * Real.exp (-(vkKappa * vkScale T / 270)) ∧
      (∫ ε in a..c, relativeLoss dampedMobiusEnergy dampedMobiusEnergyDeriv T ε) ≤
        Real.log (1 + C * (T : ℝ) ^ (1 - 2 * a) * Real.exp (-(vkKappa * vkScale T / 270))) := by
  obtain ⟨C, hC0, hev⟩ := eventually_receiver_le_growth_of_pos ha0 ha2
  refine ⟨C, hC0, ?_⟩
  filter_upwards [hev] with T hT c hac
  set B := C * (T : ℝ) ^ (1 - 2 * a) * Real.exp (-(vkKappa * vkScale T / 270))
  have hEa : dampedMobiusEnergy a T ≤ B := by
    unfold dampedMobiusEnergy
    exact hT
  have hEc0 : 0 ≤ dampedMobiusEnergy c T := dampedMobiusEnergy_nonneg c T
  constructor
  · rw [intervalIntegral.integral_neg, integral_signedDampingWork_eq ha0 hac T]
    linarith
  · rw [integral_relativeLoss_eq hac (fun ε _ => dampedMobiusEnergy_nonneg ε T)
      (fun ε hε => hasDerivAt_dampedMobiusEnergy_deriv (lt_of_lt_of_le ha0 hε.1) T)
      (intervalIntegrable_relativeLoss_dampedMobiusEnergy ha0 hac T)]
    have hlogc : 0 ≤ Real.log (1 + dampedMobiusEnergy c T) := Real.log_nonneg (by linarith)
    have hloga : Real.log (1 + dampedMobiusEnergy a T) ≤ Real.log (1 + B) :=
      Real.log_le_log (by linarith [dampedMobiusEnergy_nonneg a T]) (by linarith)
    linarith

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
