import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalSignedCompensationSaturation
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTransitionCoreAbelSourceMultiGateWeld
import GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovPrimeNumberTheorem
import GaloisForLFunctions.BezoutValuationIncidence.ReceiverBoundedInTheVinogradovKorobovBand

/-!
# Vinogradov–Korobov decay of the completed Suzuki residual

The completed Abel source is the positive causal resolvent of the normalized
Chebyshev error, with bounded polar and archimedean corrections. Splitting the
causal history at half the logarithmic height preserves a fixed fraction of the
Vinogradov–Korobov saving. The completed energy consequently occupies an
exponentially decreasing fraction of the uncompleted transition energy.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.Sieve
open GaloisForLFunctions.RHTower GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
namespace GaloisForLFunctions.ArithmeticCompensationTheory

private theorem polarNormalizedError_vk :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ h : ℝ in atTop,
      |criticalMellinPolarNormalizedError h| ≤
        B * Real.exp (-(vkKappa * vkScale (Real.exp h) / 24)) := by
  obtain ⟨B, hB, hpnt⟩ := exists_abs_sum_vonMangoldt_sub_self_vk_rate
  refine ⟨B, hB, ?_⟩
  filter_upwards [Real.tendsto_exp_atTop.eventually hpnt] with h hh
  have hP : |Chebyshev.psi (Real.exp h) - Real.exp h| ≤
      B * Real.exp h * Real.exp (-(vkKappa * vkScale (Real.exp h) / 24)) := by
    simpa only [Chebyshev.psi_eq_sum_range] using hh
  have he : Real.exp (-h / 2) / Real.sqrt (Real.exp h) = Real.exp (-h) := by
    rw [← Real.exp_half, ← Real.exp_sub]
    congr 1
    ring
  rw [criticalMellinPolarNormalizedError, criticalMellinNormalizedChebyshevError,
    criticalMellinError, criticalCumulative_vonMangoldt_eq_psi,
    abs_mul, abs_of_pos (Real.exp_pos _), abs_div,
    abs_of_pos (Real.sqrt_pos.mpr (Real.exp_pos _))]
  calc Real.exp (-h / 2) *
        (|Chebyshev.psi (Real.exp h) - Real.exp h| / Real.sqrt (Real.exp h))
      = Real.exp (-h) * |Chebyshev.psi (Real.exp h) - Real.exp h| := by
        rw [← he]
        ring
    _ ≤ Real.exp (-h) *
        (B * Real.exp h * Real.exp (-(vkKappa * vkScale (Real.exp h) / 24))) :=
      mul_le_mul_of_nonneg_left hP (Real.exp_pos _).le
    _ = B * Real.exp (-(vkKappa * vkScale (Real.exp h) / 24)) := by
      rw [show Real.exp (-h) * (B * Real.exp h *
          Real.exp (-(vkKappa * vkScale (Real.exp h) / 24))) =
          B * (Real.exp (-h) * Real.exp h) *
            Real.exp (-(vkKappa * vkScale (Real.exp h) / 24)) by ring,
        ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

private theorem eventually_vk_saving_le_half :
    ∀ᶠ h : ℝ in atTop, vkKappa * vkScale (Real.exp h) / 54 ≤ h / 2 := by
  filter_upwards [Real.tendsto_exp_atTop.eventually (eventually_vk_conditions one_pos 0)]
    with h hh
  have hhi := hh.2.2.2.2.2.1
  have hlo := hh.2.1
  rw [log_vkHeight, Real.log_exp] at hhi
  rw [Real.log_exp] at hlo
  linarith only [hhi, hlo]

/-- The actual causal Chebyshev resolvent retains the VK saving at every sufficiently
large real logarithmic aperture. -/
theorem exists_abs_criticalResolvent_le_vinogradovKorobov :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ h : ℝ in atTop,
      |criticalMellinChebyshevResolventSource h| ≤
        C * Real.exp (h / 2 - vkKappa * vkScale (Real.exp h) / 54) := by
  obtain ⟨B, hB, hrate⟩ := polarNormalizedError_vk
  obtain ⟨H, hH⟩ := eventually_atTop.mp hrate
  obtain ⟨M, hM, hglobal⟩ := exists_global_bound_criticalMellinPolarNormalizedError
  refine ⟨2 * (B + M + 1), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 * H), eventually_ge_atTop (4 : ℝ),
    eventually_vk_saving_le_half] with h hhH hh4 hsave
  let S := vkKappa * vkScale (Real.exp h) / 54
  let f : ℝ → ℝ := fun t => Real.exp (-3 * t / 2) * criticalMellinPolarNormalizedError (h-t)
  let g : ℝ → ℝ := fun t => (B + M + 1) * Real.exp (-S) * Real.exp (-(1/2 : ℝ) * t)
  have hpoint : ∀ t ∈ Ioi (0 : ℝ), |f t| ≤ g t := by
    intro t ht
    change 0 < t at ht
    dsimp only [f, g]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    rcases le_or_gt t (h/2) with hnear | hfar
    · have hcomp : 4/9 * vkScale (Real.exp h) ≤ vkScale (Real.exp (h-t)) :=
        four_ninths_mul_vkScale_le
          (by rw [Real.log_exp]; linarith only [hh4, hnear])
          (by rw [Real.log_exp, Real.log_exp]; linarith only [hh4, hnear])
          (by rw [Real.log_exp, Real.log_exp]; linarith only [ht])
      have hlocal := hH (h-t) (by linarith only [hhH, hnear])
      have hE : Real.exp (-(vkKappa * vkScale (Real.exp (h-t)) / 24)) ≤ Real.exp (-S) := by
        apply Real.exp_le_exp.mpr
        dsimp only [S]
        have hm := mul_le_mul_of_nonneg_left hcomp vkKappa_pos.le
        linarith only [hm]
      have hk : Real.exp (-3*t/2) ≤ Real.exp (-(1/2 : ℝ)*t) :=
        Real.exp_le_exp.mpr (by linarith only [ht])
      calc Real.exp (-3*t/2) * |criticalMellinPolarNormalizedError (h-t)|
          ≤ Real.exp (-3*t/2) * (B * Real.exp (-S)) :=
            mul_le_mul_of_nonneg_left (hlocal.trans (mul_le_mul_of_nonneg_left hE hB))
              (Real.exp_pos _).le
        _ ≤ Real.exp (-(1/2 : ℝ)*t) * (B * Real.exp (-S)) :=
            mul_le_mul_of_nonneg_right hk (by positivity)
        _ ≤ (B+M+1) * Real.exp (-S) * Real.exp (-(1/2 : ℝ)*t) := by
            nlinarith only [mul_nonneg (by linarith only [hM] : 0 ≤ M+1)
              (mul_nonneg (Real.exp_pos (-S)).le (Real.exp_pos (-(1/2 : ℝ)*t)).le)]
    · have hk : Real.exp (-3*t/2) ≤ Real.exp (-S) * Real.exp (-(1/2 : ℝ)*t) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        change S ≤ h/2 at hsave
        linarith only [hfar, hsave]
      calc Real.exp (-3*t/2) * |criticalMellinPolarNormalizedError (h-t)|
          ≤ Real.exp (-3*t/2) * M :=
            mul_le_mul_of_nonneg_left (hglobal _) (Real.exp_pos _).le
        _ ≤ (Real.exp (-S) * Real.exp (-(1/2 : ℝ)*t)) * M :=
            mul_le_mul_of_nonneg_right hk hM
        _ ≤ (B+M+1) * Real.exp (-S) * Real.exp (-(1/2 : ℝ)*t) := by
            nlinarith only [mul_nonneg (by linarith only [hB] : 0 ≤ B+1)
              (mul_nonneg (Real.exp_pos (-S)).le (Real.exp_pos (-(1/2 : ℝ)*t)).le)]
  have hg : IntegrableOn g (Ioi (0 : ℝ)) :=
    (integrableOn_exp_mul_Ioi (by norm_num : -(1/2 : ℝ) < 0) 0).const_mul
      ((B+M+1) * Real.exp (-S))
  have hi : |∫ t in Ioi (0 : ℝ), f t| ≤ 2 * (B+M+1) * Real.exp (-S) := by
    have hbound := norm_integral_le_of_norm_le hg
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => by
        rw [Real.norm_eq_abs]
        exact hpoint t ht))
    rw [Real.norm_eq_abs] at hbound
    refine hbound.trans_eq ?_
    dsimp only [g]
    rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : -(1/2 : ℝ) < 0) 0]
    norm_num
    ring
  have hres : Real.exp (-h/2) * |criticalMellinChebyshevResolventSource h| ≤
      2 * (B+M+1) * Real.exp (-S) := by
    rw [← abs_of_pos (Real.exp_pos (-h/2)), ← abs_mul,
      exp_neg_half_mul_criticalMellinChebyshevResolventSource_eq]
    exact hi
  have hm := mul_le_mul_of_nonneg_left hres (Real.exp_pos (h/2)).le
  have hcancel : Real.exp (h/2) * Real.exp (-h/2) = 1 := by
    rw [← Real.exp_add, show h/2 + -h/2 = 0 by ring, Real.exp_zero]
  rw [← mul_assoc, hcancel, one_mul] at hm
  refine hm.trans_eq ?_
  rw [show Real.exp (h/2) * (2*(B+M+1)*Real.exp (-S)) =
      2*(B+M+1)*(Real.exp (h/2)*Real.exp (-S)) by ring,
    ← Real.exp_add]
  rfl

/-- The literal completed Suzuki Abel source has a VK saving against its square-root
scale, including both polar and archimedean corrections. -/
theorem exists_abs_suzukiCompletedAbelSource_le_vinogradovKorobov :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      |suzukiTransitionCoreCompletedAbelSource N| ≤
        C * Real.sqrt (N : ℝ) * Real.exp (-(vkKappa * vkScale N / 54)) := by
  obtain ⟨C, hC, hres⟩ := exists_abs_criticalResolvent_le_vinogradovKorobov
  let D := |unitRieszSuzukiPolarUniformBound| + |unitRieszSuzukiArchUniformBound|
  have hD : 0 ≤ D := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  refine ⟨C/2+D+1, by positivity, ?_⟩
  filter_upwards [hlog.eventually hres, hlog.eventually eventually_vk_saving_le_half,
    hlog.eventually_ge_atTop unitRieszSuzukiBase, eventually_ge_atTop (2 : ℕ)]
      with N hR hsave hbase hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [Real.exp_log hN0] at hR hsave
  let E := Real.sqrt (N : ℝ) * Real.exp (-(vkKappa * vkScale N / 54))
  have hEeq : E = Real.exp (Real.log N / 2 - vkKappa * vkScale N / 54) := by
    dsimp only [E]
    rw [sqrt_eq_exp_log_div_two hN0, ← Real.exp_add]
    rfl
  have hE1 : 1 ≤ E := by rw [hEeq]; exact Real.one_le_exp (by linarith only [hsave])
  have hcharge : |unitRieszCoherentCompletedOutgoingCharge N| ≤ (C/2)*E := by
    rw [unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hN, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [← hEeq] at hR
    linarith only [hR]
  have hsource : suzukiTransitionCoreCompletedAbelSource N =
      unitRieszSuzukiGreen (Real.log N) := by
    rw [← suzukiNaturalApertureCompletedLowerHardyAmplitude_eq_completedAbelSource hN]
    simpa only [Nat.sub_add_cancel hN] using
      suzukiNaturalApertureCompletedLowerHardyAmplitude_add_two_eq_green (N-2)
  have hdiff : |suzukiTransitionCoreCompletedAbelSource N -
      unitRieszCoherentCompletedOutgoingCharge N| ≤ D := by
    rw [hsource, unitRieszSuzuki_outgoing_eq_green hN]
    have heq : unitRieszSuzukiGreen (Real.log N) -
        (unitRieszSuzukiGreen (Real.log N) + unitRieszSuzukiPolarCorrection (Real.log N) -
          unitRieszSuzukiArchCorrection (Real.log N)) =
        -unitRieszSuzukiPolarCorrection (Real.log N) + unitRieszSuzukiArchCorrection (Real.log N) := by ring
    rw [heq]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
    exact add_le_add ((abs_unitRieszSuzukiPolarCorrection_le hbase).trans (le_abs_self _))
      ((abs_unitRieszSuzukiArchCorrection_le hbase).trans (le_abs_self _))
  have htri := abs_add_le (suzukiTransitionCoreCompletedAbelSource N -
      unitRieszCoherentCompletedOutgoingCharge N) (unitRieszCoherentCompletedOutgoingCharge N)
  rw [sub_add_cancel] at htri
  rw [mul_assoc]
  change |suzukiTransitionCoreCompletedAbelSource N| ≤ (C/2+D+1)*E
  nlinarith only [htri, hdiff, hcharge, mul_le_mul_of_nonneg_left hE1 hD, hE1]

/-- After canonical compensation, the fraction of transition energy remaining is
bounded at twice the VK exponent of the completed source. -/
theorem exists_suzukiCompletedEnergy_ratio_le_vinogradovKorobov :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      0 ≤ suzukiTransitionCoreAlignedGammaCompletedEnergy N /
          suzukiNaturalApertureTransitionCoreCauchyEnergy N ∧
      suzukiTransitionCoreAlignedGammaCompletedEnergy N /
          suzukiNaturalApertureTransitionCoreCauchyEnergy N ≤
        K * Real.exp (-(vkKappa * vkScale N / 27)) := by
  obtain ⟨C, hC, hsource⟩ := exists_abs_suzukiCompletedAbelSource_le_vinogradovKorobov
  have hprime : ∀ᶠ N : ℕ in atTop,
      (1/6 : ℝ) < unitRieszCoherentPrimeOutgoingCharge N / Real.sqrt (N : ℝ) :=
    (tendsto_order.mp tendsto_unitRieszCoherentPrimeOutgoingCharge_div_sqrt_atTop_one_third).1
      (1/6) (by norm_num)
  refine ⟨36*C^2, by positivity, ?_⟩
  filter_upwards [hsource, hprime,
    eventually_suzukiAlignedEnergy_div_transitionCore_eq_completedRatio_sq,
    eventually_ge_atTop (2 : ℕ)] with N hA hP heq hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsqrt := Real.sqrt_pos.mpr hN0
  have hPlower : Real.sqrt (N : ℝ) ≤ 6 * unitRieszCoherentPrimeOutgoingCharge N := by
    have hm := (lt_div_iff₀ hsqrt).mp hP
    linarith only [hm]
  have hPpos : 0 < unitRieszCoherentPrimeOutgoingCharge N := by
    linarith only [hPlower, hsqrt]
  let E := Real.exp (-(vkKappa * vkScale N / 54))
  have hratio : |suzukiTransitionCoreCompletedAbelSource N /
      unitRieszCoherentPrimeOutgoingCharge N| ≤ 6*C*E := by
    rw [abs_div, abs_of_pos hPpos, div_le_iff₀ hPpos]
    have hm := mul_le_mul_of_nonneg_right hPlower
      (by dsimp only [E]; positivity : 0 ≤ C*E)
    change |suzukiTransitionCoreCompletedAbelSource N| ≤ C * Real.sqrt (N : ℝ) * E at hA
    nlinarith only [hm, hA]
  have hsquare : (suzukiTransitionCoreCompletedAbelSource N /
      unitRieszCoherentPrimeOutgoingCharge N)^2 ≤ (6*C*E)^2 := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hratio
    have hprod := mul_nonneg (sub_nonneg.mpr hhi)
      (show 0 ≤ 6*C*E + suzukiTransitionCoreCompletedAbelSource N /
        unitRieszCoherentPrimeOutgoingCharge N by linarith only [hlo])
    nlinarith only [hprod]
  rw [suzukiNaturalApertureCompletedLowerHardyAmplitude_eq_completedAbelSource hN] at heq
  rw [heq]
  refine ⟨sq_nonneg _, hsquare.trans_eq ?_⟩
  have hE : E^2 = Real.exp (-(vkKappa * vkScale N / 27)) := by
    dsimp only [E]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  calc (6*C*E)^2 = 36*C^2*E^2 := by ring
    _ = 36*C^2*Real.exp (-(vkKappa * vkScale N / 27)) := by rw [hE]

#print axioms exists_abs_criticalResolvent_le_vinogradovKorobov
#print axioms exists_abs_suzukiCompletedAbelSource_le_vinogradovKorobov

#print axioms exists_suzukiCompletedEnergy_ratio_le_vinogradovKorobov

end GaloisForLFunctions.ArithmeticCompensationTheory
