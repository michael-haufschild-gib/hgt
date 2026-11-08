import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.PolarPaymentInPhysicalCoordinates
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalPositivityThresholdLaw

/-!
# Polar payment excludes nonzero charged limit profiles

One-sided mollification preserves the finite Gamma upper bound and converges in
the exponential source norm. Payment at a strictly larger ratio then leaves a
positive reserve in the eighth mass and in the scalar pole coordinate.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory SpacingScaleHarmonicAnalysis
  WindowTowerOfSpecZ ArithmeticCastelnuovoSeveri RenormalizedArithmeticPotentialTheory
  ArithmeticPositivityTheory ArithmeticDegenerationTheory

/-- A nonzero charged physical profile satisfying the critical Gamma upper bound cannot coexist
with polar payment at every window of a strictly larger ratio. -/
theorem no_charged_limit_profile_below_polarPayment
    {R S β : ℝ} (hR : 0 < R) (hRS : R < S)
    (hpay : ∀ A : ℝ, 0 ≤ A → PolarPaymentAt S A)
    {F : ℝ → ℝ} (hFm : Measurable F) (hFi : Integrable F)
    (hF2 : Integrable fun u => F u ^ 2) (hFmass : (∫ u, F u ^ 2) ≤ 1)
    (hF8 : Integrable fun u => F u ^ 2 * Real.exp (-(8 * u)))
    (hFzero : ∀ u, 0 ≤ u → F u = 0)
    (hnonzero : 0 < (∫ u, F u ^ 2) + β ^ 2)
    (hliminf : ∀ T : ℝ, Real.exp factorialSpanGammaOffset ≤ T →
      truncatedWeilForm F T + criticalAliasCoefficient R *
        (∫ u in Iio 0, F u ^ 2 * Real.exp (-(8 * u))) +
      (∫ u, tiltedUnitSpline u ^ 2) * criticalPoleWindowCost R * β ^ 2 +
      2 * (∫ u, tiltedUnitSpline u) * β * (∫ u, F u * polarSourceProfile u) ≤ 0) : False := by
  have hS := hR.trans hRS
  let I₁ := ∫ u, tiltedUnitSpline u
  let I₂ := ∫ u, tiltedUnitSpline u ^ 2
  have hI₂ : 0 < I₂ := integral_tiltedUnitSpline_sq_pos
  let M := ∫ u, F u ^ 2 * Real.exp (-(8 * u))
  let I₈ := ∫ u in Iio 0, F u ^ 2 * Real.exp (-(8 * u))
  let B := -(I₂ * criticalPoleWindowCost R * β ^ 2) -
    2 * I₁ * β * (∫ u, F u * polarSourceProfile u)
  have hbound : ∀ T : ℝ, Real.exp factorialSpanGammaOffset ≤ T →
      truncatedWeilForm F T + criticalAliasCoefficient R * I₈ ≤ B := by
    intro T hT
    have hh := hliminf T hT
    dsimp only [B, I₁, I₂, I₈]
    linarith only [hh]
  obtain ⟨C, A, H, hC, hwin, hmass, hweighted, hL2, hweightedLim, harch⟩ :=
    exists_window_sequence_of_gammaLiminf_bound (Rstar := R) (B := B) hFm hFi hF2 hF8 (le_rfl : M ≤ M) hFzero hbound
  have hHd : ∀ k, ContDiff ℝ 2 (H k) := fun k => (hwin k).2.contDiff
  have hHc : ∀ k, HasCompactSupport (H k) := fun k => (hwin k).2.hasCompactSupport
  have hHs : ∀ k u, 1 < u → H k u = 0 := fun k u hu =>
    (hwin k).2.vanish u (fun hm => by linarith only [hu, hm.2])
  have hFW : WeightedTwo F := (exponentialSourceMass_le_of_support zero_le_one
    hFm.aestronglyMeasurable hF2 hF8
    (Eventually.of_forall fun u hu => hFzero u (zero_lt_one.trans hu).le)).1
  have hHW : ∀ k, WeightedTwo (H k) := fun k =>
    (weightedTwo_of_support (hHd k).continuous (hHc k) (hHs k)).1
  have hM0 : 0 ≤ M := integral_nonneg (fun _ => by positivity)
  have hI₈0 : 0 ≤ I₈ := setIntegral_nonneg measurableSet_Iio (fun _ _ => by positivity)
  have hI₈M : I₈ ≤ M := setIntegral_le_integral hF8
    (Eventually.of_forall fun _ => by positivity)
  have hHmass : ∀ k, (∫ u, H k u ^ 2) ≤ 1 := fun k => (hmass k).trans hFmass
  have hH8 : ∀ k, (∫ u, H k u ^ 2 * Real.exp (-(8 * u))) ≤ Real.exp 8 * M := by
    intro k
    have hδ : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 :=
      div_le_one_of_le₀ (by linarith only [Nat.cast_nonneg (α := ℝ) k]) (by positivity)
    have he : Real.exp (8 / ((k : ℝ) + 1)) ≤ Real.exp 8 :=
      Real.exp_le_exp.mpr (by
        simpa only [mul_one_div, mul_one] using
          mul_le_mul_of_nonneg_left hδ (by norm_num : (0 : ℝ) ≤ 8))
    have hh := (hweighted k).trans (mul_le_mul he hI₈M hI₈0 (Real.exp_pos _).le)
    simpa only [exponentialMass, mul_comm] using hh
  obtain ⟨hprime, hcosh, hsinh⟩ := tendsto_prime_and_pole_of_strong_limit
    (fun k => (hHd k).continuous) hHc hFW hHmass hH8 (Eventually.of_forall hHs) hweightedLim
  have hsource := tendsto_integral_mul_polarSourceProfile hHW hFW hweightedLim
  have hmass8 : (∫ u, F u ^ 2) ≤ I₈ := by
    have heq : (∫ u, F u ^ 2) = ∫ u in Iio 0, F u ^ 2 := by
      rw [← integral_indicator measurableSet_Iio]
      apply integral_congr_ae
      exact Eventually.of_forall fun u => by
        by_cases hu : u < 0
        · rw [Set.indicator_of_mem (show u ∈ Iio (0 : ℝ) from hu)]
        · rw [Set.indicator_of_notMem (show u ∉ Iio (0 : ℝ) from hu)]
          simp only [hFzero u (not_lt.mp hu), zero_pow (by decide : 2 ≠ 0)]
    rw [heq]
    exact setIntegral_mono_on hF2.integrableOn hF8.integrableOn measurableSet_Iio fun u hu =>
      le_mul_of_one_le_right (sq_nonneg _) (Real.one_le_exp (by have hu0 : u < 0 := hu; linarith only [hu0]))
  have hAlias : criticalAliasCoefficient S < criticalAliasCoefficient R := by
    unfold criticalAliasCoefficient
    have hnum : 0 < 7 * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne := by
      have := tiltedJordanOne_pos
      positivity
    have hI₁sq : 0 < (∫ u, tiltedUnitSpline u) ^ 2 :=
      sq_pos_of_ne_zero integral_tiltedUnitSpline_ne_zero
    exact div_lt_div_of_pos_left hnum (mul_pos hI₁sq hR)
      (mul_lt_mul_of_pos_left hRS hI₁sq)
  have hcost : criticalPoleWindowCost S < criticalPoleWindowCost R := by
    have he := criticalPoleWindowCost_sub_eq hR.ne' hS.ne'
    have hinv : 1 / S < 1 / R := one_div_lt_one_div_of_lt hR hRS
    have hj := jordanCoefficient_pos (by norm_num : (0 : ℕ) < 1)
    have hp := mul_pos hj (sub_pos.mpr hinv)
    linarith only [he, hp]
  let gap := (criticalAliasCoefficient R - criticalAliasCoefficient S) * I₈ +
    I₂ * (criticalPoleWindowCost R - criticalPoleWindowCost S) * β ^ 2
  have hgap : 0 < gap := by
    have ha := sub_pos.mpr hAlias
    have hb := mul_pos hI₂ (sub_pos.mpr hcost)
    have hsum : 0 < I₈ + β ^ 2 := lt_of_lt_of_le hnonzero (add_le_add hmass8 le_rfl)
    dsimp only [gap]
    rcases lt_or_eq_of_le hI₈0 with hi | hi
    · exact add_pos_of_pos_of_nonneg (mul_pos ha hi) (mul_nonneg hb.le (sq_nonneg _))
    · rw [← hi, mul_zero, zero_add]
      exact mul_pos hb (by linarith only [hsum, hi])
  let upper : ℕ → ℝ := fun k =>
    primeSum F - (2 * coshHalfMoment F ^ 2 - 2 * sinhHalfMoment F ^ 2) -
      criticalAliasCoefficient R * I₈ + C / ((k : ℝ) + 1) + B - primeSum (H k) +
      (2 * coshHalfMoment (H k) ^ 2 - 2 * sinhHalfMoment (H k) ^ 2) +
      criticalAliasCoefficient S * (Real.exp (8 / ((k : ℝ) + 1)) * I₈) +
      I₂ * criticalPoleWindowCost S * β ^ 2 +
      2 * I₁ * β * (∫ u, H k u * polarSourceProfile u)
  have hupper : Tendsto upper atTop (𝓝 (-gap)) := by
    have hinv : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hCzero : Tendsto (fun k : ℕ => C / ((k : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [mul_zero, mul_one_div] using hinv.const_mul C
    have h8zero : Tendsto (fun k : ℕ => 8 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [mul_zero, mul_one_div] using hinv.const_mul 8
    have he := Real.continuous_exp.continuousAt.tendsto.comp h8zero
    rw [Real.exp_zero] at he
    have hconst := tendsto_const_nhds (f := (atTop : Filter ℕ))
      (x := primeSum F - (2 * coshHalfMoment F ^ 2 - 2 * sinhHalfMoment F ^ 2) -
        criticalAliasCoefficient R * I₈)
    have hh := ((((((hconst.add hCzero).add_const B).sub hprime).add
      (((hcosh.pow 2).const_mul 2).sub ((hsinh.pow 2).const_mul 2))).add
        ((he.mul_const I₈).const_mul (criticalAliasCoefficient S))).add_const
          (I₂ * criticalPoleWindowCost S * β ^ 2)).add (hsource.const_mul (2 * I₁ * β))
    convert hh using 1
    · rfl
    · dsimp only [B, gap]
      congr 1
      ring
  obtain ⟨k, hk⟩ := (hupper.eventually (gt_mem_nhds (neg_lt_zero.mpr hgap))).exists
  have hnonneg := physical_charged_window_nonneg_of_polarPaymentAt hS (hwin k).1
    (hpay (A k) (hwin k).1) (hHd k) (hwin k).2.vanish β
  have hAle : 0 ≤ criticalAliasCoefficient S := by
    unfold criticalAliasCoefficient
    have := tiltedJordanOne_pos
    have := integral_tiltedUnitSpline_sq_pos
    positivity
  have henergy : weilQuad (H k) + criticalAliasCoefficient S * exponentialMass 8 (H k) +
      I₂ * criticalPoleWindowCost S * β ^ 2 +
      2 * I₁ * β * (∫ u, H k u * polarSourceProfile u) ≤ upper k := by
    rw [weilQuad_eq_arch_sub_prime_add_pole (hHd k) (hHc k)]
    have hm := mul_le_mul_of_nonneg_left (hweighted k) hAle
    have ha := harch k
    dsimp only [upper]
    linarith only [ha, hm]
  exact (not_lt_of_ge (hnonneg.trans henergy)) hk

#print axioms no_charged_limit_profile_below_polarPayment
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
