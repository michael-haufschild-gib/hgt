import GaloisForLFunctions.RHTower.CCMThetaContinuousLocalizationMoment

/-!
# A proved IMS bound for the complete arithmetic source form

The prime second moment is the actual finite von Mangoldt sum allowed by
the source aperture. Combining it with the continuous moment gives a
localization bound for every complex smooth source and every Schwartz angle.
No positivity premise or assumed second-moment estimate enters the result.
The exact signed formula remains available when absolute bounds lose too much.
-/

noncomputable section

open MeasureTheory Filter
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard

def ccmThetaPrimeMomentDensity (a : SuzukiPositiveAperture) (n : ℕ) : ℝ :=
  if n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))) then
    ArithmeticFunction.vonMangoldt n / Real.sqrt n * Real.log n ^ 2 else 0

def ccmThetaPrimeLocalizationMoment (a : SuzukiPositiveAperture) : ℝ :=
  ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
    ArithmeticFunction.vonMangoldt n / Real.sqrt n * Real.log n ^ 2

theorem ccmThetaPrimeMomentDensity_nonneg (a : SuzukiPositiveAperture) (n : ℕ) :
    0 ≤ ccmThetaPrimeMomentDensity a n := by
  have hn := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  unfold ccmThetaPrimeMomentDensity
  split <;> positivity

theorem integrable_ccmThetaPrimeMomentDensity (a : SuzukiPositiveAperture) :
    Integrable (ccmThetaPrimeMomentDensity a) Measure.count := by
  rw [integrable_count_iff]
  apply summable_of_ne_finset_zero (s := Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))))
  intro n hn
  simp only [ccmThetaPrimeMomentDensity, if_neg hn, norm_zero]

theorem integral_ccmThetaPrimeMomentDensity (a : SuzukiPositiveAperture) :
    (∫ n, ccmThetaPrimeMomentDensity a n ∂Measure.count) =
      ccmThetaPrimeLocalizationMoment a := by
  rw [integral_countable (integrable_ccmThetaPrimeMomentDensity a)]
  simp only [count_real_singleton, one_smul]
  rw [tsum_eq_sum (s := Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))))
    (fun n hn => by simp only [ccmThetaPrimeMomentDensity, if_neg hn])]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [ccmThetaPrimeMomentDensity, if_pos hn]

theorem ccmThetaPrimeLocalizationMoment_nonneg (a : SuzukiPositiveAperture) :
    0 ≤ ccmThetaPrimeLocalizationMoment a := by
  rw [← integral_ccmThetaPrimeMomentDensity]
  exact integral_nonneg (ccmThetaPrimeMomentDensity_nonneg a)

theorem ccmThetaPrimeLocalizationDensity_eq_zero_outside {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : ℝ → ℝ) (n : ℕ) (x : ℝ)
    (hn : n ∉ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1)))) :
    ccmThetaPrimeLocalizationDensity u theta (n, x) = 0 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [ccmThetaPrimeLocalizationDensity]
  rcases eq_or_ne n 1 with rfl | hn1
  · simp [ccmThetaPrimeLocalizationDensity]
  have hn2 : 2 ≤ n := by omega
  have hfloor : Nat.floor (Real.exp (2 * a.1)) < n := by
    simpa only [Finset.mem_Icc, hn2, true_and, not_le] using hn
  have hexp : Real.exp (2 * a.1) < (n : ℝ) :=
    (Nat.floor_lt (Real.exp_pos _).le).mp hfloor
  have hlog : 2 * a.1 < Real.log n :=
    (Real.lt_log_iff_exp_lt (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0))).mpr hexp
  rw [ccmThetaPrimeLocalizationDensity,
    ccmThetaLocalizationCross_eq_zero_of_aperture_le u theta x (Real.log n)
      (hlog.le.trans (le_abs_self _)), mul_zero]

theorem integral_norm_ccmThetaPrimeLocalizationDensity_le
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a)
    (theta : 𝓢(ℝ, ℝ)) (n : ℕ) :
    (∫ x : ℝ, ‖ccmThetaPrimeLocalizationDensity u theta (n, x)‖) ≤
      SchwartzMap.seminorm ℝ 0 1 theta ^ 2 * ccmThetaPrimeMomentDensity a n *
        ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 := by
  by_cases hn : n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1)))
  · have hc : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n :=
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    simp only [ccmThetaPrimeLocalizationDensity, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg hc, integral_const_mul, ccmThetaPrimeMomentDensity, if_pos hn]
    have hb := mul_le_mul_of_nonneg_left
      (integral_abs_ccmThetaLocalizationCross_shift_le u theta (Real.log n)) hc
    convert! hb using 1; ring
  · simp only [ccmThetaPrimeLocalizationDensity_eq_zero_outside u theta n _ hn,
      norm_zero, integral_zero, ccmThetaPrimeMomentDensity, if_neg hn, mul_zero,
      zero_mul, le_refl]

/-- The prime error is bounded by the literal finite prime second moment. -/
theorem abs_ccmThetaPrimeLocalizationError_le {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) :
    |ccmThetaPrimeLocalizationError u theta| ≤
      SchwartzMap.seminorm ℝ 0 1 theta ^ 2 * ccmThetaPrimeLocalizationMoment a *
        ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 := by
  have hi := integrable_ccmThetaPrimeLocalizationDensity u theta
  have hm := ((integrable_ccmThetaPrimeMomentDensity a).const_mul
    (SchwartzMap.seminorm ℝ 0 1 theta ^ 2)).mul_const
      (‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2)
  have hb := integral_mono hi.integral_norm_prod_left hm
    (integral_norm_ccmThetaPrimeLocalizationDensity_le u theta)
  rw [integral_mul_const, integral_const_mul, integral_ccmThetaPrimeMomentDensity] at hb
  calc
    _ ≤ ∫ p, ‖ccmThetaPrimeLocalizationDensity u theta p‖ ∂thetaPrimeLinkMeasure :=
      norm_integral_le_integral_norm _
    _ = ∫ n, (∫ x : ℝ, ‖ccmThetaPrimeLocalizationDensity u theta (n, x)‖) ∂Measure.count :=
      integral_prod _ hi.norm
    _ ≤ _ := hb

/-- An unconditional IMS lower bound for the full actual arithmetic form. -/
theorem ccmRestrictedWeilSourceQuadratic_localization_lower_bound
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a)
    (theta : 𝓢(ℝ, ℝ)) :
    ccmRestrictedWeilSourceQuadratic a (ccmCosLocalizedSource u theta).toCCMFormVector +
      ccmRestrictedWeilSourceQuadratic a (ccmSinLocalizedSource u theta).toCCMFormVector -
      SchwartzMap.seminorm ℝ 0 1 theta ^ 2 *
        (ccmThetaPrimeLocalizationMoment a + ccmThetaContinuousLocalizationMoment a) *
          ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector := by
  rw [ccmRestrictedWeilSourceQuadratic_localization u theta]
  have hp := abs_ccmThetaPrimeLocalizationError_le u theta
  have hc := abs_ccmThetaContinuousLocalizationError_le u theta
  nlinarith [le_abs_self (ccmThetaPrimeLocalizationError u theta),
    neg_abs_le (ccmThetaContinuousLocalizationError u theta)]

end RHTower
