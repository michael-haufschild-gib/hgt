import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorCenterLogMomentPolylog
import GaloisForLFunctions.RHTower.Sieve.InghamUniformGabrielRawCenterMomentExplicit

open Complex MeasureTheory Set

namespace RHTower.Sieve

noncomputable section

/-- Uniform-constant logarithmic detector bound on every vertical subinterval. -/
theorem exists_intervalIntegral_log_norm_inghamClassicalDetector_uniformCenter_le_explicit :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {sigma : ℝ}, 7 / 10 ≤ sigma → sigma < 1 →
      ∀ {X : ℕ}, 4 ≤ X →
      ∀ {T₁ T₂ : ℝ}, -(X : ℝ) ≤ T₁ → T₁ ≤ T₂ → T₂ ≤ (X : ℝ) →
        (∫ t in T₁..T₂,
          Real.log ‖1 -
            (riemannZeta ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) *
              inghamMollifier X
                ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) - 1) ^ 2‖) ≤
          C *
            ((1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1) ^
              (2 : ℕ) *
            (1 + inghamMovingRightTranslatedExplicitConstant
              ((9 / 100 : ℝ) * (1 - sigma))) *
            (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
            (1 + Real.log (X : ℝ)) ^
              (2 * inghamUniformGabrielCriticalShare sigma) := by
  obtain ⟨C0, hC0, hraw⟩ :=
    exists_inghamRawError_uniformGabrielCenterMoment_le_explicit
  refine ⟨2 * C0, by positivity, ?_⟩
  intro sigma hsigma0 hsigma1 X hX T₁ T₂ hlow hT hhigh
  have hsigma1le : sigma ≤ 1 := hsigma1.le
  have hcenter1 : inghamUniformGabrielCenter sigma ≠ 1 := by
    unfold inghamUniformGabrielCenter
    nlinarith
  let raw : ℝ → ℝ := fun t =>
    ‖riemannZeta ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) *
      inghamMollifier X
        ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) - 1‖ ^
          inghamUniformGabrielInteriorPower sigma
  let detector : ℝ → ℂ := fun t =>
    1 - (riemannZeta ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) *
      inghamMollifier X
        ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) - 1) ^ 2
  have hrawCont : Continuous raw := by
    dsimp only [raw]
    exact (continuous_inghamRawError_uniformGabrielCenter
      sigma X hcenter1).norm.rpow_const
        (fun _ => Or.inr
          (inghamUniformGabrielInteriorPower_pos hsigma0 hsigma1le).le)
  have hlogInt : IntervalIntegrable (fun t => Real.log ‖detector t‖) volume T₁ T₂ := by
    have hmer : MeromorphicOn detector (uIcc T₁ T₂) := by
      intro t _
      exact (analyticOnNhd_inghamClassicalDetector_uniformCenter
        sigma X hcenter1 t (mem_univ t)).meromorphicAt
    exact hmer.intervalIntegrable_log_norm
  have hmajorInt : IntervalIntegrable (fun t => 2 * raw t) volume T₁ T₂ :=
    (continuous_const.mul hrawCont).intervalIntegrable _ _
  have hpoint : ∀ t ∈ Icc T₁ T₂,
      Real.log ‖detector t‖ ≤ 2 * raw t := by
    intro t _
    exact log_norm_one_sub_sq_le_two_mul_norm_rpow _
      (le_trans (by norm_num : (1 : ℝ) ≤ 4 / 3)
        (four_thirds_le_inghamUniformGabrielInteriorPower hsigma0 hsigma1le))
      (inghamUniformGabrielInteriorPower_le_two hsigma1le)
  have hlogMajor :
      (∫ t in T₁..T₂, Real.log ‖detector t‖) ≤
        ∫ t in T₁..T₂, 2 * raw t :=
    intervalIntegral.integral_mono_on hT hlogInt hmajorInt hpoint
  have hrawFullInt : IntervalIntegrable raw volume (-(X : ℝ)) (X : ℝ) :=
    hrawCont.intervalIntegrable _ _
  have hrawMono :
      (∫ t in T₁..T₂, raw t) ≤ ∫ t in (-(X : ℝ))..(X : ℝ), raw t := by
    exact intervalIntegral.integral_mono_interval hlow hT hhigh
      (Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _)
      hrawFullInt
  have hrawFullEq :
      (∫ t in (-(X : ℝ))..(X : ℝ), raw t) =
        ∫ t in Icc (-(X : ℝ)) (X : ℝ), raw t := by
    have hXX : -(X : ℝ) ≤ (X : ℝ) := neg_le_self (Nat.cast_nonneg X)
    rw [intervalIntegral.integral_of_le hXX,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  calc
    (∫ t in T₁..T₂, Real.log ‖detector t‖) ≤
        ∫ t in T₁..T₂, 2 * raw t := hlogMajor
    _ = 2 * (∫ t in T₁..T₂, raw t) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ 2 * (∫ t in (-(X : ℝ))..(X : ℝ), raw t) :=
      mul_le_mul_of_nonneg_left hrawMono (by norm_num)
    _ = 2 * (∫ t in Icc (-(X : ℝ)) (X : ℝ), raw t) := by rw [hrawFullEq]
    _ ≤ 2 *
        (C0 *
          ((1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1) ^
            (2 : ℕ) *
          (1 + inghamMovingRightTranslatedExplicitConstant
            ((9 / 100 : ℝ) * (1 - sigma))) *
          (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
          (1 + Real.log (X : ℝ)) ^
            (2 * inghamUniformGabrielCriticalShare sigma)) :=
      mul_le_mul_of_nonneg_left (hraw hsigma0 hsigma1 hX) (by norm_num)
    _ = (2 * C0) *
          ((1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1) ^
            (2 : ℕ) *
          (1 + inghamMovingRightTranslatedExplicitConstant
            ((9 / 100 : ℝ) * (1 - sigma))) *
          (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
          (1 + Real.log (X : ℝ)) ^
            (2 * inghamUniformGabrielCriticalShare sigma) := by ring

end

end RHTower.Sieve
