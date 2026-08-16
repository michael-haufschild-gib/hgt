import GaloisForLFunctions.RHTower.Sieve.InghamUniformGabrielRawCenterMomentPolylog
import GaloisForLFunctions.RHTower.Sieve.InghamDetectorLogMoment
import GaloisForLFunctions.RHTower.Sieve.ChebyshevLineContinuity
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic

open Complex MeasureTheory Set

namespace RHTower.Sieve

noncomputable section

private theorem continuous_inghamRawError_uniformCenter
    (sigma : ℝ) (X : ℕ) (hcenter1 : inghamUniformGabrielCenter sigma ≠ 1) :
    Continuous fun t : ℝ =>
      riemannZeta ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) *
        inghamMollifier X
          ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) - 1 := by
  rw [continuous_iff_continuousAt]
  intro t
  let s : ℂ := (inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
    exact hcenter1 hre
  have hpath : ContinuousAt
      (fun u : ℝ => (inghamUniformGabrielCenter sigma : ℂ) + (u : ℂ) * I) t := by
    fun_prop
  have hvalue : ContinuousAt (fun w : ℂ =>
      riemannZeta w * inghamMollifier X w - 1) s :=
    (((analyticAt_riemannZeta_of_ne_one hs1).mul
      (analyticAt_inghamMollifier X s)).sub analyticAt_const).continuousAt
  exact ContinuousAt.comp_of_eq hvalue hpath rfl

theorem analyticOnNhd_inghamClassicalDetector_uniformCenter
    (sigma : ℝ) (X : ℕ) (hcenter1 : inghamUniformGabrielCenter sigma ≠ 1) :
    AnalyticOnNhd ℝ (fun t : ℝ =>
      1 - (riemannZeta ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) *
        inghamMollifier X
          ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) - 1) ^ 2)
      univ := by
  intro t _
  let s : ℂ := (inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
    exact hcenter1 hre
  have hcomplex : AnalyticAt ℂ (fun w : ℂ =>
      1 - (riemannZeta w * inghamMollifier X w - 1) ^ 2) s :=
    analyticAt_const.sub ((((analyticAt_riemannZeta_of_ne_one hs1).mul
      (analyticAt_inghamMollifier X s)).sub analyticAt_const).pow 2)
  have hpath : AnalyticAt ℝ
      (fun u : ℝ => (inghamUniformGabrielCenter sigma : ℂ) + (u : ℂ) * I) t := by
    exact analyticAt_const.add ((Complex.ofRealCLM.analyticAt t).mul analyticAt_const)
  have hreal : AnalyticAt ℝ (fun w : ℂ =>
      1 - (riemannZeta w * inghamMollifier X w - 1) ^ 2)
      ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) := by
    simpa only [s] using hcomplex.restrictScalars
  have hcomp : AnalyticAt ℝ
      ((fun w : ℂ => 1 - (riemannZeta w * inghamMollifier X w - 1) ^ 2) ∘
        (fun u : ℝ =>
          (inghamUniformGabrielCenter sigma : ℂ) + (u : ℂ) * I)) t :=
    AnalyticAt.comp (f := fun u : ℝ =>
      (inghamUniformGabrielCenter sigma : ℂ) + (u : ℂ) * I) hreal hpath
  simpa only [Function.comp_def] using hcomp

/-- Integrated logarithm of the classical detector inherits the moving Gabriel exponent. -/
theorem exists_integral_log_norm_inghamClassicalDetector_uniformCenter_le_polylog
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X : ℕ}, 4 ≤ X →
      (∫ t in Icc (-(X : ℝ)) (X : ℝ),
        Real.log ‖1 -
          (riemannZeta ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) *
            inghamMollifier X
              ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) - 1) ^ 2‖) ≤
        C * (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
          (1 + Real.log (X : ℝ)) ^
            (2 * inghamUniformGabrielCriticalShare sigma) := by
  obtain ⟨C0, hC0, hraw⟩ :=
    exists_inghamRawError_uniformGabrielCenterMoment_le_polylog hsigma0 hsigma1
  refine ⟨2 * C0, by positivity, ?_⟩
  intro X hX
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
    exact (continuous_inghamRawError_uniformCenter
      sigma X hcenter1).norm.rpow_const
        (fun _ => Or.inr
          (inghamUniformGabrielInteriorPower_pos hsigma0 hsigma1le).le)
  have hlogInt : IntervalIntegrable (fun t => Real.log ‖detector t‖) volume
      (-(X : ℝ)) (X : ℝ) := by
    have hmer : MeromorphicOn detector (uIcc (-(X : ℝ)) (X : ℝ)) := by
      intro t _
      exact (analyticOnNhd_inghamClassicalDetector_uniformCenter
        sigma X hcenter1 t (mem_univ t)).meromorphicAt
    simpa only [detector] using hmer.intervalIntegrable_log_norm
  have hmajorInt : IntervalIntegrable (fun t => 2 * raw t) volume
      (-(X : ℝ)) (X : ℝ) :=
    (continuous_const.mul hrawCont).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on
    (by linarith : -(X : ℝ) ≤ X) hlogInt hmajorInt (fun t _ => by
      dsimp only [detector, raw]
      exact log_norm_one_sub_sq_le_two_mul_norm_rpow _
        (le_trans (by norm_num : (1 : ℝ) ≤ 4 / 3)
          (four_thirds_le_inghamUniformGabrielInteriorPower hsigma0 hsigma1le))
        (inghamUniformGabrielInteriorPower_le_two hsigma1le))
  rw [intervalIntegral.integral_of_le (by linarith : -(X : ℝ) ≤ X),
    intervalIntegral.integral_of_le (by linarith : -(X : ℝ) ≤ X),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc] at hmono
  calc
    (∫ t in Icc (-(X : ℝ)) (X : ℝ), Real.log ‖detector t‖) ≤
        ∫ t in Icc (-(X : ℝ)) (X : ℝ), 2 * raw t := hmono
    _ = 2 * (∫ t in Icc (-(X : ℝ)) (X : ℝ), raw t) := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ 2 * (C0 * (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
          (1 + Real.log (X : ℝ)) ^
            (2 * inghamUniformGabrielCriticalShare sigma)) :=
      mul_le_mul_of_nonneg_left (hraw hX) (by norm_num)
    _ = (2 * C0) * (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
          (1 + Real.log (X : ℝ)) ^
            (2 * inghamUniformGabrielCriticalShare sigma) := by ring

/-- Same moving-center detector bound on every subinterval of symmetric cutoff window. -/
theorem exists_intervalIntegral_log_norm_inghamClassicalDetector_uniformCenter_le_polylog
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X : ℕ}, 4 ≤ X →
      ∀ {T₁ T₂ : ℝ}, -(X : ℝ) ≤ T₁ → T₁ ≤ T₂ → T₂ ≤ (X : ℝ) →
        (∫ t in T₁..T₂,
          Real.log ‖1 -
            (riemannZeta ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) *
              inghamMollifier X
                ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) - 1) ^ 2‖) ≤
          C * (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
            (1 + Real.log (X : ℝ)) ^
              (2 * inghamUniformGabrielCriticalShare sigma) := by
  obtain ⟨C0, hC0, hraw⟩ :=
    exists_inghamRawError_uniformGabrielCenterMoment_le_polylog hsigma0 hsigma1
  refine ⟨2 * C0, by positivity, ?_⟩
  intro X hX T₁ T₂ hlow hT hhigh
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
    exact (continuous_inghamRawError_uniformCenter
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
    _ ≤ 2 * (C0 * (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
          (1 + Real.log (X : ℝ)) ^
            (2 * inghamUniformGabrielCriticalShare sigma)) :=
      mul_le_mul_of_nonneg_left (hraw hX) (by norm_num)
    _ = (2 * C0) * (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
          (1 + Real.log (X : ℝ)) ^
            (2 * inghamUniformGabrielCriticalShare sigma) := by ring

end

end RHTower.Sieve
