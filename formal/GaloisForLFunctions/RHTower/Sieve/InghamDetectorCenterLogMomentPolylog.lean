import GaloisForLFunctions.RHTower.Sieve.InghamGabrielCenterMomentPolylog
import GaloisForLFunctions.RHTower.Sieve.InghamDetectorLogMoment
import GaloisForLFunctions.RHTower.Sieve.ChebyshevLineContinuity
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic

open Complex MeasureTheory Set

namespace RHTower.Sieve

noncomputable section

private theorem continuous_inghamRawError_fixedGabrielCenter (X : ℕ) :
    Continuous fun t : ℝ =>
      riemannZeta ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I) *
        inghamMollifier X ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I) - 1 := by
  rw [continuous_iff_continuousAt]
  intro t
  let s : ℂ := (inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [s, inghamFixedGabrielSigma] at hre
  have hpath : ContinuousAt
      (fun u : ℝ => (inghamFixedGabrielSigma : ℂ) + (u : ℂ) * I) t := by fun_prop
  have hvalue : ContinuousAt (fun w : ℂ =>
      riemannZeta w * inghamMollifier X w - 1) s :=
    (((analyticAt_riemannZeta_of_ne_one hs1).mul
      (analyticAt_inghamMollifier X s)).sub analyticAt_const).continuousAt
  exact ContinuousAt.comp_of_eq hvalue hpath rfl

/-- The raw mollified error inherits the exact fixed-Gabriel center exponent. -/
theorem exists_inghamRawError_fixedGabrielCenterMoment_le_polylog :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X : ℕ}, 4 ≤ X →
      (∫ t in Icc (-(X : ℝ)) (X : ℝ),
        ‖riemannZeta ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I) *
          inghamMollifier X ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I) - 1‖ ^
            inghamFixedGabrielInteriorPower) ≤
        C * (X : ℝ) ^ (82571 / 118590 : ℝ) * (1 + Real.log (X : ℝ)) ^ 2 := by
  obtain ⟨C0, hC0, hcenter⟩ :=
    exists_inghamGabrielPoleClearedError_centerMoment_le_polylog
  let A : ℝ := (7 / 3 : ℝ) * Real.exp 1
  let C : ℝ := A ^ inghamFixedGabrielInteriorPower * C0
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro X hX
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  let raw : ℝ → ℝ := fun t =>
    ‖riemannZeta ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I) *
      inghamMollifier X ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I) - 1‖ ^
        inghamFixedGabrielInteriorPower
  let field : ℝ → ℝ := fun t =>
    ‖inghamGabrielPoleClearedError X 1 (X : ℝ)
      ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I)‖ ^
        inghamFixedGabrielInteriorPower
  have hrawCont : Continuous raw := by
    dsimp only [raw]
    exact continuous_inghamRawError_fixedGabrielCenter X |>.norm.rpow_const
      (fun _ => Or.inr (by rw [inghamFixedGabrielInteriorPower_eq]; norm_num))
  have hfieldCont : Continuous field := by
    dsimp only [field]
    exact (continuous_poleCleared_vertical_of_half_le X
      (z := (inghamFixedGabrielSigma : ℂ)) (by
        norm_num [inghamFixedGabrielSigma])).norm.rpow_const
          (fun _ => Or.inr (by rw [inghamFixedGabrielInteriorPower_eq]; norm_num))
  have hpoint : ∀ t ∈ Icc (-(X : ℝ)) (X : ℝ),
      raw t ≤ A ^ inghamFixedGabrielInteriorPower * field t := by
    intro t ht
    have hraw := norm_inghamRawError_center_le_regularized X
      (kappa := 1) (T := (X : ℝ)) (t := t) (by norm_num) hXpos ((abs_le).2 ht)
    have hpnonneg : 0 ≤ inghamFixedGabrielInteriorPower := by
      rw [inghamFixedGabrielInteriorPower_eq]
      norm_num
    have hp := Real.rpow_le_rpow (norm_nonneg _) hraw
      hpnonneg
    rw [Real.mul_rpow (by positivity) (norm_nonneg _)] at hp
    simpa only [raw, field, A] using hp
  have hintegral :
      (∫ t in Icc (-(X : ℝ)) (X : ℝ), raw t) ≤
        A ^ inghamFixedGabrielInteriorPower *
          inghamFixedGabrielCenterMoment
            (inghamGabrielPoleClearedError X 1 (X : ℝ)) (X : ℝ) := by
    calc
      (∫ t in Icc (-(X : ℝ)) (X : ℝ), raw t) ≤
          ∫ t in Icc (-(X : ℝ)) (X : ℝ),
            A ^ inghamFixedGabrielInteriorPower * field t := by
        exact integral_mono_ae hrawCont.integrableOn_Icc
          ((continuous_const.mul hfieldCont).integrableOn_Icc)
          (ae_restrict_of_forall_mem measurableSet_Icc hpoint)
      _ = A ^ inghamFixedGabrielInteriorPower *
          inghamFixedGabrielCenterMoment
            (inghamGabrielPoleClearedError X 1 (X : ℝ)) (X : ℝ) := by
        rw [MeasureTheory.integral_const_mul, inghamFixedGabrielCenterMoment]
        dsimp only [field]
        rw [inghamFixedGabrielInteriorPower_eq]
  calc
    (∫ t in Icc (-(X : ℝ)) (X : ℝ), raw t) ≤
        A ^ inghamFixedGabrielInteriorPower *
          inghamFixedGabrielCenterMoment
            (inghamGabrielPoleClearedError X 1 (X : ℝ)) (X : ℝ) := hintegral
    _ ≤ A ^ inghamFixedGabrielInteriorPower *
          (C0 * (X : ℝ) ^ (82571 / 118590 : ℝ) * (1 + Real.log (X : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left (hcenter hX)
        (Real.rpow_nonneg hA _)
    _ = C * (X : ℝ) ^ (82571 / 118590 : ℝ) * (1 + Real.log (X : ℝ)) ^ 2 := by
      dsimp only [C]
      ring

private theorem analyticOnNhd_inghamClassicalDetector_fixedGabrielCenter (X : ℕ) :
    AnalyticOnNhd ℝ (fun t : ℝ =>
      1 - (riemannZeta ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I) *
        inghamMollifier X ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I) - 1) ^ 2)
      univ := by
  intro t _
  let s : ℂ := (inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [s, inghamFixedGabrielSigma] at hre
  have hcomplex : AnalyticAt ℂ (fun w : ℂ =>
      1 - (riemannZeta w * inghamMollifier X w - 1) ^ 2) s :=
    analyticAt_const.sub ((((analyticAt_riemannZeta_of_ne_one hs1).mul
      (analyticAt_inghamMollifier X s)).sub analyticAt_const).pow 2)
  have hpath : AnalyticAt ℝ
      (fun u : ℝ => (inghamFixedGabrielSigma : ℂ) + (u : ℂ) * I) t := by
    exact analyticAt_const.add ((Complex.ofRealCLM.analyticAt t).mul analyticAt_const)
  have hreal : AnalyticAt ℝ (fun w : ℂ =>
      1 - (riemannZeta w * inghamMollifier X w - 1) ^ 2)
      ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I) := by
    simpa only [s] using hcomplex.restrictScalars
  have hcomp : AnalyticAt ℝ
      ((fun w : ℂ => 1 - (riemannZeta w * inghamMollifier X w - 1) ^ 2) ∘
        (fun u : ℝ => (inghamFixedGabrielSigma : ℂ) + (u : ℂ) * I)) t :=
    AnalyticAt.comp (f := fun u : ℝ =>
      (inghamFixedGabrielSigma : ℂ) + (u : ℂ) * I) hreal hpath
  simpa only [Function.comp_def] using hcomp

/-- Integrated logarithm of the literal classical detector has the exact sub-`7/10` exponent. -/
theorem exists_integral_log_norm_inghamClassicalDetector_fixedGabrielCenter_le_polylog :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X : ℕ}, 4 ≤ X →
      (∫ t in Icc (-(X : ℝ)) (X : ℝ),
        Real.log ‖1 -
          (riemannZeta ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I) *
            inghamMollifier X ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I) - 1) ^ 2‖) ≤
        C * (X : ℝ) ^ (82571 / 118590 : ℝ) * (1 + Real.log (X : ℝ)) ^ 2 := by
  obtain ⟨C0, hC0, hraw⟩ := exists_inghamRawError_fixedGabrielCenterMoment_le_polylog
  refine ⟨2 * C0, by positivity, ?_⟩
  intro X hX
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  let raw : ℝ → ℝ := fun t =>
    ‖riemannZeta ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I) *
      inghamMollifier X ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I) - 1‖ ^
        inghamFixedGabrielInteriorPower
  let detector : ℝ → ℂ := fun t =>
    1 - (riemannZeta ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I) *
      inghamMollifier X ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I) - 1) ^ 2
  have hrawCont : Continuous raw := by
    dsimp only [raw]
    exact continuous_inghamRawError_fixedGabrielCenter X |>.norm.rpow_const
      (fun _ => Or.inr (by rw [inghamFixedGabrielInteriorPower_eq]; norm_num))
  have hlogInt : IntervalIntegrable (fun t => Real.log ‖detector t‖) volume
      (-(X : ℝ)) (X : ℝ) := by
    have hmer : MeromorphicOn detector (uIcc (-(X : ℝ)) (X : ℝ)) := by
      intro t _
      exact (analyticOnNhd_inghamClassicalDetector_fixedGabrielCenter X t
        (mem_univ t)).meromorphicAt
    simpa only [detector] using hmer.intervalIntegrable_log_norm
  have hmajorInt : IntervalIntegrable (fun t => 2 * raw t) volume
      (-(X : ℝ)) (X : ℝ) :=
    (continuous_const.mul hrawCont).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on (by linarith : -(X : ℝ) ≤ X)
    hlogInt hmajorInt (fun t _ => by
      dsimp only [detector, raw]
      exact log_norm_inghamClassicalDetector_le_fixedMoment X
        ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I))
  rw [intervalIntegral.integral_of_le (by linarith : -(X : ℝ) ≤ X),
    intervalIntegral.integral_of_le (by linarith : -(X : ℝ) ≤ X),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc] at hmono
  calc
    (∫ t in Icc (-(X : ℝ)) (X : ℝ), Real.log ‖detector t‖) ≤
        ∫ t in Icc (-(X : ℝ)) (X : ℝ), 2 * raw t := hmono
    _ = 2 * (∫ t in Icc (-(X : ℝ)) (X : ℝ), raw t) := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ 2 * (C0 * (X : ℝ) ^ (82571 / 118590 : ℝ) * (1 + Real.log (X : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left (hraw hX) (by norm_num)
    _ = (2 * C0) * (X : ℝ) ^ (82571 / 118590 : ℝ) * (1 + Real.log (X : ℝ)) ^ 2 := by ring

/-- The same classical-detector logarithmic bound holds on every subinterval of the symmetric
cutoff window.  The proof compares the logarithm with the nonnegative raw-error density before
using interval inclusion, so no false monotonicity of signed logarithmic integrals is used. -/
theorem exists_intervalIntegral_log_norm_inghamClassicalDetector_fixedGabrielCenter_le_polylog :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X : ℕ}, 4 ≤ X →
      ∀ {T₁ T₂ : ℝ}, -(X : ℝ) ≤ T₁ → T₁ ≤ T₂ → T₂ ≤ (X : ℝ) →
        (∫ t in T₁..T₂,
          Real.log ‖1 -
            (riemannZeta ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I) *
              inghamMollifier X ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I) - 1) ^ 2‖) ≤
          C * (X : ℝ) ^ (82571 / 118590 : ℝ) * (1 + Real.log (X : ℝ)) ^ 2 := by
  obtain ⟨C0, hC0, hraw⟩ := exists_inghamRawError_fixedGabrielCenterMoment_le_polylog
  refine ⟨2 * C0, by positivity, ?_⟩
  intro X hX T₁ T₂ hlow hT hhigh
  let raw : ℝ → ℝ := fun t =>
    ‖riemannZeta ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I) *
      inghamMollifier X ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I) - 1‖ ^
        inghamFixedGabrielInteriorPower
  let detector : ℝ → ℂ := fun t =>
    1 - (riemannZeta ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I) *
      inghamMollifier X ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I) - 1) ^ 2
  have hrawCont : Continuous raw := by
    dsimp only [raw]
    exact (continuous_inghamRawError_fixedGabrielCenter X).norm.rpow_const
      (fun _ => Or.inr (by rw [inghamFixedGabrielInteriorPower_eq]; norm_num))
  have hlogInt : IntervalIntegrable (fun t => Real.log ‖detector t‖) volume T₁ T₂ := by
    have hmer : MeromorphicOn detector (uIcc T₁ T₂) := by
      intro t _
      exact (analyticOnNhd_inghamClassicalDetector_fixedGabrielCenter X t
        (mem_univ t)).meromorphicAt
    exact hmer.intervalIntegrable_log_norm
  have hmajorInt : IntervalIntegrable (fun t => 2 * raw t) volume T₁ T₂ :=
    (continuous_const.mul hrawCont).intervalIntegrable _ _
  have hpoint : ∀ t ∈ Icc T₁ T₂,
      Real.log ‖detector t‖ ≤ 2 * raw t := by
    intro t _
    exact log_norm_inghamClassicalDetector_le_fixedMoment X
      ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I)
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
    _ ≤ 2 * (C0 * (X : ℝ) ^ (82571 / 118590 : ℝ) * (1 + Real.log (X : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left (hraw hX) (by norm_num)
    _ = (2 * C0) * (X : ℝ) ^ (82571 / 118590 : ℝ) * (1 + Real.log (X : ℝ)) ^ 2 := by ring

end

end RHTower.Sieve


