import GaloisForLFunctions.RHTower.ZetaChiCriticalLineOscillatoryIntegral

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- Abel summation for a complex differentiable amplitude against a bounded anchored primitive. -/
theorem norm_integral_complexAmplitude_mul_deriv_le
    {a b B : ℝ} (hab : a ≤ b)
    {u u' v v' : ℝ → ℂ}
    (hu : ∀ x ∈ Set.uIcc a b, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ Set.uIcc a b, HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b)
    (hv' : IntervalIntegrable v' volume a b)
    (hva : v a = 0)
    (hvB : ∀ x ∈ Set.Icc a b, ‖v x‖ ≤ B) :
    ‖∫ x in a..b, u x * v' x‖ ≤
      B * (‖u b‖ + ∫ x in a..b, ‖u' x‖) := by
  have hvc : ContinuousOn v (Set.uIcc a b) :=
    fun x hx => (hv x hx).continuousAt.continuousWithinAt
  have hprodInt : IntervalIntegrable (fun x => u' x * v x) volume a b :=
    hu'.mul_continuousOn hvc
  have hprodNormInt : IntervalIntegrable (fun x => ‖u' x * v x‖) volume a b :=
    hprodInt.norm
  have hrightInt : IntervalIntegrable (fun x => ‖u' x‖ * B) volume a b :=
    hu'.norm.mul_const B
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  rw [hva, mul_zero, sub_zero] at hibp
  rw [hibp]
  calc
    ‖u b * v b - ∫ x in a..b, u' x * v x‖
        ≤ ‖u b * v b‖ + ‖∫ x in a..b, u' x * v x‖ := norm_sub_le _ _
    _ ≤ ‖u b‖ * B + ∫ x in a..b, ‖u' x * v x‖ := by
      gcongr
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hvB b ⟨hab, le_rfl⟩) (norm_nonneg _)
      · exact intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ‖u b‖ * B + ∫ x in a..b, ‖u' x‖ * B := by
      gcongr
      exact intervalIntegral.integral_mono_on hab hprodNormInt hrightInt
        (fun x hx => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hvB x hx) (norm_nonneg _))
    _ = B * (‖u b‖ + ∫ x in a..b, ‖u' x‖) := by
      rw [intervalIntegral.integral_mul_const]
      ring

/-- Stationary critical-line chi cancellation survives any complex amplitude with integrable
derivative, at the cost of its endpoint norm and derivative variation. -/
theorem norm_integral_complexAmplitude_mul_zetaChi_line_mul_exp_le
    {T : ℝ} (hT : 4 ≤ T) (ω : ℝ) {u u' : ℝ → ℂ}
    (hu : ∀ x ∈ Set.uIcc T (2 * T), HasDerivAt u (u' x) x)
    (hu' : IntervalIntegrable u' volume T (2 * T)) :
    ‖∫ x in T..(2 * T),
        u x * (zetaChi (linePt x) *
          Complex.exp (((ω * x : ℝ) : ℂ) * I))‖ ≤
      (6 / Real.sqrt (1 / (100 * T))) *
        (‖u (2 * T)‖ + ∫ x in T..(2 * T), ‖u' x‖) := by
  have hab : T ≤ 2 * T := by linarith
  let f : ℝ → ℂ := fun x =>
    zetaChi (linePt x) * Complex.exp (((ω * x : ℝ) : ℂ) * I)
  let F : ℝ → ℂ := zetaChiCriticalTwistPrimitive T ω
  have hf : Continuous f := continuous_zetaChiCriticalTwistIntegrand ω
  apply norm_integral_complexAmplitude_mul_deriv_le hab hu
      (u' := u') (v := F) (v' := f)
  · intro x hx
    exact hasDerivAt_zetaChiCriticalTwistPrimitive T ω x
  · exact hu'
  · exact hf.intervalIntegrable T (2 * T)
  · exact zetaChiCriticalTwistPrimitive_left T ω
  · intro x hx
    exact norm_zetaChiCriticalTwistPrimitive_le hT hx ω

end

end RHTower
