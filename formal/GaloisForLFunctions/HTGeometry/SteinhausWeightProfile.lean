import GaloisForLFunctions.HTGeometry.SteinhausLaplaceProduct

/-!
# The limiting weight profile and the regular-variation cumulant

The normalized weights of the regular-variation Steinhaus model converge to the profile
`w_α(v) = (1−α)v^{−α}` on `(0,1]`, whose integral is `1`.  The limiting cumulant is the mixture
`Λ_α(λ) = ∫₀¹ log I₀(λ w_α(v)) dv`, finite for every `λ` because the one-circle cumulant is
squeezed between `0` and `|·|`.
-/

open MeasureTheory Set

namespace HTGeometry

noncomputable section

/-- The limiting weight profile. -/
def weightProfile (α v : ℝ) : ℝ := (1 - α) * v ^ (-α)

theorem weightProfile_nonneg {α : ℝ} (hα : α < 1) {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ weightProfile α v := by
  rw [weightProfile]
  have h1 : (0 : ℝ) < 1 - α := by linarith
  have h2 : (0 : ℝ) ≤ v ^ (-α) := Real.rpow_nonneg hv _
  positivity

theorem intervalIntegrable_rpow_neg {α : ℝ} (hα : α < 1) :
    IntervalIntegrable (fun v : ℝ => v ^ (-α)) volume 0 1 := by
  refine intervalIntegral.intervalIntegrable_rpow' ?_
  linarith

theorem intervalIntegrable_weightProfile {α : ℝ} (hα : α < 1) :
    IntervalIntegrable (weightProfile α) volume 0 1 := by
  have h := (intervalIntegrable_rpow_neg hα).const_mul (1 - α)
  exact h

/-- **The profile is a probability density.** -/
theorem integral_weightProfile {α : ℝ} (hα : α < 1) :
    (∫ v in (0 : ℝ)..1, weightProfile α v) = 1 := by
  have hne : (1 : ℝ) - α ≠ 0 := by linarith
  have hbase : (∫ v in (0 : ℝ)..1, v ^ (-α)) = 1 / (1 - α) := by
    rw [integral_rpow (Or.inl (by linarith))]
    have hexp : -α + 1 = 1 - α := by ring
    rw [hexp, Real.one_rpow, Real.zero_rpow (by linarith)]
    ring
  have hsimp : (∫ v in (0 : ℝ)..1, weightProfile α v)
      = (1 - α) * ∫ v in (0 : ℝ)..1, v ^ (-α) := by
    simp only [weightProfile]
    exact intervalIntegral.integral_const_mul _ _
  rw [hsimp, hbase]
  field_simp

/-- The regular-variation cumulant. -/
def rvCumulant (α lam : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..1, steinhausLogLaplace (lam * weightProfile α v)

theorem continuous_steinhausLogLaplace : Continuous steinhausLogLaplace :=
  continuousOn_univ.mp analyticOnNhd_steinhausLogLaplace.continuousOn

theorem intervalIntegrable_rvCumulant_integrand {α : ℝ} (hα : α < 1) (lam : ℝ) :
    IntervalIntegrable (fun v : ℝ => steinhausLogLaplace (lam * weightProfile α v))
      volume 0 1 := by
  have hwm : Measurable (weightProfile α) := by
    have hfun : (weightProfile α) = fun v : ℝ => (1 - α) * v ^ (-α) := rfl
    rw [hfun]
    exact measurable_const.mul (measurable_id.pow_const (-α))
  have hmeas : Measurable fun v : ℝ => steinhausLogLaplace (lam * weightProfile α v) :=
    continuous_steinhausLogLaplace.measurable.comp (measurable_const.mul hwm)
  have hdom : IntervalIntegrable (fun v : ℝ => |lam| * weightProfile α v) volume 0 1 :=
    (intervalIntegrable_weightProfile hα).const_mul _
  refine IntervalIntegrable.mono_fun hdom hmeas.aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with v hv
  have hv0 : (0 : ℝ) ≤ v := le_of_lt (by simpa using hv.1)
  have hw : 0 ≤ weightProfile α v := weightProfile_nonneg hα hv0
  have hbound := abs_steinhausLogLaplace_le (lam * weightProfile α v)
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ |lam| * weightProfile α v)]
  refine hbound.trans (le_of_eq ?_)
  rw [abs_mul, abs_of_nonneg hw]

/-- The cumulant vanishes at the origin. -/
@[simp] theorem rvCumulant_zero (α : ℝ) : rvCumulant α 0 = 0 := by
  rw [rvCumulant]
  simp

/-- The cumulant is nonnegative. -/
theorem rvCumulant_nonneg (α lam : ℝ) : 0 ≤ rvCumulant α lam := by
  rw [rvCumulant]
  refine intervalIntegral.integral_nonneg (by norm_num) fun v _ => ?_
  exact steinhausLogLaplace_nonneg _

/-- **The cumulant is at most the tilt.**  This is the card's `(11)`: the profile has unit mass. -/
theorem rvCumulant_le {α : ℝ} (hα : α < 1) (lam : ℝ) : rvCumulant α lam ≤ |lam| := by
  rw [rvCumulant]
  have hle : ∀ v ∈ Set.uIcc (0 : ℝ) 1,
      steinhausLogLaplace (lam * weightProfile α v) ≤ |lam| * weightProfile α v := by
    intro v hv
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Icc] at hv
    have hw : 0 ≤ weightProfile α v := weightProfile_nonneg hα hv.1
    have hbound := steinhausLogLaplace_le_abs (lam * weightProfile α v)
    rw [abs_mul, abs_of_nonneg hw] at hbound
    exact hbound
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
    (intervalIntegrable_rvCumulant_integrand hα lam)
    ((intervalIntegrable_weightProfile hα).const_mul _)
    (fun v hv => hle v (by rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hv))
  refine hmono.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul, integral_weightProfile hα, mul_one]

end

end HTGeometry
