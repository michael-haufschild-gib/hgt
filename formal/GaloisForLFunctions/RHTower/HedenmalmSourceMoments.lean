import GaloisForLFunctions.RHTower.HedenmalmThetaKernelEnergy
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstMoment

/-!
# The source moments in quantile coordinates

The quantile change of variables turns the normalized source moments into moments of the quantile
map itself:

`∫₀¹ Q(t)^j dt = (1/M) ∫ x^j k(x) dx`.

For the even theta source the first moment vanishes, so the second moment is the source variance
that calibrates the trace invariant of the compressed inverse.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile

/-! ### Integrability of the first two moments -/

theorem integrable_mul_thetaSource :
    Integrable (fun x : ℝ => x * thetaCuspFullSource x) (volume : Measure ℝ) := by
  refine Integrable.mono'
    ((integrable_abs_mul_exp_neg_mul_abs (by norm_num : (0:ℝ) < 1)).const_mul thetaBound) ?_ ?_
  · exact (continuous_id.mul contDiff_thetaCuspFullSource.continuous).aestronglyMeasurable
  · filter_upwards with x
    have hle := abs_thetaCuspFullSource_le x
    have hpos := (thetaCuspFullSource_pos x).le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpos]
    calc |x| * thetaCuspFullSource x
        ≤ |x| * (thetaBound * Real.exp (-|x|)) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg x)
          exact le_trans (le_abs_self _) hle
      _ = thetaBound * (|x| * Real.exp (-(1 * |x|))) := by
          rw [one_mul]
          ring

/-- **The first moment of the even theta source vanishes.** -/
theorem integral_mul_thetaSource_eq_zero :
    (∫ x : ℝ, x * thetaCuspFullSource x) = 0 := by
  have hodd : ∀ x : ℝ, (-x) * thetaCuspFullSource (-x) = -(x * thetaCuspFullSource x) := by
    intro x
    rw [thetaCuspFullSource_neg]
    ring
  have h := integral_neg_eq_self (fun x : ℝ => x * thetaCuspFullSource x) (volume : Measure ℝ)
  rw [integral_congr_ae (Filter.Eventually.of_forall hodd)] at h
  rw [MeasureTheory.integral_neg] at h
  linarith [h]

/-! ### The quantile moments -/

/-- **The first quantile moment.**  `∫₀¹ Q = M⁻¹ ∫ x k(x) dx = 0`. -/
theorem integral_quantileFun :
    (∫ t in Ioo (0 : ℝ) 1, thetaSource.quantileFun t) = 0 := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x) (volume : Measure ℝ) :=
    continuous_id.aestronglyMeasurable
  have h := integral_comp_quantile thetaSource (fun x : ℝ => x) hmeas
  rw [h]
  have hpt : ∀ x : ℝ, thetaSource.normalized x • x
      = thetaSource.mass⁻¹ * (x * thetaCuspFullSource x) := by
    intro x
    show thetaSource.k x / thetaSource.mass * x = _
    show thetaCuspFullSource x / thetaSource.mass * x = _
    field_simp
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), MeasureTheory.integral_const_mul,
    integral_mul_thetaSource_eq_zero, mul_zero]

/-- **The second quantile moment is the source variance.**
`∫₀¹ Q² = M⁻¹ ∫ x² k(x) dx`, and the first moment vanishes, so this is the variance that
calibrates the trace invariant of the compressed inverse. -/
theorem integral_sq_quantileFun :
    (∫ t in Ioo (0 : ℝ) 1, thetaSource.quantileFun t ^ 2)
      = thetaSource.mass⁻¹ * ∫ x : ℝ, x ^ 2 * thetaCuspFullSource x := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ 2) (volume : Measure ℝ) :=
    (continuous_pow 2).aestronglyMeasurable
  have h := integral_comp_quantile thetaSource (fun x : ℝ => x ^ 2) hmeas
  rw [h]
  have hpt : ∀ x : ℝ, thetaSource.normalized x • x ^ 2
      = thetaSource.mass⁻¹ * (x ^ 2 * thetaCuspFullSource x) := by
    intro x
    show thetaSource.k x / thetaSource.mass * x ^ 2 = _
    show thetaCuspFullSource x / thetaSource.mass * x ^ 2 = _
    field_simp
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), MeasureTheory.integral_const_mul]

end HedenmalmThetaSource

end

end RHTower
