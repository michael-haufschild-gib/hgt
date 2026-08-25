import GaloisForLFunctions.HTGeometry.PoissonJensenUpperBound
import GaloisForLFunctions.HTGeometry.PoissonInteriorLogKernel

/-!
# Shifted-circle logarithmic kernel bounds

These estimates control logarithmic divisor kernels on a circle whose center is displaced inside a
larger Nevanlinna disc.  They are the local analytic input for translating small-characteristic
meromorphic functions.
-/

open Complex Metric Real Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every logarithmic point kernel has circle mean at least the logarithm of the radius. -/
theorem log_radius_le_circleAverage_log_norm_sub (c a : ℂ) {r : ℝ} (hr : 0 < r) :
    Real.log r ≤ Real.circleAverage (fun z => Real.log ‖z - a‖) c r := by
  by_cases ha : a ∈ closedBall c r
  · rw [circleAverage_log_norm_sub_const_of_mem_closedBall
      (by simpa [abs_of_pos hr] using ha)]
  · have hfree : ∀ z ∈ closedBall c r, z - a ≠ 0 := by
      intro z hz hza
      apply ha
      have hza' : z = a := sub_eq_zero.mp hza
      simpa [hza'] using hz
    have hanalytic : AnalyticOnNhd ℂ (fun z : ℂ => z - a)
        (closedBall c |r|) := analyticOnNhd_id.sub analyticOnNhd_const
    have hfree' : ∀ z ∈ closedBall c |r|, z - a ≠ 0 := by
      simpa [abs_of_pos hr] using hfree
    have hmean := hanalytic.circleAverage_log_norm_of_ne_zero hfree'
    have hdist : r < ‖c - a‖ := by
      rw [mem_closedBall_iff_norm, not_le] at ha
      simpa [norm_sub_rev] using ha
    rw [hmean]
    exact Real.log_le_log hr hdist.le

/-- The outer-disc Blaschke majorant is zero-free on every strictly contained shifted disc. -/
theorem circleAverage_log_norm_innerLogKernel {u c : ℂ} {R r : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hu : u ∈ closedBall (0 : ℂ) R)
    (hinner : ‖c‖ + r < R) :
    Real.circleAverage
        (fun w => Real.log ‖PoissonJensen.innerLogKernel 0 u R w‖) c r =
      Real.log ‖PoissonJensen.innerLogKernel 0 u R c‖ := by
  have hanalytic : AnalyticOnNhd ℂ
      (PoissonJensen.innerLogKernel 0 u R) (closedBall c |r|) := by
    unfold PoissonJensen.innerLogKernel
    apply AnalyticOnNhd.div
    · exact analyticOnNhd_const.sub
        (analyticOnNhd_const.mul (analyticOnNhd_id.sub analyticOnNhd_const))
    · exact analyticOnNhd_const
    · intro _ _
      exact Complex.ofReal_ne_zero.mpr hR.ne'
  have hfree : ∀ w ∈ closedBall c |r|,
      PoissonJensen.innerLogKernel 0 u R w ≠ 0 := by
    intro w hw
    apply PoissonJensen.innerLogKernel_ne_zero hR
    have huR : ‖u‖ ≤ R := by
      simpa [mem_closedBall_iff_norm] using hu
    have hwc : ‖w - c‖ ≤ r := by
      rw [abs_of_pos hr] at hw
      exact mem_closedBall_iff_norm.mp hw
    have hwR : ‖w‖ < R := by
      calc
        ‖w‖ ≤ ‖w - c‖ + ‖c‖ := by
          have := norm_add_le (w - c) c
          simpa using this
        _ ≤ r + ‖c‖ := by linarith
        _ < R := by linarith
    have hprod : ‖u‖ * ‖w‖ < R ^ 2 := by
      calc
        ‖u‖ * ‖w‖ ≤ R * ‖w‖ := mul_le_mul_of_nonneg_right huR (norm_nonneg w)
        _ < R * R := mul_lt_mul_of_pos_left hwR hR
        _ = R ^ 2 := by ring
    simpa using hprod
  exact hanalytic.circleAverage_log_norm_of_ne_zero hfree

/-- The Blaschke harmonic majorant has the elementary center bound. -/
theorem norm_innerLogKernel_zero_center_le {u c : ℂ} {R : ℝ}
    (hR : 0 < R) (hu : u ∈ closedBall (0 : ℂ) R) :
    ‖PoissonJensen.innerLogKernel 0 u R c‖ ≤ R + ‖c‖ := by
  have huR : ‖u‖ ≤ R := by
    simpa [mem_closedBall_iff_norm] using hu
  rw [PoissonJensen.innerLogKernel, norm_div, Complex.norm_real,
    Real.norm_of_nonneg hR.le]
  have hnum : ‖((R : ℂ) ^ 2 - (starRingEnd ℂ) (u - 0) * (c - 0))‖
      ≤ R ^ 2 + R * ‖c‖ := by
    calc
      ‖((R : ℂ) ^ 2 - (starRingEnd ℂ) (u - 0) * (c - 0))‖
          ≤ ‖((R : ℂ) ^ 2)‖ + ‖(starRingEnd ℂ) (u - 0) * (c - 0)‖ :=
            norm_sub_le _ _
      _ = R ^ 2 + ‖u‖ * ‖c‖ := by
        rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le,
          norm_mul, RCLike.norm_conj]
        simp
      _ ≤ R ^ 2 + R * ‖c‖ := by
        gcongr
  rw [div_le_iff₀ hR]
  nlinarith

/-- The Blaschke harmonic majorant dominates the logarithmic distance in the outer disc. -/
theorem norm_sub_le_norm_innerLogKernel {u w : ℂ} {R : ℝ}
    (hR : 0 < R) (hu : u ∈ closedBall (0 : ℂ) R)
    (hw : w ∈ closedBall (0 : ℂ) R) :
    ‖w - u‖ ≤ ‖PoissonJensen.innerLogKernel 0 u R w‖ := by
  have huR : ‖u‖ ≤ R := by simpa [mem_closedBall_iff_norm] using hu
  have hwR : ‖w‖ ≤ R := by simpa [mem_closedBall_iff_norm] using hw
  have hcast : ((R : ℂ) ^ 2) = ((R ^ 2 : ℝ) : ℂ) := by norm_num
  have hid :
      Complex.normSq (((R : ℂ) ^ 2) - (starRingEnd ℂ) u * w) -
          R ^ 2 * Complex.normSq (w - u) =
        (R ^ 2 - Complex.normSq u) * (R ^ 2 - Complex.normSq w) := by
    rw [hcast]
    simp [Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_conj,
      Complex.normSq_ofReal, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, pow_two]
    ring
  have huSq : Complex.normSq u ≤ R ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg u]
  have hwSq : Complex.normSq w ≤ R ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]
  have hsq : R ^ 2 * Complex.normSq (w - u) ≤
      Complex.normSq (((R : ℂ) ^ 2) - (starRingEnd ℂ) u * w) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr huSq) (sub_nonneg.mpr hwSq)]
  have hRne : ‖(R : ℂ)‖ ≠ 0 := by simpa using hR.ne'
  rw [PoissonJensen.innerLogKernel, sub_zero, norm_div,
    Complex.norm_real, Real.norm_of_nonneg hR.le]
  simp only [sub_zero]
  have hsq' : ‖w - u‖ ^ 2 ≤
      (‖((R : ℂ) ^ 2 - (starRingEnd ℂ) u * w)‖ / R) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
    rw [div_pow]
    apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq
  exact (sq_le_sq₀ (norm_nonneg (w - u))
    (div_nonneg (norm_nonneg _) hR.le)).mp hsq'

/-- Away from the divisor point, the logarithmic Green kernel is nonnegative. -/
theorem log_norm_sub_le_log_norm_innerLogKernel {u w : ℂ} {R : ℝ}
    (hR : 0 < R) (hu : u ∈ closedBall (0 : ℂ) R)
    (hw : w ∈ closedBall (0 : ℂ) R) (hwu : w ≠ u) :
    Real.log ‖w - u‖ ≤
      Real.log ‖PoissonJensen.innerLogKernel 0 u R w‖ := by
  exact Real.log_le_log (norm_pos_iff.mpr (sub_ne_zero.mpr hwu))
    (norm_sub_le_norm_innerLogKernel hR hu hw)

/-- Shifted-circle mean of one outer-disc Green kernel is bounded by one logarithmic ratio. -/
theorem circleAverage_innerLogKernel_sub_log_norm_le {u c : ℂ} {R r : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hu : u ∈ closedBall (0 : ℂ) R)
    (hinner : ‖c‖ + r < R) :
    Real.circleAverage
        (fun w => Real.log ‖PoissonJensen.innerLogKernel 0 u R w‖ -
          Real.log ‖w - u‖) c r ≤
      Real.log ((R + ‖c‖) / r) := by
  have hinnerInt : CircleIntegrable
      (fun w => Real.log ‖PoissonJensen.innerLogKernel 0 u R w‖) c r := by
    apply MeromorphicOn.circleIntegrable_log_norm
    intro w _
    apply AnalyticAt.meromorphicAt
    unfold PoissonJensen.innerLogKernel
    apply AnalyticAt.div
    · exact analyticAt_const.sub
        (analyticAt_const.mul (analyticAt_id.sub analyticAt_const))
    · exact analyticAt_const
    · exact Complex.ofReal_ne_zero.mpr hR.ne'
  have hdistInt : CircleIntegrable (fun w => Real.log ‖w - u‖) c r :=
    ((analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn).circleIntegrable_log_norm
  change Real.circleAverage
      ((fun w => Real.log ‖PoissonJensen.innerLogKernel 0 u R w‖) -
        fun w => Real.log ‖w - u‖) c r ≤ _
  rw [Real.circleAverage_sub hinnerInt hdistInt,
    circleAverage_log_norm_innerLogKernel hR hr hu hinner]
  have hdist := log_radius_le_circleAverage_log_norm_sub c u hr
  have hkernel0 : 0 < ‖PoissonJensen.innerLogKernel 0 u R c‖ := by
    rw [norm_pos_iff]
    apply PoissonJensen.innerLogKernel_ne_zero hR
    have huR : ‖u‖ ≤ R := by
      simpa [mem_closedBall_iff_norm] using hu
    have hcR : ‖c‖ < R := by linarith [norm_nonneg c]
    have hprod : ‖u‖ * ‖c‖ < R ^ 2 := by
      calc
        ‖u‖ * ‖c‖ ≤ R * ‖c‖ := mul_le_mul_of_nonneg_right huR (norm_nonneg c)
        _ < R * R := mul_lt_mul_of_pos_left hcR hR
        _ = R ^ 2 := by ring
    simpa using hprod
  have hsum0 : 0 < R + ‖c‖ := by positivity
  have hlogKernel : Real.log ‖PoissonJensen.innerLogKernel 0 u R c‖ ≤
      Real.log (R + ‖c‖) :=
    Real.log_le_log hkernel0 (norm_innerLogKernel_zero_center_le hR hu)
  rw [Real.log_div hsum0.ne' hr.ne']
  linarith

end

end GaloisForLFunctions.HTGeometry
