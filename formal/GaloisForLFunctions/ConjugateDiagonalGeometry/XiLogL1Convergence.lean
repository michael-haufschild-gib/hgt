import GaloisForLFunctions.ConjugateDiagonalGeometry.XiLogRegularization

/-!
# Local L1 error of the arithmetic logarithmic regulator

The regulated potential lies above the singular potential almost everywhere.
Its local L1 error is therefore an ordinary difference of integrals. This
provides a source-only error channel for families of moving smooth tests.
-/

open Complex MeasureTheory Filter Set Metric
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open _root_.RHTower

/-- The positive squared-amplitude regulator raises the logarithmic potential. -/
theorem log_norm_xi_le_xiLogPotential {η : ℝ} (hη : 0 < η) {z : ℂ} (hz : xi z ≠ 0) :
    Real.log ‖xi z‖ ≤ xiLogPotential η z := by
  have hnorm : 0 < ‖xi z‖ := norm_pos_iff.mpr hz
  have h := Real.log_le_log (sq_pos_of_pos hnorm)
    (le_add_of_nonneg_right hη.le : ‖xi z‖ ^ 2 ≤ ‖xi z‖ ^ 2 + η)
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  have hs : (xi z).re ^ 2 + (xi z).im ^ 2 = ‖xi z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  unfold xiLogPotential radialLogPotential
  rw [hs]
  linarith only [h]

/-- Error channel defined solely by the regularized and exact arithmetic potentials. -/
def xiLocalLogError (c : ℂ) (R : ℝ) (k : ℕ) : ℝ :=
  ∫ z in closedBall c |R|, |xiLogPotential (sourceRegulator k) z - Real.log ‖xi z‖|

theorem xiLocalLogError_nonneg (c : ℂ) (R : ℝ) (k : ℕ) :
    0 ≤ xiLocalLogError c R k :=
  integral_nonneg fun _ => abs_nonneg _

/-- Local L1 error equals the source integral difference, including discs containing zeros. -/
theorem xiLocalLogError_eq_sub (c : ℂ) (R : ℝ) (k : ℕ) :
    xiLocalLogError c R k =
      (∫ z in closedBall c |R|, xiLogPotential (sourceRegulator k) z) -
        ∫ z in closedBall c |R|, Real.log ‖xi z‖ := by
  unfold xiLocalLogError
  have hzero : ∀ᵐ z : ℂ ∂(volume.restrict (closedBall c |R|)), xi z ≠ 0 :=
    ae_restrict_of_ae xi_ne_zero_ae
  calc
    (∫ z in closedBall c |R|,
        |xiLogPotential (sourceRegulator k) z - Real.log ‖xi z‖|) =
        ∫ z in closedBall c |R|,
          xiLogPotential (sourceRegulator k) z - Real.log ‖xi z‖ := by
      apply integral_congr_ae
      filter_upwards [hzero] with z hz
      exact abs_of_nonneg (sub_nonneg.mpr
        (log_norm_xi_le_xiLogPotential (sourceRegulator_pos k) hz))
    _ = _ := integral_sub
      ((contDiff_xiLogPotential (sourceRegulator_pos k)).continuous.continuousOn.integrableOn_compact
        (isCompact_closedBall c |R|)) (integrableOn_xi_log_norm c R)

/-- The source error channel tends to zero without a zero-free-disc or simplicity condition. -/
theorem tendsto_xiLocalLogError (c : ℂ) (R : ℝ) :
    Tendsto (xiLocalLogError c R) atTop (𝓝 0) := by
  have h := tendsto_integral_xiLogPotential_on_disc (fun _ => (1 : ℝ)) continuous_const c R
  simp only [mul_one] at h
  have hsub := h.sub_const (∫ z in closedBall c |R|, Real.log ‖xi z‖)
  have he : xiLocalLogError c R = fun k =>
      (∫ z in closedBall c |R|, xiLogPotential (sourceRegulator k) z) -
        ∫ z in closedBall c |R|, Real.log ‖xi z‖ :=
    funext (xiLocalLogError_eq_sub c R)
  rw [he]
  simpa only [sub_self] using hsub

end GaloisForLFunctions.ConjugateDiagonalGeometry
