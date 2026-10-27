import GaloisForLFunctions.ConjugateDiagonalGeometry.XiPositiveSourceMetric
import GaloisForLFunctions.ConjugateDiagonalGeometry.XiLogL1Convergence

/-!
# A source error bound for compact current readings

A single local L1 error of the logarithmic potential controls every compact
smooth test through its Laplacian bound. The estimate retains multiple zeros
and permits the test to change with the regulator.
-/

open Complex MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Laplacian Topology
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open _root_.RHTower

/-- Local logarithmic error controls every compact test whose Laplacian has the indicated support
and bound. No zero-separation parameter enters the estimate. -/
theorem abs_xiCurvatureReading_sub_current_le (φ : ℂ → ℝ)
    (hp : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (c : ℂ) (R B : ℝ)
    (hs : ∀ z, z ∉ closedBall c |R| → Δ φ z = 0)
    (hb : ∀ z ∈ closedBall c |R|, |Δ φ z| ≤ B) (k : ℕ) :
    |(∫ z, φ z * xiCurvatureDensity (sourceRegulator k) z) -
      (1 / 2 : ℝ) * ∫ z, Real.log ‖xi z‖ * Δ φ z| ≤
        (1 / 2 : ℝ) * B * xiLocalLogError c R k := by
  let V : ℂ → ℝ := fun z => xiLogPotential (sourceRegulator k) z - Real.log ‖xi z‖
  have hi : IntegrableOn V (closedBall c |R|) :=
    ((contDiff_xiLogPotential (sourceRegulator_pos k)).continuous.continuousOn.integrableOn_compact
      (isCompact_closedBall c |R|)).sub (integrableOn_xi_log_norm c R)
  have hΔ := continuous_test_laplacian hp
  have hip : IntegrableOn (fun z => V z * Δ φ z) (closedBall c |R|) :=
    hi.mul_continuousOn hΔ.continuousOn (isCompact_closedBall c |R|)
  have hu : IntegrableOn (fun z => xiLogPotential (sourceRegulator k) z * Δ φ z)
      (closedBall c |R|) :=
    (((contDiff_xiLogPotential (sourceRegulator_pos k)).continuous.mul hΔ).continuousOn).integrableOn_compact
      (isCompact_closedBall c |R|)
  have hl : IntegrableOn (fun z => Real.log ‖xi z‖ * Δ φ z) (closedBall c |R|) :=
    (integrableOn_xi_log_norm c R).mul_continuousOn hΔ.continuousOn
      (isCompact_closedBall c |R|)
  have heq (g : ℂ → ℝ) :
      (∫ z in closedBall c |R|, g z * Δ φ z) = ∫ z, g z * Δ φ z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [hs z hz, mul_zero]
  have herr : (∫ z, φ z * xiCurvatureDensity (sourceRegulator k) z) -
      (1 / 2 : ℝ) * (∫ z, Real.log ‖xi z‖ * Δ φ z) =
        (1 / 2 : ℝ) * ∫ z in closedBall c |R|, V z * Δ φ z := by
    have hgreen := twice_integral_xiCurvatureDensity φ hp hc k
    have hv : (∫ z in closedBall c |R|, V z * Δ φ z) =
        (∫ z, xiLogPotential (sourceRegulator k) z * Δ φ z) -
          ∫ z, Real.log ‖xi z‖ * Δ φ z := by
      dsimp only [V]
      simp_rw [sub_mul]
      rw [integral_sub hu hl, heq, heq]
    rw [hv]
    linarith only [hgreen]
  have hbound : |∫ z in closedBall c |R|, V z * Δ φ z| ≤ B * xiLocalLogError c R k := by
    calc
      |∫ z in closedBall c |R|, V z * Δ φ z| ≤
          ∫ z in closedBall c |R|, |V z * Δ φ z| := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (μ := volume.restrict (closedBall c |R|))
          (fun z => V z * Δ φ z)
      _ ≤ ∫ z in closedBall c |R|, B * |V z| := by
        apply integral_mono_ae (by simpa only [Real.norm_eq_abs] using hip.norm)
          (by simpa only [Real.norm_eq_abs] using hi.norm.const_mul B)
        filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
        rw [abs_mul]
        calc
          |V z| * |Δ φ z| ≤ |V z| * B := mul_le_mul_of_nonneg_left (hb z hz) (abs_nonneg _)
          _ = _ := mul_comm _ _
      _ = B * xiLocalLogError c R k := by
        rw [integral_const_mul]
        rfl
  rw [herr, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbound
    (by norm_num : (0 : ℝ) ≤ 1 / 2)

end GaloisForLFunctions.ConjugateDiagonalGeometry
