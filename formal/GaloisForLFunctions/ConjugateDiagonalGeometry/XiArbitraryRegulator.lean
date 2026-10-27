import GaloisForLFunctions.ConjugateDiagonalGeometry.XiPositiveSourceMetric
import GaloisForLFunctions.ConjugateDiagonalGeometry.XiLogL1Convergence

/-!
# Local xi current error at an arbitrary positive regulator

The Green identity bounds a compact source reading by the local logarithmic
potential error and the test's Laplacian. The regulator is an arbitrary
positive real, so the bound also applies to prescribed exponential schedules.
-/

open Complex MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Laplacian Topology
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open _root_.RHTower

/-- Local absolute error between the positive-regulator and exact xi potentials. -/
def xiLocalPotentialError (η : ℝ) (c : ℂ) (R : ℝ) : ℝ :=
  ∫ z in closedBall c |R|, |xiLogPotential η z - Real.log ‖xi z‖|

lemma xiLocalPotentialError_nonneg (η : ℝ) (c : ℂ) (R : ℝ) :
    0 ≤ xiLocalPotentialError η c R := integral_nonneg fun _ => abs_nonneg _

/-- Compact Green testing at every positive regulator. -/
theorem twice_integral_xiCurvatureDensity_of_pos (φ : ℂ → ℝ)
    (hp : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) {η : ℝ} (hη : 0 < η) :
    2 * (∫ z, φ z * xiCurvatureDensity η z) =
      ∫ z, xiLogPotential η z * Δ φ z := by
  calc
    2 * (∫ z, φ z * xiCurvatureDensity η z) =
        ∫ z, φ z * (2 * xiCurvatureDensity η z) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with z
      ring
    _ = ∫ z, φ z * Δ (xiLogPotential η) z := by
      simp_rw [laplacian_xiLogPotential hη]
    _ = ∫ z, Δ φ z * xiLogPotential η z :=
      source_green_identity _ φ (contDiff_xiLogPotential hη) hp hc
    _ = ∫ z, xiLogPotential η z * Δ φ z := by
      apply integral_congr_ae
      filter_upwards with z
      exact mul_comm _ _

/-- Local logarithmic error controls every compact test whose Laplacian has the indicated support
and bound. No zero-separation parameter enters the estimate. -/
theorem abs_xiCurvatureReading_sub_current_le_of_pos (φ : ℂ → ℝ)
    (hp : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (c : ℂ) (R B : ℝ)
    (hs : ∀ z, z ∉ closedBall c |R| → Δ φ z = 0)
    (hb : ∀ z ∈ closedBall c |R|, |Δ φ z| ≤ B) {η : ℝ} (hη : 0 < η) :
    |(∫ z, φ z * xiCurvatureDensity η z) -
      (1 / 2 : ℝ) * ∫ z, Real.log ‖xi z‖ * Δ φ z| ≤
        (1 / 2 : ℝ) * B * xiLocalPotentialError η c R := by
  let V : ℂ → ℝ := fun z => xiLogPotential η z - Real.log ‖xi z‖
  have hi : IntegrableOn V (closedBall c |R|) :=
    ((contDiff_xiLogPotential hη).continuous.continuousOn.integrableOn_compact
      (isCompact_closedBall c |R|)).sub (integrableOn_xi_log_norm c R)
  have hΔ := continuous_test_laplacian hp
  have hip : IntegrableOn (fun z => V z * Δ φ z) (closedBall c |R|) :=
    hi.mul_continuousOn hΔ.continuousOn (isCompact_closedBall c |R|)
  have hu : IntegrableOn (fun z => xiLogPotential η z * Δ φ z)
      (closedBall c |R|) :=
    (((contDiff_xiLogPotential hη).continuous.mul hΔ).continuousOn).integrableOn_compact
      (isCompact_closedBall c |R|)
  have hl : IntegrableOn (fun z => Real.log ‖xi z‖ * Δ φ z) (closedBall c |R|) :=
    (integrableOn_xi_log_norm c R).mul_continuousOn hΔ.continuousOn
      (isCompact_closedBall c |R|)
  have heq (g : ℂ → ℝ) :
      (∫ z in closedBall c |R|, g z * Δ φ z) = ∫ z, g z * Δ φ z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [hs z hz, mul_zero]
  have herr : (∫ z, φ z * xiCurvatureDensity η z) -
      (1 / 2 : ℝ) * (∫ z, Real.log ‖xi z‖ * Δ φ z) =
        (1 / 2 : ℝ) * ∫ z in closedBall c |R|, V z * Δ φ z := by
    have hgreen := twice_integral_xiCurvatureDensity_of_pos φ hp hc hη
    have hv : (∫ z in closedBall c |R|, V z * Δ φ z) =
        (∫ z, xiLogPotential η z * Δ φ z) -
          ∫ z, Real.log ‖xi z‖ * Δ φ z := by
      dsimp only [V]
      simp_rw [sub_mul]
      rw [integral_sub hu hl, heq, heq]
    rw [hv]
    linarith only [hgreen]
  have hbound : |∫ z in closedBall c |R|, V z * Δ φ z| ≤ B * xiLocalPotentialError η c R := by
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
      _ = B * xiLocalPotentialError η c R := by
        rw [integral_const_mul]
        rfl
  rw [herr, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbound
    (by norm_num : (0 : ℝ) ≤ 1 / 2)

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.abs_xiCurvatureReading_sub_current_le_of_pos
