import GaloisForLFunctions.HTGeometry.RegularizedMonomialCharge
import GaloisForLFunctions.Bottcher.AnnulusRoot
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Disk.GreenIdentity

/-!
# Regularized divisor mass and monomial winding

The proved planar Green identity evaluates the disk Laplacian mass of the smooth
regularized logarithm. At every positive radius that mass converges to `2πm` as
the regularizer vanishes through nonzero values. The limit agrees with the
imaginary part of the existing logarithmic-derivative winding integral of `z^m`.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace HTGeometry.RegularizedMonomialCharge
open DifferentialGeometry.Analysis

theorem radial_boundary_flux (m : ℕ) {ε R : ℝ} (hε : ε ≠ 0) (hR : 0 < R) (θ : ℝ) :
    R * fderiv ℝ (logFactor m ε) (Complex.polarCoord.symm (R, θ))
      (Complex.polarCoord.symm (1, θ)) = charge m ε R := by
  have hp : R • Complex.polarCoord.symm (1, θ) = Complex.polarCoord.symm (R, θ) := by
    exact (polar_point_eq_smul_unit R θ).symm
  have hn : ‖Complex.polarCoord.symm (R, θ)‖ = R := by simp [hR.le]
  rw [← smul_eq_mul, ← map_smul, hp, fderiv_logFactor_radial m hε, hn]
  rfl

def laplacianMass (m : ℕ) (ε R : ℝ) : ℝ :=
  ∫ z in Metric.closedBall (0 : ℂ) R, Laplacian.laplacian (logFactor m ε) z

theorem laplacianMass_eq (m : ℕ) {ε R : ℝ} (hε : ε ≠ 0) (hR : 0 < R) :
    laplacianMass m ε R = 2 * Real.pi * charge m ε R := by
  unfold laplacianMass
  rw [integral_laplacian_closedBall ((contDiff_logFactor m hε).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hR]
  simp_rw [radial_boundary_flux m hε hR]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem tendsto_laplacianMass (m : ℕ) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun ε : ℝ => laplacianMass m ε R) (𝓝[≠] 0) (𝓝 (2 * Real.pi * (m : ℝ))) := by
  apply ((tendsto_const_nhds.mul (tendsto_charge m hR)).mono_left inf_le_left).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (laplacianMass_eq m hε hR).symm

theorem tendsto_laplacianMass_winding (m : ℕ) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun ε : ℝ => laplacianMass m ε R) (𝓝[≠] 0)
      (𝓝 ((∫ θ in (0 : ℝ)..(2 * Real.pi),
        logDeriv (fun z : ℂ => z ^ (m : ℤ)) (circleMap 0 R θ) *
          (circleMap 0 R θ * Complex.I)).im)) := by
  rw [Bottcher.winding_zpow_circle hR]
  convert tendsto_laplacianMass m hR using 1 <;> simp <;> ring

end HTGeometry.RegularizedMonomialCharge
